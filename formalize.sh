#!/usr/bin/env bash
# LaTeX -> Lean 4/Mathlib formalization pipeline.
#
# Stages:
#   0. Scaffold a fresh Lean 4 + Mathlib project under ./Vlasov (once).
#   1. latex-parser    vlasov.tex            -> formalize/structure.md
#   2. lean-translator structure.md          -> Vlasov/Vlasov/Basic.lean
#   3. lean-fixer      iterates `lake build` until clean (sorries OK)
#   4. lean-verifier   produces formalize/report.md
#
# Each stage runs as a Claude Code subagent (.claude/agents/*.md) invoked
# non-interactively via `claude -p`. Stages communicate via files only.

set -euo pipefail

# Allow this script to be invoked from inside an existing Claude Code session.
# Unsetting these prevents the nested-session guard from firing when we spawn
# `claude -p` for each subagent stage.
unset CLAUDECODE CLAUDE_CODE_SSE_PORT CLAUDE_CODE_ENTRYPOINT 2>/dev/null || true

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEX="${ROOT}/vlasov.tex"
PROJECT="${ROOT}/Vlasov"
LEAN_FILE_REL="Vlasov/Basic.lean"
LEAN_FILE="${PROJECT}/${LEAN_FILE_REL}"
OUTLINE="${ROOT}/formalize/structure.md"
REPORT="${ROOT}/formalize/report.md"
LOGS="${ROOT}/formalize/logs"

mkdir -p "${ROOT}/formalize" "${LOGS}"

# ---- argument parsing -------------------------------------------------------

STAGES="all"
CLEAN=0
PROVE_CYCLES=0
PROVE_MODE="top-recommendation"
while [ $# -gt 0 ]; do
  case "$1" in
    --stage)         STAGES="$2"; shift 2 ;;
    --stage=*)       STAGES="${1#*=}"; shift ;;
    --clean)         CLEAN=1; shift ;;
    --prove-next|--prove-easiest)
      # `--prove-next`     → sorry-prover targets the verifier's top recommendation
      # `--prove-easiest`  → sorry-prover scans all sorries and picks the most tractable
      if [ "$1" = "--prove-easiest" ]; then
        PROVE_MODE="most-tractable"
      fi
      # Optional positive integer argument for cycle count.
      if [ $# -ge 2 ] && [[ "$2" =~ ^[1-9][0-9]*$ ]]; then
        PROVE_CYCLES="$2"; shift 2
      else
        PROVE_CYCLES=1; shift
      fi
      STAGES="prove"
      ;;
    -h|--help)
      cat <<EOF
Usage: ./formalize.sh [--stage all|0|1|2|3|4] [--clean]
       ./formalize.sh --prove-next [N]
       ./formalize.sh --prove-easiest [N]

  --stage N           Run only stage N (default: all). Comma-separate for
                      multiple.
  --clean             Remove ./Vlasov, ./formalize/structure.md,
                      ./formalize/report.md before running.
  --prove-next [N]    Run an automated proving cycle: verifier (refresh
                      report) -> sorry-prover (target the report's TOP
                      recommendation) -> verifier (refresh report).
                      Repeat N times (default 1).
  --prove-easiest [N] Same cycle as --prove-next, but the sorry-prover
                      scans ALL open sorries and picks the one most likely
                      to fit in its 8-iteration budget (shortest statement,
                      no dep on other sorries, concrete conclusion).
                      Use this when the top recommendation is too large
                      and you'd rather take any sorry off the board.
  -h, --help          Show this message.

Prerequisites:
  - elan / lake / lean (Lean 4.x toolchain)
  - claude (Claude Code CLI), authenticated
  - perl (for the timeout watchdog)
  - .claude/agents/{latex-parser,lean-translator,lean-fixer,lean-verifier,sorry-prover}.md
EOF
      exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

run_stage() {
  local stage="$1"
  [ "${STAGES}" = "all" ] && return 0
  case ",${STAGES}," in *,${stage},*) return 0 ;; *) return 1 ;; esac
}

# ---- 0. clean (optional) and scaffold ---------------------------------------

if [ "${CLEAN}" -eq 1 ]; then
  echo "=== clean ==="
  rm -rf "${PROJECT}" "${OUTLINE}" "${REPORT}"
fi

if run_stage 0; then
  echo "=== stage 0: scaffold Lean project ==="
  if [ ! -d "${PROJECT}" ]; then
    (cd "${ROOT}" && lake new Vlasov math)
    echo "fetching precompiled Mathlib oleans (this can take a few minutes the first time)..."
    (cd "${PROJECT}" && lake exe cache get) | tail -20
    echo "scaffold complete at ${PROJECT}"
  else
    echo "${PROJECT} exists; skipping scaffold"
  fi
fi

# ---- Claude invocation helper ----------------------------------------------

# bypassPermissions: the four subagents have narrow tool grants in their
# frontmatter (Read/Edit/Write + `lake build` for fixer/verifier), so the
# blast radius is bounded by those grants. The driver runs locally.
CLAUDE_BASE=(claude --permission-mode bypassPermissions)

# Each call asks main Claude to delegate to a specific subagent. The subagent
# discovery comes from .claude/agents/<name>.md.
#
# A wall-clock timeout is applied to every claude -p invocation so that a
# stuck subagent (e.g. one stuck in extended thinking without ever calling
# `lake build`) cannot wedge the pipeline. The fourth argument overrides
# the default 600s budget; long-running stages (fixer, prover) pass 900s.
# Timeout exit is non-fatal: the pipeline logs it and continues so the
# post-stage verifier still runs and produces a current report.
#
# macOS does not ship GNU `timeout`. The perl idiom
#   perl -e 'alarm shift; exec @ARGV' SECONDS CMD ARGS...
# installs a SIGALRM timer in the perl process, then exec's the target
# command. The alarm timer survives the exec (same PID), so the target
# command is killed by SIGALRM (default handler: exit 142) if it runs
# past SECONDS.  Standard Unix portability trick.
delegate() {
  local agent="$1" log="$2" prompt="$3" seconds="${4:-600}" effort="${5:-}"
  # Optional --effort <level> override.  For the prover specifically, we
  # pass `low` to discourage long extended-thinking phases — the §4
  # discipline relies on the agent CALLING `lake build` early and often,
  # which it won't do if it spends all 15 minutes deliberating in its head.
  local -a effort_args=()
  if [ -n "${effort}" ]; then
    effort_args=(--effort "${effort}")
  fi
  echo
  echo "--- invoking subagent: ${agent} (timeout ${seconds}s${effort:+, effort ${effort}}) ---"
  # The driver runs with `set -euo pipefail`, so a non-zero exit from the
  # pipe (e.g. SIGALRM=142 when the watchdog fires) would abort the function
  # before we could classify the exit and decide whether to continue.
  # The `{ ... } || rc=$?` pattern captures the pipeline's exit code into
  # `rc` without aborting: the brace group inherits pipefail so `$?` is the
  # rightmost non-zero exit code, and the `|| rc=$?` short-circuit catches
  # it.  Plain `|| true` would zero out PIPESTATUS and lose the signal info.
  local rc=0
  # `${effort_args[@]+"${effort_args[@]}"}` is the "empty array safe under
  # set -u" expansion idiom — without it, an empty array trips `unbound
  # variable` on macOS bash 3.2 even though `local -a effort_args=()`
  # explicitly initialised it.
  { perl -e 'alarm shift @ARGV; exec @ARGV or die "exec: $!"' \
         "${seconds}" "${CLAUDE_BASE[@]}" \
         ${effort_args[@]+"${effort_args[@]}"} \
         -p "Use the Agent tool with subagent_type=\"${agent}\" to perform the following task, then exit.

${prompt}" 2>&1 | tee "${LOGS}/${log}" ; } || rc=$?
  if [ "${rc}" -eq 142 ]; then
    echo "agent '${agent}' exceeded ${seconds}s wall-clock budget (SIGALRM) — pipeline continuing"
  elif [ "${rc}" -ne 0 ]; then
    echo "agent '${agent}' exited non-zero (rc=${rc}) — pipeline continuing"
  fi
}

# ---- 1. parse ---------------------------------------------------------------

if run_stage 1; then
  echo "=== stage 1: latex-parser ==="
  delegate latex-parser 01-parser.log \
"Parse the LaTeX paper at:
  ${TEX}

Write the structured outline to:
  ${OUTLINE}

Follow your system prompt exactly."
fi

# ---- 2. translate -----------------------------------------------------------

if run_stage 2; then
  echo "=== stage 2: lean-translator ==="
  delegate lean-translator 02-translator.log \
"Translate the structured outline into a Lean 4 / Mathlib statement skeleton.

  outline (input): ${OUTLINE}
  tex     (input): ${TEX}
  lean    (output): ${LEAN_FILE}

Every proof is \`sorry\`. Follow your system prompt exactly."
fi

# ---- 3. fix -----------------------------------------------------------------

if run_stage 3; then
  echo "=== stage 3: lean-fixer ==="
  delegate lean-fixer 03-fixer.log \
"Fix Lean compilation errors until the build is clean (only \`sorry\` warnings).

  project root: ${PROJECT}
  target file:  ${LEAN_FILE_REL}  (relative to project root)

Follow your system prompt exactly. Hard cap of 12 build iterations." \
    900
fi

# ---- 4. verify --------------------------------------------------------------

if run_stage 4; then
  echo "=== stage 4: lean-verifier ==="
  delegate lean-verifier 04-verifier.log \
"Verify the Lean formalization and write a coverage report.

  project root: ${PROJECT}
  lean file:    ${LEAN_FILE}
  outline:      ${OUTLINE}
  report:       ${REPORT}

Follow your system prompt exactly. Read-only on source files."
fi

# ---- prove-next cycle: verifier -> sorry-prover -> verifier ----------------

if [ "${PROVE_CYCLES}" -gt 0 ]; then
  for ((cycle=1; cycle<=PROVE_CYCLES; cycle++)); do
    echo
    echo "=== prove-next cycle ${cycle}/${PROVE_CYCLES} ==="

    # 1. Refresh the report so the prover sees current state.
    echo "--- refreshing report (verifier) ---"
    delegate lean-verifier "prove-${cycle}-pre-verify.log" \
"Verify the Lean formalization and write a coverage report.

  project root: ${PROJECT}
  lean file:    ${LEAN_FILE}
  outline:      ${OUTLINE}
  report:       ${REPORT}

Follow your system prompt exactly. Read-only on source files."

    # 2. Attempt one sorry, selected per PROVE_MODE.
    local_log="${LOGS}/prover-cycle-${cycle}.md"
    echo "--- sorry-prover (cycle ${cycle}, mode: ${PROVE_MODE}) ---"
    delegate sorry-prover "prove-${cycle}-prover.log" \
"Attempt to discharge ONE sorry.

  project root:    ${PROJECT}
  lean file:       ${LEAN_FILE}
  verifier report: ${REPORT}
  attempt log:     ${local_log}
  selection mode:  ${PROVE_MODE}

Follow your system prompt exactly. The selection mode tells you which sorry
to target (see §0 of your system prompt). Hard cap of 8 build iterations.
Checkpoint the file before editing and revert on failure." \
      900 low

    # 2b. Safety net: if the prover was killed mid-edit (e.g. SIGALRM from the
    # watchdog), the agent never reached its own revert step.  The checkpoint
    # file `<LEAN_FILE>.prover-bak` was created at the start of the prover
    # run; the agent removes it on either success or controlled failure.  If
    # it still exists here, the agent was killed — restore from it so the
    # post-verifier sees the green baseline rather than a broken half-edit.
    if [ -f "${LEAN_FILE}.prover-bak" ]; then
      echo "--- prover-bak checkpoint still present; restoring (prover was killed before its own revert step) ---"
      mv "${LEAN_FILE}.prover-bak" "${LEAN_FILE}"
    fi

    # 3. Refresh the report so the next cycle (or the user) sees the new state.
    echo "--- refreshing report after attempt (verifier) ---"
    delegate lean-verifier "prove-${cycle}-post-verify.log" \
"Verify the Lean formalization and write a coverage report.

  project root: ${PROJECT}
  lean file:    ${LEAN_FILE}
  outline:      ${OUTLINE}
  report:       ${REPORT}

Follow your system prompt exactly. Read-only on source files."
  done
fi

echo
echo "Pipeline finished."
echo "  Outline:    ${OUTLINE}"
echo "  Lean file:  ${LEAN_FILE}"
echo "  Report:     ${REPORT}"
echo "  Logs:       ${LOGS}/"
