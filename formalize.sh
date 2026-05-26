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

mkdir -p "${ROOT}/formalize" "${LOGS}" "${ROOT}/formalize/plans"

# ---- argument parsing -------------------------------------------------------

STAGES="all"
CLEAN=0
PROVE_CYCLES=0
PROVE_MODE="top-recommendation"
DECOMPOSE_TARGET=""
DECOMPOSE_MODE="explicit"
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
    --decompose)
      # `--decompose <name-or-tex-label>` → explicit mode, that specific target
      # `--decompose` (no arg)            → largest-blocked mode, agent picks
      # The `[[ ! "$2" =~ ^- ]]` pattern distinguishes a target name from another
      # flag — safer than positive-integer matching for free-form names.
      if [ $# -ge 2 ] && [[ ! "$2" =~ ^- ]]; then
        DECOMPOSE_TARGET="$2"; DECOMPOSE_MODE="explicit"; shift 2
      else
        DECOMPOSE_TARGET=""; DECOMPOSE_MODE="largest-blocked"; shift
      fi
      STAGES="decompose"
      ;;
    --decompose=*)
      DECOMPOSE_TARGET="${1#*=}"; DECOMPOSE_MODE="explicit"
      STAGES="decompose"; shift
      ;;
    --decompose-gap)
      # `--decompose-gap <name-or-tex-label>` — like --decompose, but the
      # target is expected to need Mathlib API that doesn't exist.  Agent
      # produces sorry'd helpers AND named axiom MathlibTODO_* declarations.
      if [ $# -ge 2 ] && [[ ! "$2" =~ ^- ]]; then
        DECOMPOSE_TARGET="$2"; DECOMPOSE_MODE="gap"; shift 2
      else
        echo "ERROR: --decompose-gap requires a target name (e.g. Vlasov.vlasovWellPosedness)" >&2
        exit 1
      fi
      STAGES="decompose"
      ;;
    --decompose-gap=*)
      DECOMPOSE_TARGET="${1#*=}"; DECOMPOSE_MODE="gap"
      STAGES="decompose"; shift
      ;;
    --sketch)
      # `--sketch <helper-name>` — author/refresh proof_sketch for ONE helper.
      # The helper name is mandatory; we resolve it to the plan JSON via grep.
      if [ $# -ge 2 ] && [[ ! "$2" =~ ^- ]]; then
        SKETCH_TARGET="$2"; shift 2
      else
        echo "ERROR: --sketch requires a helper name (e.g. Vlasov.diagonalCorrection_bound)" >&2
        exit 1
      fi
      STAGES="sketch"
      ;;
    --sketch=*)
      SKETCH_TARGET="${1#*=}"
      STAGES="sketch"; shift
      ;;
    -h|--help)
      cat <<EOF
Usage: ./formalize.sh [--stage all|0|1|2|3|4] [--clean]
       ./formalize.sh --prove-next [N]
       ./formalize.sh --prove-easiest [N]
       ./formalize.sh --decompose [target]
       ./formalize.sh --sketch <helper-name>

  --stage N            Run only stage N (default: all). Comma-separate for
                       multiple.
  --clean              Remove ./Vlasov, ./formalize/structure.md,
                       ./formalize/report.md before running.
  --prove-next [N]     Run an automated proving cycle: verifier (refresh
                       report) -> sorry-prover (target the report's TOP
                       recommendation) -> verifier (refresh report).
                       Repeat N times (default 1).
  --prove-easiest [N]  Same cycle as --prove-next, but the sorry-prover
                       scans ALL open sorries and picks the one most likely
                       to fit in its 8-iteration budget (shortest statement,
                       no dep on other sorries, concrete conclusion).
                       Use this when the top recommendation is too large
                       and you'd rather take any sorry off the board.
  --decompose [target] Decompose ONE oversized sorry'd theorem into 3-8
                       helper sorries (sorry count INCREASES, on purpose).
                       [target] is a Lean declaration name or tex-label;
                       with no argument the largest blocked sorry from the
                       report is picked. Auto-runs verifier afterward to
                       refresh report.md. Use BEFORE --prove-next when the
                       top recommendation is too big to attempt directly.
  --decompose-gap <t>  Like --decompose, but expects the target to need
                       Mathlib API that doesn't yet exist. Decomposer
                       produces both sorry'd constructive helpers AND
                       named 'axiom MathlibTODO_*' declarations for the
                       gaps. Use for theorems flagged as 'needs Mathlib
                       API not yet available' in the verifier report
                       (e.g., vlasovWellPosedness, dobrushin).
  --sketch <helper>    Draft (or refresh) the 'proof_sketch' field of ONE
                       helper in formalize/plans/*.json. Reads the helper's
                       Lean signature, grep-validates mathlib_hints, applies
                       any matching patterns from sorry-decomposer.md
                       section 3.1.6, writes a multi-line tactic block back
                       into the plan JSON. Does NOT edit the Lean file.
                       <helper> is the fully-qualified helper name (e.g.
                       Vlasov.diagonalCorrection_bound) and must already
                       appear in some plan's helpers[].
  -h, --help           Show this message.

Prerequisites:
  - elan / lake / lean (Lean 4.x toolchain)
  - claude (Claude Code CLI), authenticated
  - perl (for the timeout watchdog)
  - .claude/agents/{latex-parser,lean-translator,lean-fixer,lean-verifier,sorry-prover,sorry-decomposer}.md
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
  #
  # The pipeline has three stages giving us per-event visibility:
  #
  #   claude --output-format stream-json --verbose -p ...
  #     ↓ (one JSONL event per line, flushed immediately)
  #   tee LOG.jsonl                       # raw archive for replay
  #     ↓
  #   jq -rR --unbuffered '<filter>'      # render to human-readable
  #     ↓
  #   tee LOG                             # human-readable archive
  #
  # The streaming output mode is essential: `claude -p` in default mode
  # buffers the entire session and only flushes when the assistant produces
  # a final message, so SIGALRM-killed runs left zero-byte logs.  With
  # stream-json, each Read/Edit/Bash tool call and each text chunk lands
  # in the log as it happens.  `--verbose` is required when combining
  # `--output-format stream-json` with `-p` (otherwise claude errors).
  #
  # The jq filter uses `-R` (read each line as a raw string) + `try fromjson
  # catch null` so non-JSON lines (perl errors, the kernel's `Alarm clock`
  # SIGALRM notice) pass through unchanged.  `--unbuffered` makes jq flush
  # per line, preserving the streaming property.  Tool inputs/results are
  # truncated at 300 chars in the rendered log; the LOG.jsonl sibling
  # has full fidelity.
  #
  # `${effort_args[@]+"${effort_args[@]}"}` is the "empty array safe under
  # set -u" expansion idiom — without it, an empty array trips `unbound
  # variable` on macOS bash 3.2 even though `local -a effort_args=()`
  # explicitly initialised it.
  local rc=0
  { perl -e 'alarm shift @ARGV; exec @ARGV or die "exec: $!"' \
         "${seconds}" "${CLAUDE_BASE[@]}" \
         --output-format stream-json --verbose \
         ${effort_args[@]+"${effort_args[@]}"} \
         -p "Use the Agent tool with subagent_type=\"${agent}\" to perform the following task, then exit.

${prompt}" 2>&1 \
      | tee "${LOGS}/${log}.jsonl" \
      | jq -rR --unbuffered '
          if (try fromjson catch null) | type == "object" then
            fromjson
            | if .type == "system" then "[system] " + (.subtype // "init")
              elif .type == "rate_limit_event" then
                "[rate-limit] " + (.rate_limit_info | tostring)
              elif .type == "result" then
                "[result] " + (.subtype // "")
                + " duration=" + ((.duration_ms // 0)|tostring) + "ms"
                + " cost=$" + ((.total_cost_usd // 0)|tostring)
              elif .type == "assistant" then
                ((.message.content // []) | map(
                  if .type == "text" then .text
                  elif .type == "thinking" then "[thinking] " + (.thinking | .[0:200])
                  elif .type == "tool_use" then "[" + (.name // "?") + "] " + (.input | tostring | .[0:300])
                  else "[" + (.type // "?") + "]" end
                ) | join("\n"))
              elif .type == "user" then
                ((.message.content // []) | map(
                  if .type == "tool_result" then "→ " + (.content | tostring | .[0:300])
                  else "[" + (.type // "?") + "]" end
                ) | join("\n"))
              else "[" + (.type // "?") + "]" end
          else
            .
          end' \
      | tee "${LOGS}/${log}" ; } || rc=$?
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

# ---- decompose cycle: sorry-decomposer -> verifier (refresh report) --------

if [ "${STAGES}" = "decompose" ]; then
  echo
  echo "=== decompose (target: ${DECOMPOSE_TARGET:-<largest-blocked>}, mode: ${DECOMPOSE_MODE}) ==="

  local_log="${LOGS}/decomposer-$(date +%Y%m%d-%H%M%S).md"

  # The decomposer is invoked with default effort (NOT --effort low).  Unlike
  # the prover (where `low` forces tool-call cadence over deliberation), the
  # decomposer's task is the opposite: quality of the helper graph is a
  # thinking task, and builds here are cheap (mostly elaborating sorry'd
  # statements rather than searching for tactics).
  delegate sorry-decomposer "decompose-decomposer.log" \
"Decompose ONE oversized sorry'd theorem into 3-8 helper lemmas.

  project root:    ${PROJECT}
  lean file:       ${LEAN_FILE}
  verifier report: ${REPORT}
  attempt log:     ${local_log}
  selection mode:  ${DECOMPOSE_MODE}
  target:          ${DECOMPOSE_TARGET}

Follow your system prompt exactly. In explicit mode, 'target' is a Lean
declaration name OR a tex-label; resolve it against the report's Sorry
inventory table. In largest-blocked mode, 'target' is empty — pick per
§0 Mode B (score by statement size + deferral signals + dependency
depth). Hard cap of 6 build iterations. Checkpoint the file before
editing and revert on failure." \
    900

  # Safety net (mirrors the prover's checkpoint restore): if the decomposer
  # is killed before its own §7 cleanup, the .decomposer-bak file is left
  # behind.  Decide whether the post-SIGALRM state is "agent's work
  # successfully landed" (preserve) or "agent broke the file" (restore).
  #
  # Background: the May 25 dobrushin gap-mode run hit SIGALRM at 900s right
  # AFTER the agent finished all Lean edits (axioms + 5 helpers + parent
  # rewrite, build green) and started its final plan-JSON write.  The
  # earlier always-restore heuristic wiped that good work.  The new
  # heuristic preserves it.
  if [ -f "${LEAN_FILE}.decomposer-bak" ]; then
    echo "--- decomposer-bak checkpoint present; deciding preserve vs restore ---"
    if cmp -s "${LEAN_FILE}" "${LEAN_FILE}.decomposer-bak"; then
      # No diff between current and checkpoint.  Agent did no useful Lean
      # work (or undid it all itself).  Just clean up the bak.
      echo "    current Lean file == checkpoint; nothing to preserve, cleaning bak."
      rm "${LEAN_FILE}.decomposer-bak"
    elif (cd "${PROJECT}" && lake build 2>&1 | grep -qE "^error:"); then
      # File differs AND has build errors.  Agent's edits broke compilation;
      # restore from checkpoint so the post-verifier sees a green baseline.
      echo "    current Lean file has build errors; RESTORING from .decomposer-bak."
      mv "${LEAN_FILE}.decomposer-bak" "${LEAN_FILE}"
    else
      # File differs AND builds clean.  Agent's work landed before SIGALRM.
      # Preserve it; clean up the bak.
      echo "    current Lean file builds green with edits; PRESERVING agent's work, cleaning bak."
      rm "${LEAN_FILE}.decomposer-bak"
    fi
  fi

  # Refresh report so subsequent --prove-next/--prove-easiest sees the new
  # helper sorries.  No chained prover invocation — the user reviews the
  # decomposition graph before letting the prover swing at the new helpers.
  echo "--- refreshing report after decomposition (verifier) ---"
  delegate lean-verifier "decompose-post-verify.log" \
"Verify the Lean formalization and write a coverage report.

  project root: ${PROJECT}
  lean file:    ${LEAN_FILE}
  outline:      ${OUTLINE}
  report:       ${REPORT}

Follow your system prompt exactly. Read-only on source files."
fi

# ---- sketch cycle: sketch-author writes one helper's proof_sketch -----------

if [ "${STAGES}" = "sketch" ]; then
  echo
  echo "=== sketch (target: ${SKETCH_TARGET}) ==="

  # Resolve the helper to its plan file via a quick grep across plans/.
  # `|| true` neutralises set -e + pipefail when grep finds no match (which
  # is the very case we want the explicit -z check below to handle).
  PLAN_FILE=$(grep -l "\"name\": \"${SKETCH_TARGET}\"" "${ROOT}/formalize/plans/"*.json 2>/dev/null | head -1 || true)
  if [ -z "${PLAN_FILE}" ]; then
    echo "ERROR: helper '${SKETCH_TARGET}' not found in any plan under ${ROOT}/formalize/plans/" >&2
    echo "       (search pattern: \"name\": \"${SKETCH_TARGET}\")" >&2
    exit 1
  fi

  local_log="${LOGS}/sketch-author-$(date +%Y%m%d-%H%M%S).md"

  # Timeout 600s + effort=low: sketch authoring is bounded (one helper, no
  # Lean iteration), but a 300s budget proved tight in the first run when
  # the agent went into exploratory Mathlib grep mode. `effort=low`
  # discourages long extended-thinking phases (same rationale as the prover
  # — forces tool-call cadence over deliberation). No safety net needed:
  # the agent only edits the plan JSON (validated via jq in its §5).
  delegate sketch-author "sketch-author.log" \
"Draft (or refresh) the proof_sketch for one helper.

  project root:    ${PROJECT}
  lean file:       ${LEAN_FILE}
  plan JSON:       ${PLAN_FILE}
  helper name:     ${SKETCH_TARGET}
  attempt log:     ${local_log}

Follow your system prompt exactly.  Single-responsibility: read the
helper's signature in the Lean file, grep-validate the existing
mathlib_hints (do NOT search Mathlib for additional names), consult
the patterns catalogue in sorry-decomposer.md §3.1.6, draft a
proof_sketch from those validated hints + boilerplate, write it
back to the plan JSON.  Do NOT edit the Lean file.  If the
validated hints are insufficient to author a confident sketch,
exit cleanly with result=skipped (a bad sketch is worse than no
sketch)." \
    600 low

  echo
  echo "Sketch authoring finished."
  echo "  Plan file:  ${PLAN_FILE}"
  echo "  Agent log:  ${LOGS}/sketch-author.log"
  echo "  Attempt:    ${local_log}"
fi

echo
echo "Pipeline finished."
echo "  Outline:    ${OUTLINE}"
echo "  Lean file:  ${LEAN_FILE}"
echo "  Report:     ${REPORT}"
echo "  Logs:       ${LOGS}/"
