#!/usr/bin/env bash
# agent-edit-guard.sh — defensive post-run guard for file-editing subagent passes.
#
# WHY: during two multi-agent edit passes, a target `.lean` was found renamed to
# `<stem>.prover-bak` (the repo's sorry-prover checkpoint convention, see
# `.claude/agents/sorry-prover.md`). No hook, cron, or daemon does this — all were
# ruled out. The strongest hypothesis is that a general-purpose subagent mimicked
# the convention and renamed the file itself, then narrated it as an "external
# watchdog". This is NOT a confirmed lesson (one occurrence, cause unproven) — it
# is only a guard until the cause is pinned down.
#
# THREE MITIGATIONS:
#  (1) PROMPT-SIDE — when launching a file-editing subagent, include the hard rule:
#      "edit in place with the Edit tool only; never cp/mv/rename the target file,
#       and never create any .bak/.prover-bak file."
#  (2) POST-RUN (this script) — after a subagent edit pass and BEFORE the
#      consolidated build, restore any `.lean` renamed to `*.prover-bak`/`*.bak`,
#      and flag any git-tracked `.lean` now missing from disk.
#  (3) VERIFY — a pass run under (1) should leave ZERO `*.prover-bak` files. If this
#      script ever has to RESTORE one, the hypothesis is confirmed; revisit then.
#
# Exit 0 = clean. Exit 1 = had to act / found a problem (investigate before build).

set -uo pipefail
ROOT="${1:-/Users/jkmiller/Documents/Claude/Projects/Vlasov}"
SRC="$ROOT/Vlasov/Vlasov"
acted=0

echo "== agent-edit-guard: scanning $SRC =="

# (a) restore any *.prover-bak / *.bak whose .lean is missing; flag strays
while IFS= read -r bak; do
  [ -z "$bak" ] && continue
  base="${bak%.prover-bak}"; base="${base%.bak}"
  case "$base" in *.lean) lean="$base";; *) lean="$base.lean";; esac
  if [ ! -e "$lean" ]; then
    echo "  RESTORE: $(basename "$lean")  <-  $(basename "$bak")"
    mv "$bak" "$lean"; acted=1
  else
    echo "  STRAY (target present; left for manual review): $bak"; acted=1
  fi
done < <(find "$SRC" \( -name '*.prover-bak' -o -name '*.bak' \) 2>/dev/null)

# (b) any git-tracked .lean now missing from disk?
while IFS= read -r f; do
  [ -e "$ROOT/$f" ] || { echo "  MISSING tracked file: $f"; acted=1; }
done < <(git -C "$ROOT" ls-files '*.lean')

if [ "$acted" -eq 0 ]; then
  echo "== agent-edit-guard: CLEAN (no .bak files, no missing tracked .lean) =="
  exit 0
else
  echo "== agent-edit-guard: ACTED — investigate before trusting any build =="
  exit 1
fi
