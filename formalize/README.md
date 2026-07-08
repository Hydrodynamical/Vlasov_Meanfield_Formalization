# LaTeX → Lean formalization pipeline

A five-agent Claude Code pipeline that turns a LaTeX math paper into a Lean 4 /
Mathlib statement skeleton with `sorry` proofs — and then incrementally
discharges those sorries one at a time. Designed for [vlasov.tex](vlasov.tex);
generalizes to other analysis/PDE papers with minor edits to the agents.

## Pipeline

Two flows share the same five agents:

**Scaffold flow** — runs once per paper to produce a green-building skeleton:

```
vlasov.tex
   │
   ▼
[1] latex-parser  ─────► formalize/structure.md
   │                       (Markdown outline: one section per
   │                        definition / assumption / theorem)
   ▼
[2] lean-translator ───► Vlasov/Vlasov/Basic.lean
   │                       (import Mathlib, definitions,
   │                        theorem signatures, every proof = `sorry`)
   ▼
[3] lean-fixer    ─────► edits Basic.lean in place
   │                       (loops `lake build`, fixes errors,
   │                        up to 12 iterations, never proves)
   ▼
[4] lean-verifier ─────► formalize/report.md
                           (build status, coverage table,
                            sorry inventory, ranked next steps)
```

**Proving flow** — incremental, runs once per `sorry` you want to discharge:

```
                        formalize/report.md (current state)
                          │
                          ▼
   ┌─► [4] lean-verifier ─► refresh report.md
   │      │
   │      ▼
   │   [5] sorry-prover ─► edits Basic.lean: attempts top recommendation
   │      │                  · checkpoints file before any edit
   │      │                  · max 8 iterations, one tactic edit per build
   │      │                  · reverts on failure
   │      ▼
   │   [4] lean-verifier ─► refresh report.md
   │      │
   └──────┘  (repeat N times via `--prove-next N`)
```

Stage 0 (one-shot, in the driver) scaffolds the Lean project: `lake new Vlasov math`
then `lake exe cache get` to pull precompiled Mathlib oleans.

## Files

```
.claude/agents/
  latex-parser.md       Read-only on .tex; writes structure.md
  lean-translator.md    Read outline + tex; writes one .lean file
  lean-fixer.md         Read/Edit + `lake build`; no proof attempts
  lean-verifier.md      Read + `lake build`; writes report.md
  sorry-prover.md       Read/Edit + `lake build`; attempts ONE sorry per run
formalize.sh            Driver — invokes each subagent via `claude -p`,
                        wrapped in a perl alarm-exec watchdog (timeout)
formalize/
  README.md             this file
  structure.md          generated, stage 1 output
  report.md             generated, refreshed by every verifier run
  logs/                 per-stage stdout
                          01-parser.log, 02-translator.log,
                          03-fixer.log, 04-verifier.log
                          prove-N-pre-verify.log,
                          prove-N-prover.log, prove-N-post-verify.log
                          prover-cycle-N.md  (sorry-prover attempt log)
Vlasov/                 generated, the Lean 4 + Mathlib project
  lakefile.toml
  lean-toolchain
  Vlasov.lean
  Vlasov/Basic.lean     ← the formalization itself
```

## Usage

Scaffold a fresh formalization:

```sh
./formalize.sh                    # full scaffold: stages 0,1,2,3,4
./formalize.sh --stage 1          # just re-parse
./formalize.sh --stage 2,3,4      # re-translate, re-fix, re-verify
./formalize.sh --clean            # nuke Vlasov/, structure.md, report.md first
```

Incrementally discharge sorries (run after the scaffold flow):

```sh
./formalize.sh --prove-next       # one cycle, target = report's top recommendation
./formalize.sh --prove-next 3     # three cycles in a row
./formalize.sh --prove-easiest    # one cycle, target = most-tractable sorry across the file
./formalize.sh --prove-easiest 3  # three cycles using easiest-first selection
```

Each cycle ends with `report.md` refreshed, so you can read the current
state between cycles.

**`--prove-next`** targets the top item under "Recommended next steps" in
the report, skipping items it identifies as blocked. Best when the report's
priority order reflects what you actually want to prove (typically: when
the highest-impact theorem is also tractable).

**`--prove-easiest`** instructs the prover to scan ALL open sorries and
pick the one most likely to fit in its 8-iteration budget — shortest
statement, no dependency on other sorries, concrete conclusion. Best when
the top recommendation is a large theorem the prover keeps timing out on,
and you'd rather take any sorry off the board to build momentum.

```sh
./formalize.sh --help
```

Prerequisites:

- Lean toolchain: `elan` (gets `lake` + `lean`). Verified at `lean 4.29.1`.
- `claude` CLI on PATH, authenticated.
- `perl` (system perl is fine — used for the timeout watchdog since macOS
  ships no `timeout` binary).

## Cost and time

- **Stage 0 (scaffold)**: a few minutes the first time — most of it is
  `lake exe cache get` downloading ~1–2 GB of precompiled Mathlib oleans.
  Skipped on subsequent runs.
- **Stages 1–4 (scaffold agents)**: each is one or a few `claude -p` calls.
  Stage 3 may take longer because it loops `lake build` (each rebuild of a
  file importing `Mathlib` is ~30–80 s once cached).
- **`--prove-next` cycle**: pre-verifier (~3 min) + prover (≤ 15 min, capped)
  + post-verifier (~3 min) ≈ 20 min worst case per cycle.
- Budget per full scaffold or per prove-next cycle: low-single-digit
  dollars with Sonnet.

## Timeout watchdog

`delegate()` in `formalize.sh` wraps every `claude -p` call in
`perl -e 'alarm shift; exec @ARGV'`, which installs a `SIGALRM` timer that
survives the `exec` and kills the subagent process if it runs past its
wall-clock budget:

- default budget: **600 s** (verifiers, parser, translator)
- fixer: **900 s** (its internal loop can do up to 12 builds)
- sorry-prover: **900 s** (up to 8 builds + tactic exploration)

If a subagent times out the driver logs the SIGALRM exit (rc=142) and
continues to the next stage, so the post-verifier always refreshes the
report — even if the prover stalled, the pipeline doesn't wedge.

## What the prover does (and doesn't) do

The `sorry-prover` agent attacks ONE sorry per invocation:

- Picks the target according to the driver-supplied selection mode:
  - `top-recommendation` (via `--prove-next`): take the verifier's
    "Recommended next steps" #1, skipping items marked as blocked on
    missing Mathlib API.
  - `most-tractable` (via `--prove-easiest`): scan ALL open sorries and
    pick the highest-scoring on a tractability rubric (short statement,
    concrete conclusion, no dep on other sorries, verifier hints like
    "~5 lines" or "straightforward").
- Checkpoints `Vlasov/Vlasov/Basic.lean` to `Basic.lean.prover-bak` before
  any edit.
- Iterates up to **8 build cycles** of "smallest viable edit" (single
  `exact?` / `apply?` probe, one `have h : … := by sorry` placeholder,
  one named tactic, etc. — max 3 tactic lines per iteration) followed
  by an immediate `lake build`. Whole-proof drafts are explicitly
  forbidden in the agent spec.
- On success: writes an attempt log at `formalize/logs/prover-cycle-N.md`
  with the final proof, lookup trail, and Mathlib lemmas used.
- On failure (8 iterations exhausted, or wall-clock timeout): reverts the
  file from the checkpoint and logs the iterations tried plus the
  wished-for Mathlib API.

The prover **never** weakens a statement to make it typecheck. If a
statement is malformed (e.g., the universal-vs-existential bug in
`weakEvolutionEmpiricalMeasure` that was caught earlier), it surfaces
that as a finding rather than fabricating a proof. Fixing malformed
statements is a manual step, not the prover's job.

## What this pipeline does *not* do

- It does **not** attempt unbounded automated proof search. Each
  `--prove-next` invocation tackles ONE sorry; the user is in the loop
  between cycles to triage results and decide what to attack next.
- It does **not** tighten imports. The translator emits `import Mathlib`
  to maximize the surface area available to the fixer and prover.
  Reducing imports is a follow-up step you can do by hand once the
  skeleton stabilizes.
- It does **not** edit the .tex.

## Re-targeting to a different paper

1. Drop your `paper.tex` next to `formalize.sh`.
2. Edit `formalize.sh`: change the `TEX=` line and pick a new
   `PROJECT=` name (e.g. `MyTheorem`).
3. Run `./formalize.sh` to scaffold, then `./formalize.sh --prove-next`
   to chip away at sorries.

The five agents are paper-agnostic — they reason from the outline produced
in stage 1, not from baked-in domain knowledge.

## Permissions

The driver runs `claude --permission-mode bypassPermissions` so the agents
do not prompt during the pipeline. Blast radius is bounded by each agent's
tool grants in its frontmatter: parser/translator/verifier never run shell
commands beyond `lake build`; the fixer and prover additionally edit the
target Lean file. None of the agents touch files outside this repo.

If you would rather review every action, run individual stages without the
driver:

```sh
claude       # interactive
> Use the latex-parser subagent to parse vlasov.tex into formalize/structure.md.
> Use the sorry-prover subagent to attack the top recommendation in formalize/report.md.
```
