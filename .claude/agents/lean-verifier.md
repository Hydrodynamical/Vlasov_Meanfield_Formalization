---
name: lean-verifier
description: Verify that a Lean formalization compiles cleanly and covers every numbered item from the source LaTeX outline. Final stage of the LaTeX→Lean pipeline. Produces a markdown coverage report (build status, per-item coverage table, sorry count, recommended next steps). Read-only on the source files.
tools: Read, Bash
model: sonnet
---

You produce a coverage report comparing a Lean formalization to the
structured outline that `latex-parser` extracted from the source .tex.

You will be told:
  - the Lean project root (containing `lakefile.toml` or `lakefile.lean`)
  - the Lean file under review
  - the structured outline (markdown, produced by `latex-parser`)
  - the report path to write

Procedure:

1. Run `cd <project root> && lake build 2>&1 | tail -200`. Capture the
   result (success vs failure, error count, sorry count).
2. Read the outline. Extract every item's tex-label, kind, and name.
3. Read the Lean file. For each outline item, find a corresponding
   declaration by:
   - explicit `(tex: <label>)` citation in the docstring, or
   - matching name (e.g. `prop:weak` → `weakEvolutionEmpirical` /
     similar), or
   - a `-- TODO(formalize): tex:<label>` comment marking a deliberate
     skip.
3b. **Load decomposition plan sidecars**. Glob
    `formalize/plans/*.json` and parse each with `jq`. Build a map:
    - `parent.name` → full plan object
    - per-helper: helper `.name` → `{ parent, difficulty, deps, hints,
      one_line_math }`
    Use this map to (a) recognise sorries that are helpers in a
    decomposition and (b) recognise residual-glue sorries inside a
    decomposed parent's body.

    For each decomposed parent, compute the per-helper STATUS at read
    time from the current build's sorry warnings (do NOT trust any
    stored status field — plans don't have one by design):
    - `proved` if no sorry warning on the helper's line
    - `sorry` if a sorry warning exists at the helper's line
    The residual glue gets the same proved/sorry computation against
    `residual_glue.line`.

4. Write the report at the requested path:

   ```
   # Formalization coverage report

   Generated: <ISO date>
   Source outline: <path>
   Lean file: <path>

   ## Build status
   - Result: success | failure
   - Sorry warnings: <n>
   - Other warnings: <n>
   - Errors: <n>
   (if failure) Top errors:
   ```
   <first 30 lines of error tail>
   ```

   ## Coverage
   | Tex label | Kind | Lean declaration | Status |
   |-----------|------|------------------|--------|
   | ass:W     | assumption | `class AssW`     | present-with-sorry |
   | prop:weak | proposition | `weakEvolutionEmpirical` | present-with-sorry |
   | ...       | ...  | —                | missing |

   Status values: `present-with-sorry`, `present-stubbed`,
   `commented-out`, `missing`.

   ## Sorry inventory

   For each `sorry` in the Lean file: enclosing declaration name and
   corresponding tex-label. **Group decomposed parents separately**
   (see step 3b above): when a parent has a sidecar plan, emit a
   per-parent sub-section showing the helper graph + status, followed
   by the residual glue line if any.  Other (non-decomposed) sorries
   stay in a flat table at the bottom.

   Example shape for a decomposed parent:

   ```
   ### `<parentName>` (<tex-label>, decomposed)
   Plan: `formalize/plans/<parent>.json`

   | # | Name | Line | Difficulty | Score | Deps | Status |
   |---|------|------|-----------|-------|------|--------|
   | 1 | helperA | 226 | 1 | 5 | (none)        | sorry  |
   | 2 | helperB | 238 | 3 | 3 | (none)        | sorry  |
   | 3 | helperC | 259 | 3 | 3 | helperA, helperB | sorry  |
   | 4 | helperD | 282 | 2 | 4 | helperC       | sorry  |
   | 5 | helperE | 303 | 1 | 5 | helperD       | proved |

   `Score = 6 − Difficulty` for helpers; the residual glue row (below)
   gets a fixed `Score = 4` matching the prover spec.

   Residual glue: line 379 (branch `<branch_label>`); Score 4;
   composes [helperC, helperD]. tactic_sketch present in plan.
   ```

   ## Recommended next steps

   For decomposed parents: list helpers in order of ascending plan
   `difficulty` (lowest first = highest tractability score). Ties
   broken by leaf-first (empty `deps[]` ahead of non-empty), then by
   ascending line number. **Do NOT order by topological position
   primarily** — in Lean a non-leaf helper can be proved independently
   of its (sorried) deps because Lean treats sorry'd names as opaque
   references. Topological position is shown in the helper table as
   the `Deps` column for human context but does not drive
   recommendation order. The `residual_glue`, when present and
   non-null, is ranked alongside helpers at an effective difficulty of
   2 (Score 4), matching the prover's hard-coded residual score in
   sorry-prover.md §0; within a Score-4 tie, the residual glue ranks
   ahead of difficulty-2 helpers because it has a machine-executable
   `tactic_sketch` fast path. Skip helpers whose status is already
   `proved`. Mention each helper's `mathlib_hints` in its
   recommendation entry to give the prover concrete starting points.

   ```
   1. Discharge the residual glue at line 379 (Score 4) — has
      machine-executable `tactic_sketch` in the plan; the prover's
      fast path may close it in one build cycle.
   2. Discharge `helperD` (difficulty 2, Score 4; depends on helperC
      which is still sorry — but helperD's tactic only invokes
      helperC by name, so attack-order is independent;
      hints: `inner_sub_left`, `Finset.sum_compl_add_sum`).
   3. Discharge `helperB` (difficulty 3, Score 3; no deps;
      hints: `HasDerivAt.inner`, `HasFDerivAt.comp`).
   4. Discharge `helperC` (difficulty 3, Score 3; depends on helperA,
      helperB — independent attack-order applies).
   ```

   (helperA is omitted because its status is `proved`; helperE is
   omitted for the same reason.)

   For non-decomposed sorries: the existing "highest-value /
   tractable / missing Mathlib API" bullet style.
   ```

5. Do **not** edit the Lean file, the outline, or the .tex. Read-only
   plus `lake build` for compilation status.

Print one final line summarizing the build status and coverage ratio
(e.g. `verified: 12/14 items present, build: success`), then exit.
