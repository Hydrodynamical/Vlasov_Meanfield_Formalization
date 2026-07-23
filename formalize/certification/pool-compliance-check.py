#!/usr/bin/env python3
"""Measure this project against lean-pool's content-quality rules.

Mirrors the enforced checks of https://github.com/Vilin97/lean-pool
python/lean_pool/quality.py (fetched 2026-07-22): file-size cap (10,000
non-comment code lines), proof-size cap (200 code lines per theorem/lemma
body, text heuristic), and the forbidden-content scan (set_option, nolint,
broad `import Mathlib`, sorry/admit, axiom/constant/unsafe/partial/opaque/
@[extern], diagnostic commands). The two counting helpers are copied
verbatim from quality.py so the numbers here are the numbers their CI
computes. Run from the repo root:

    python3 formalize/certification/pool-compliance-check.py

Exit code 0 iff no violations. Not a Lean check — pair with lake build,
sorry-scan.lean, and footprint-check.lean.
"""

import re
import sys
from pathlib import Path

LEAN_ROOT = Path(__file__).resolve().parents[2] / "Vlasov" / "Vlasov"

DECLARATION_PREFIX = (
    r"(?:@\[[^\n\]]+\]\s+)*"
    r"(?:(?:private|protected|noncomputable|scoped)\s+)*"
)
FORBIDDEN_DIAGNOSTICS = re.compile(
    r"^\s*#(?:check|print|eval!?|reduce|guard_msgs|lint)\b"
)
FORBIDDEN_SOUNDNESS = re.compile(
    r"\b(?:axiom|constant|unsafe|partial|opaque)\b|@\[\s*extern\b"
)


# Copied verbatim from lean-pool python/lean_pool/quality.py (Apache-2.0).
def _strip_lean_comments(text: str) -> str:
    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth > 0:
            if pair == "/-":
                block_depth += 1
                result.append("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.append("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            result.append("  ")
            index += 2
        elif pair == "/-":
            block_depth = 1
            result.append("  ")
            index += 2
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1

    return "".join(result)


def _non_comment_code_lines(text: str) -> int:
    stripped = _strip_lean_comments(text)
    return sum(1 for line in stripped.splitlines() if line.strip())


def _declaration_starts(stripped: str) -> list[tuple[int, str]]:
    pattern = re.compile(rf"^\s*{DECLARATION_PREFIX}(?:theorem|lemma)\b")
    return [
        (index, line)
        for index, line in enumerate(stripped.splitlines(), start=1)
        if pattern.match(line)
    ]


def check_file(path: Path) -> list[str]:
    problems: list[str] = []
    text = path.read_text()
    rel = path.relative_to(LEAN_ROOT)

    code_lines = _non_comment_code_lines(text)
    if code_lines > 10000:
        problems.append(f"{rel}: file has {code_lines} code lines; limit is 10000")

    stripped = _strip_lean_comments(text)
    for line_number, line in enumerate(stripped.splitlines(), start=1):
        if re.search(r"\bset_option\b", line):
            problems.append(f"{rel}:{line_number}: set_option is forbidden")
        if re.search(r"\bnolint\b", line):
            problems.append(f"{rel}:{line_number}: nolint waiver is forbidden")
        if re.match(r"^\s*(?:public\s+)?import\s+Mathlib\s*$", line):
            problems.append(f"{rel}:{line_number}: broad import Mathlib is forbidden")
        if re.search(r"\b(?:sorry|admit)\b", line):
            problems.append(f"{rel}:{line_number}: sorry/admit is forbidden")
        if FORBIDDEN_SOUNDNESS.search(line):
            problems.append(f"{rel}:{line_number}: unchecked declaration is forbidden")
        if FORBIDDEN_DIAGNOSTICS.search(line):
            problems.append(f"{rel}:{line_number}: diagnostic command is forbidden")

    original_lines = text.splitlines()
    starts = _declaration_starts(stripped)
    for index, (start_line, _) in enumerate(starts):
        end_line = (
            starts[index + 1][0] if index + 1 < len(starts) else len(original_lines) + 1
        )
        block = original_lines[start_line - 1 : end_line - 1]
        try:
            body_start = next(offset for offset, line in enumerate(block) if ":=" in line)
        except StopIteration:
            continue
        body = "\n".join(block[body_start:])
        proof_lines = _non_comment_code_lines(body)
        if proof_lines > 200:
            problems.append(
                f"{rel}:{start_line}: proof has {proof_lines} code lines; limit is 200"
            )

    return problems


def main() -> int:
    files = sorted(LEAN_ROOT.rglob("*.lean"))
    if not files:
        print(f"no .lean files found under {LEAN_ROOT}", file=sys.stderr)
        return 2
    all_problems: list[str] = []
    for path in files:
        all_problems.extend(check_file(path))
    for problem in all_problems:
        print(problem)
    print(
        f"\n{len(all_problems)} violation(s) across {len(files)} file(s) "
        f"(lean-pool content rules)"
    )
    return 1 if all_problems else 0


if __name__ == "__main__":
    sys.exit(main())
