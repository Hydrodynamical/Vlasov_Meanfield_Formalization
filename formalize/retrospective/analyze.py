#!/usr/bin/env python3
"""Build-path retrospective for the Vlasov formalization.

Extracts three data-direct series from the full git history and writes CSV + PNG:
  1. sorry trajectory: live `sorry` count per production file (leaf) + total, per commit.
  2. cumulative named lessons (CLAUDE.md L/P/M/B-series) over time.
  3. commit-type taxonomy.

Run from the repo root (the dir containing `Vlasov/`).
"""
import csv
import re
import subprocess
from collections import OrderedDict, Counter

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime

OUT = "formalize/retrospective"
PROD_RE = re.compile(r"^Vlasov/Vlasov/.*\.lean$")
SORRY_RE = re.compile(r"\bsorry\b")
LESSON_RE = re.compile(r"^###\s+([LPMB])(\d+)\.", re.MULTILINE)


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True).stdout


def git_bytes(*args):
    return subprocess.run(["git", *args], capture_output=True).stdout


# ---------------------------------------------------------------------------
# Lean comment stripping (line `--`, nested block `/- -/`, docstrings `/-- -/`),
# then count `\bsorry\b` in the surviving code. This is the honest "live sorry"
# count: the word "sorry" appears constantly in docstrings/prose here.
# ---------------------------------------------------------------------------
def count_live_sorry(text):
    out = []
    i, n, depth, in_line = 0, len(text), 0, False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            i += 1
            continue
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1; i += 2; continue
            if c == "-" and nxt == "/":
                depth -= 1; i += 2; continue
            i += 1; continue
        if c == "-" and nxt == "-":
            in_line = True; i += 2; continue
        if c == "/" and nxt == "-":
            depth += 1; i += 2; continue
        out.append(c); i += 1
    return len(SORRY_RE.findall("".join(out)))


# ---------------------------------------------------------------------------
# Commit list, chronological (oldest first).
# ---------------------------------------------------------------------------
def commit_list():
    raw = git("log", "--reverse", "--format=%H%x09%cI%x09%s").strip("\n").split("\n")
    rows = []
    for line in raw:
        h, iso, subj = line.split("\t", 2)
        rows.append((h, iso, subj))
    return rows


def short_name(path):
    # Vlasov/Vlasov/OT/CharacteristicFlow.lean -> OT/CharacteristicFlow
    p = path[len("Vlasov/Vlasov/"):]
    return p[:-len(".lean")]


# ===========================================================================
# 1. SORRY TRAJECTORY
# ===========================================================================
def sorry_trajectory(commits):
    per_commit = []          # (idx, date, hash, {file: count}, total)
    seen_files = OrderedDict()
    for idx, (h, iso, subj) in enumerate(commits):
        tree = git("ls-tree", "-r", "--name-only", h).split("\n")
        files = [f for f in tree if PROD_RE.match(f) and "Scratch" not in f]
        counts = {}
        for f in files:
            blob = git_bytes("show", f"{h}:{f}").decode("utf-8", "replace")
            c = count_live_sorry(blob)
            if c:
                counts[short_name(f)] = c
                seen_files[short_name(f)] = True
        total = sum(counts.values())
        per_commit.append((idx, iso[:10], h[:8], counts, total))
    files_sorted = list(seen_files.keys())

    # CSV
    with open(f"{OUT}/sorry_trajectory.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["idx", "date", "commit"] + files_sorted + ["total"])
        for idx, date, h, counts, total in per_commit:
            w.writerow([idx, date, h] + [counts.get(f, 0) for f in files_sorted] + [total])

    # Plot: stacked area of per-file (leaf) sorries; leaves sum to total.
    xs = [datetime.fromisoformat(c[1]) for c in per_commit]
    series = {f: [c[3].get(f, 0) for c in per_commit] for f in files_sorted}
    totals = [c[4] for c in per_commit]

    fig, ax = plt.subplots(figsize=(12, 5.5))
    ax.stackplot(xs, *[series[f] for f in files_sorted], labels=files_sorted, alpha=0.85)
    ax.plot(xs, totals, color="black", lw=1.6, label="total (= Σ leaves)")
    ax.set_title("Live sorry count by production file (leaf) and total\n"
                 "the proof frontier migrates Basic → CharacteristicFlow → WeakToLagrangian, "
                 "each driven to 0 (library: 0 live sorries at HEAD)")
    ax.set_ylabel("live sorries")
    ax.set_xlabel("commit date")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.legend(loc="upper left", fontsize=8, ncol=2)
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(f"{OUT}/sorry_trajectory.png", dpi=140)
    plt.close(fig)
    return per_commit, files_sorted


# ===========================================================================
# 2. CUMULATIVE NAMED LESSONS (CLAUDE.md L/P/M/B-series)
# ===========================================================================
def lessons_over_time():
    # commits that touched CLAUDE.md, chronological
    raw = git("log", "--reverse", "--format=%H%x09%cI", "--", "CLAUDE.md").strip("\n").split("\n")
    rows = []
    series_order = ["L", "P", "M", "B"]
    for line in raw:
        if not line.strip():
            continue
        h, iso = line.split("\t")
        blob = git_bytes("show", f"{h}:CLAUDE.md").decode("utf-8", "replace")
        ids = set(LESSON_RE.findall(blob))           # set of (series, num)
        by_series = Counter(s for s, _ in ids)
        rows.append((iso[:10], h[:8], by_series, len(ids)))

    with open(f"{OUT}/lessons_cumulative.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["date", "commit"] + series_order + ["total"])
        for date, h, bs, total in rows:
            w.writerow([date, h] + [bs.get(s, 0) for s in series_order] + [total])

    xs = [datetime.fromisoformat(r[0]) for r in rows]
    fig, ax = plt.subplots(figsize=(12, 5.5))
    colors = {"L": "#1f77b4", "P": "#d62728", "M": "#2ca02c", "B": "#9467bd"}
    names = {"L": "L — Lean/tooling", "P": "P — process", "M": "M — math", "B": "B — bridging"}
    cum = {s: [r[2].get(s, 0) for r in rows] for s in series_order}
    ax.stackplot(xs, *[cum[s] for s in series_order],
                 labels=[names[s] for s in series_order],
                 colors=[colors[s] for s in series_order], alpha=0.85, step="post")
    totals = [r[3] for r in rows]
    ax.step(xs, totals, where="post", color="black", lw=1.6, label="total named lessons")
    # annotate the taxonomy-crystallization commit (four-series naming)
    ax.set_title("Cumulative named lessons in CLAUDE.md, by series (L/P/M/B)\n"
                 "the discipline framework as accumulating reusable meta-knowledge")
    ax.set_ylabel("named lessons present")
    ax.set_xlabel("commit date")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.legend(loc="upper left", fontsize=9)
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(f"{OUT}/lessons_cumulative.png", dpi=140)
    plt.close(fig)
    return rows


# ===========================================================================
# 3. COMMIT-TYPE TAXONOMY
# ===========================================================================
def classify(subj):
    s = subj.lower()
    # Meta / discipline / lessons
    if (re.search(r"\b(discipline|lesson|project memory|claude\.md|watch-list|ossif)", s)
            or re.search(r"\b[lpmb]\d+\b", s) or "notes+discipline" in s):
        return "Discipline / lessons"
    # Tooling / harness / agents
    if re.search(r"\b(formalize|sorry-prover|sorry-decomposer|decompos|prover|agent|"
                 r"driver|watchdog|harness|pipeline|verifier|translator|fixer|blueprint|"
                 r"outline|codebase-outliner|latexmk|plastex)\b", s):
        return "Tooling / docs-gen"
    # Plain documentation
    if (subj.split(":")[0].strip().lower() in {"doc", "docs", "notes", "readme"}
            or s.startswith("doc:") or s.startswith("notes")):
        return "Documentation"
    # Spec / LaTeX
    if re.search(r"\b(vlasov\.tex|latex|\.tex|spec)\b", s):
        return "Spec (LaTeX)"
    # everything else = core Lean proof work (ot/basic/phase/stage/step/bridge/...)
    return "Core proof (Lean)"


def commit_taxonomy(commits):
    cats = Counter()
    prefixes = Counter()
    for h, iso, subj in commits:
        cats[classify(subj)] += 1
        pre = re.split(r"[:(]", subj)[0].strip().lower()
        prefixes[pre] += 1

    cat_order = ["Core proof (Lean)", "Discipline / lessons", "Tooling / docs-gen",
                 "Documentation", "Spec (LaTeX)"]
    cat_order = [c for c in cat_order if c in cats] + \
                [c for c in cats if c not in cat_order]

    with open(f"{OUT}/commit_taxonomy.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["category", "commits", "pct"])
        tot = sum(cats.values())
        for c in cat_order:
            w.writerow([c, cats[c], f"{100*cats[c]/tot:.1f}"])
        w.writerow(["TOTAL", tot, "100.0"])

    with open(f"{OUT}/commit_prefixes.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["raw_prefix", "commits"])
        for p, n in prefixes.most_common():
            w.writerow([p, n])

    fig, ax = plt.subplots(figsize=(9, 5))
    vals = [cats[c] for c in cat_order]
    bars = ax.barh(cat_order[::-1], vals[::-1], color="#4c72b0")
    tot = sum(vals)
    for b, v in zip(bars, vals[::-1]):
        ax.text(b.get_width() + tot*0.01, b.get_y() + b.get_height()/2,
                f"{v}  ({100*v/tot:.0f}%)", va="center", fontsize=9)
    ax.set_title(f"Commit-type taxonomy ({tot} commits)")
    ax.set_xlabel("commits")
    ax.set_xlim(0, max(vals) * 1.18)
    ax.grid(True, axis="x", alpha=0.25)
    fig.tight_layout()
    fig.savefig(f"{OUT}/commit_taxonomy.png", dpi=140)
    plt.close(fig)
    return cats, cat_order


def main():
    commits = commit_list()
    print(f"{len(commits)} commits")
    pc, files = sorry_trajectory(commits)
    print(f"sorry trajectory: {len(files)} files ever carried sorries; "
          f"peak total = {max(c[4] for c in pc)}; HEAD total = {pc[-1][4]}")
    lr = lessons_over_time()
    print(f"lessons: {len(lr)} CLAUDE.md commits; final lesson count = {lr[-1][3]}")
    cats, order = commit_taxonomy(commits)
    print("taxonomy:", {c: cats[c] for c in order})
    print("wrote CSV + PNG to", OUT)


if __name__ == "__main__":
    main()
