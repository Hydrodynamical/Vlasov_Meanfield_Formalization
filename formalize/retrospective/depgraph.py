#!/usr/bin/env python3
"""Extract the blueprint dependency-graph DOT source and render it to a static
vector PDF (+ PNG preview) for inclusion in the paper.

The leanblueprint/plastexdepgraph web output renders the graph client-side with
d3-graphviz from a DOT string embedded in `dep_graph_document.html`
(`.renderDot(`...`)`). We pull that exact string out, swap the transparent
background for white (for print), and render with graphviz `dot`.

Run from repo root:  python3 formalize/retrospective/depgraph.py
Requires graphviz (`dot`).
"""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HTML = ROOT / "formalize/phase-d/blueprint-demo/blueprint/web/dep_graph_document.html"
OUTDIR = Path(__file__).resolve().parent
DOT = OUTDIR / "blueprint_depgraph.dot"
PDF = OUTDIR / "blueprint_depgraph.pdf"
PNG = OUTDIR / "blueprint_depgraph.png"


def main():
    html = HTML.read_text(encoding="utf-8")
    m = re.search(r"\.renderDot\(`(.*?)`\)", html, re.DOTALL)
    if not m:
        raise SystemExit("could not find renderDot(`...`) in the blueprint HTML")
    dot = m.group(1)
    # print on white rather than transparent; give the DAG a bit more breathing room.
    dot = dot.replace("graph [bgcolor=transparent];",
                      "graph [bgcolor=white, rankdir=TB, nodesep=0.25, ranksep=0.45];")
    DOT.write_text(dot, encoding="utf-8")
    subprocess.run(["dot", "-Tpdf", str(DOT), "-o", str(PDF)], check=True)
    subprocess.run(["dot", "-Tpng", "-Gdpi=150", str(DOT), "-o", str(PNG)], check=True)
    nodes = len(re.findall(r'\[color=', dot))
    edges = dot.count("->")
    print(f"wrote {PDF.name}, {PNG.name}  ({nodes} nodes, {edges} edges)")


if __name__ == "__main__":
    main()
