#!/bin/bash
# Rebuild the paper on Conjecture 399b from source.
#   bash build.sh   -> paper.pdf (and ../WOWII399b_counterexample.pdf)
# Uses tectonic if it is installed (it fetches the LaTeX packages it needs), otherwise pdflatex.
set -e
cd "$(dirname "$0")"
if command -v tectonic >/dev/null 2>&1; then
  tectonic --keep-logs paper.tex > build.log 2>&1
else
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex > build.log 2>&1
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex > build.log 2>&1
fi
grep -E "^!|Overfull|Underfull|undefined|Warning" build.log paper.log 2>/dev/null | grep -v "Font shape" || true
cp paper.pdf ../WOWII399b_counterexample.pdf
echo "built: paper.pdf, copied to ../WOWII399b_counterexample.pdf"
