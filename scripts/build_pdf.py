#!/usr/bin/env python3
"""Render PDFs from Verso's checked manual content (LNCS by default)."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs" / "verso"
OUT = DOC / "_out" / "tex"


def plain_document(original):
    class_line = r"\documentclass[oneside]{memoir}"
    if original.count(class_line) != 1:
        raise SystemExit("Verso's document class changed; review the plain font-size setting.")
    return original.replace(class_line, r"\documentclass[11pt,oneside]{memoir}", 1)


def lncs_document(original):
    class_line = r"\documentclass[oneside]{memoir}"
    if original.count(class_line) != 1:
        raise SystemExit("Verso's document class changed; review the LNCS adapter.")
    original = original.replace(class_line, r"\documentclass[runningheads]{llncs}", 1)
    for package in ("sourcecodepro", "sourcesanspro", "sourceserifpro"):
        original = original.replace("\\usepackage{" + package + "}", "")
    original = original.replace(r"\usepackage{fancyvrb}",
                                "\\usepackage{fontspec}\n\\usepackage{fancyvrb}", 1)
    # Keep hyperref's native link command rather than Verso's printed-URL
    # footnotes. Remove the wrapper instead of aliasing a redefined command.
    original, count = re.subn(
        r"\\let\\oldhref\\href.*?(?=\\usepackage\[normalem\]\{ulem\})",
        "", original, flags=re.S)
    if count != 1:
        raise SystemExit("Verso's hyperlink wrapper changed; review the LNCS adapter.")
    # Remove only memoir's generated layout setup. Retain Verso's rendering
    # macros and all content after the title metadata.
    original, count = re.subn(
        r"\\makechapterstyle\{lean\}.*?(?=\\title\{)", "", original, flags=re.S)
    if count != 1:
        raise SystemExit("Verso's layout preamble changed; review the LNCS adapter.")
    original = original.replace(r"\sffamily ", "")
    for command in (r"\frontmatter", r"\mainmatter", r"\backmatter",
                    r"\begin{titlingpage}", r"\end{titlingpage}",
                    r"\tableofcontents", r"\cleardoublepage"):
        original = original.replace(command, "")
    # One simultaneous substitution prevents promoting a heading twice.
    headings = {"chapter": "section", "section": "subsection",
                "subsection": "subsubsection", "subsubsection": "paragraph"}
    original = re.sub(r"\\(chapter|section|subsection|subsubsection)(?=\{)",
                      lambda match: "\\" + headings[match[1]], original)
    original = original.replace(r"\begin{document}",
        "\\institute{}\n\\titlerunning{Craig interpolation for EUF}\n"
        "\\authorrunning{}\n\\begin{document}", 1)
    # Only the presentation layer changes: original section labels and every
    # Lean code display remain untouched.
    return original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--style", choices=("lncs", "plain", "default"), default="lncs")
    style = parser.parse_args().style
    if shutil.which("latexmk") is None or shutil.which("lualatex") is None:
        raise SystemExit("Install LuaLaTeX and latexmk; see docs/verso/README.md")
    subprocess.run([
        "lake", "exe", "audit", "--with-tex", "--without-html-single",
        "--without-html-multi", "--output", "_out",
    ], cwd=DOC, check=True)
    original = (OUT / "main.tex").read_text()
    if style == "plain":
        original = plain_document(original)
    elif style == "lncs":
        original = lncs_document(original)
    document = r"\begin{document}"
    if original.count(document) != 1:
        raise SystemExit("Verso's LaTeX layout changed; review the style insertion point.")
    # The project's style follows Verso's preamble, so it overrides presentation
    # while retaining the generated declarations and checked examples verbatim.
    if style != "default":
        shutil.copyfile(DOC / f"{style}.tex", OUT / f"{style}.tex")
    if style == "lncs":
        shutil.copyfile(DOC / "latex" / "llncs" / "llncs.cls", OUT / "llncs.cls")
    styled = (original if style == "default" else
              original.replace(document, f"\\input{{{style}.tex}}\n" + document, 1))
    stem = "main" if style == "default" else f"main-{style}"
    (OUT / f"{stem}.tex").write_text(styled)
    cache = DOC / ".lake" / "texmf-var"
    cache.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, TEXMFVAR=str(cache), TEXMFCACHE=str(cache))
    subprocess.run([
        "latexmk", "-lualatex", "-interaction=nonstopmode", "-halt-on-error",
        f"{stem}.tex",
    ], cwd=OUT, env=env, check=True)
    site = DOC / "_out" / "html-single"
    if site.is_dir():
        shutil.copyfile(OUT / f"{stem}.pdf", site / f"manual-{style}.pdf")
        if style == "lncs":
            shutil.copyfile(OUT / f"{stem}.pdf", site / "manual.pdf")
    print(f"{style.upper()} PDF: {OUT / f'{stem}.pdf'}")


if __name__ == "__main__":
    main()
