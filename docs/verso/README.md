# EUF interpolation audit manual

The manual follows the proof's ideas: conditional equality exchange, theory
leaves, the falsified-clause invariant, and shared-interface extraction. It
targets a human auditor who will inspect Lean for the finer details. The
seam-lean audit manual supplies the presentation model.

Edit the chapters directly in `Audit/*.lean` and the introduction in
`Audit.lean`. Verso checks the Lean examples and reads reference declarations
from the imported environment. Source links open complete, line-numbered
files bundled with the rendered manual. The manual imports the current
interpolation library and the longer Proof 43 trace explicitly.

The reference chapter allows missing docstrings on structure fields and
constructors. Verso still checks declaration lookup and displays their types;
missing prose produces warnings rather than omitting those declarations.

## Build

This is a separate Lake package. The root proof package keeps its existing
dependencies and Lean 4.35.0 toolchain. The documentation pins Verso's
4.35.0 release (`304b8561790c50222551c937ce02928df0d5b445`); its transitive
dependencies are locked in this directory's `lake-manifest.json`.

From the repository root, initialize once:

```sh
cd docs/verso
lake update
cd ../..
```

Then build, render, bundle source files, check local links and anchors, and
audit the selected endpoints' axiom dependencies:

```sh
python3 scripts/build_manual.py
```

The initial build compiles Verso and can take several minutes. Later builds
reuse Lake artifacts. No globally built Verso is required. The local checkout
at `/ag/git/verso` currently targets a different Lean release; the documentation
uses its own pinned version rather than changing either checkout's toolchain.

To reuse that local Git history before initialization, optionally run:

```sh
git clone --no-hardlinks /ag/git/verso docs/verso/.lake/packages/verso
```

Then initialize normally. Lake selects the pinned commit; the local checkout
is only a seed. Other dependencies may still require downloading.

## Read

Serve the generated manual over HTTP so Verso can fetch its hover data:

```sh
python3 -m http.server 8000 --bind 127.0.0.1 \
  --directory docs/verso/_out/html-single
```

Open <http://localhost:8000>. When working remotely, forward port 8000 over
SSH. The generated `html-single` directory is self-contained and includes
the Lean source pages and `axioms.txt`; it can also be copied for review.
The build uses the Marked JavaScript bundled with Verso in place of the
generated CDN script, so reading does not require a connection to that CDN.

`_out` and `.lake` are generated and ignored by Git. The build's axiom check
allows `propext`, `Classical.choice`, and `Quot.sound` and rejects other axiom
dependencies, including `sorryAx`, at the endpoints listed in `AxiomAudit.lean`.
This audits the selected dependency closures, not every declaration in the repo.

## LaTeX and PDF

On Ubuntu 24.04, install LuaLaTeX, the LaTeX packages used by Verso, its
Source Pro fonts, and the DejaVu monospace font:

```sh
sudo apt update
sudo apt install --no-install-recommends \
  texlive-luatex texlive-latex-extra texlive-fonts-extra \
  fonts-dejavu-core latexmk
```

`texlive-fonts-extra` is a large download. Generate LaTeX from the same
checked chapters, without regenerating the HTML:

```sh
cd docs/verso
lake exe audit --with-tex --without-html-single --output _out
```

Then compile it, letting latexmk repeat LuaLaTeX until references settle:

```sh
cd _out/tex
latexmk -lualatex -interaction=nonstopmode -halt-on-error main.tex
```

The output is `docs/verso/_out/tex/main.pdf` from the repository root.
Source links currently target
the HTML manual's bundled pages and are intended for the served HTML edition.

LNCS is the preferred PDF edition. From the repository root:

```sh
python3 scripts/build_pdf.py
```

This generates `_out/tex/main-lncs.pdf`, also copied to the HTML directory
as `manual.pdf` and `manual-lncs.pdf`.

For the plain technical-report alternative:

```sh
python3 scripts/build_pdf.py --style plain
```

This generates and compiles `docs/verso/_out/tex/main-plain.pdf`.
Edit `docs/verso/plain.tex` to adjust its DejaVu fonts,
spacing, headings, and declaration boxes. The script regenerates the checked
content before applying the style. If the HTML manual has been built, it also
copies the PDF there as `manual-plain.pdf`. Use `--style default` to build
the original Verso edition as `manual-default.pdf` for comparison.

For the CAV/LNCS paper layout:

```sh
python3 scripts/build_pdf.py --style lncs
```

This uses Springer's unmodified LNCS 2.26 class (vendored in `latex/llncs/`)
with its serif typography and page geometry. Chapters become sections that
flow continuously; the separate cover and contents pages are omitted.
Lean examples and declaration signatures still come from the same checked
Verso source. `lncs.tex` removes decorative declaration frames and printed
URL footnotes. The output is `_out/tex/main-lncs.pdf`, also copied to
`_out/html-single/manual-lncs.pdf`. This is a paper-style reading edition,
not a claim of compliance with conference submission requirements.

## Publish a static copy

```sh
python3 scripts/package_manual.py
```

This builds and checks the HTML and all three PDF editions, then creates
`docs/verso/_out/craig.zip`. Extract it into your web root: it creates a
single `craig/` directory with `index.html`, PDF download links, search and
hover assets, line-numbered Lean sources, and the axiom report. Visit
`https://YOUR-SITE/craig/`. The LNCS PDF is also available at `craig/manual.pdf`.

The archive is a generated artifact and is not committed. To package the
current rendered files without rebuilding, use `--skip-build`.
