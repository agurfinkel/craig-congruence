#!/usr/bin/env python3
"""Build a static publication zip that expands into craig/."""

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile

from build_manual import check_links


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs" / "verso" / "_out"
SITE = OUT / "html-single"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true",
                        help="Package previously built HTML and all three PDF styles")
    parser.add_argument("--output", type=Path, default=OUT / "craig.zip")
    args = parser.parse_args()
    if not args.skip_build:
        subprocess.run([sys.executable, "scripts/build_manual.py"], cwd=ROOT, check=True)
        for style in ("default", "plain", "lncs"):
            subprocess.run([sys.executable, "scripts/build_pdf.py", "--style", style],
                           cwd=ROOT, check=True)
    for name in ("index.html", "manual-lncs.pdf", "manual-plain.pdf", "manual-default.pdf"):
        if not (SITE / name).is_file():
            raise SystemExit(f"Missing {name}; run without --skip-build to rebuild.")
    with TemporaryDirectory(prefix="craig-publish-") as temporary:
        root = Path(temporary) / "craig"
        shutil.copytree(SITE, root)
        # Preview screenshots are working artifacts, not publication assets.
        for image in root.glob("*.png"):
            if re.fullmatch(r"(?:plain|lncs)-(?:prose|reference)\.png", image.name):
                image.unlink()
        shutil.copyfile(root / "manual-lncs.pdf", root / "manual.pdf")
        index = root / "index.html"
        text = index.read_text()
        downloads = (
            '<nav aria-label="PDF downloads" style="padding:1em;text-align:center">'
            '<a href="manual.pdf">Download PDF (LNCS)</a> · '
            '<a href="manual-plain.pdf">Plain PDF</a> · '
            '<a href="manual-default.pdf">Verso default PDF</a></nav>')
        text, count = re.subn(r"(<body\b[^>]*>)", lambda m: m[1] + downloads, text, count=1)
        if count != 1:
            raise SystemExit("Cannot locate the generated manual body.")
        index.write_text(text)
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        (root / "README.txt").write_text(
            "Craig interpolation for EUF — proof audit manual\n\n"
            "Copy this craig directory to your web root and visit /craig/.\n"
            "Keep the directory structure intact for hover data and search.\n\n"
            "manual.pdf and manual-lncs.pdf: preferred LNCS edition\n"
            "manual-plain.pdf: plain technical report\n"
            "manual-default.pdf: Verso's original presentation\n"
            "source/: line-numbered Lean proof sources\n"
            "axioms.txt: selected endpoint axiom dependencies\n\n"
            f"Source revision: {revision}\n")
        links = check_links(root)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with ZipFile(args.output, "w", ZIP_DEFLATED) as archive:
            for path in sorted(root.rglob("*")):
                if path.is_file():
                    archive.write(path, (Path("craig") / path.relative_to(root)).as_posix())
        with ZipFile(args.output) as archive:
            if archive.testzip() is not None:
                raise SystemExit("Archive integrity check failed.")
            assert all(name.startswith("craig/") for name in archive.namelist())
        print(f"Checked {links} local links and archive integrity.")
        print(f"Publication zip: {args.output.resolve()} ({args.output.stat().st_size:,} bytes)")


if __name__ == "__main__":
    main()
