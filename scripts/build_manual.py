#!/usr/bin/env python3
"""Build the Verso audit manual and bundle its evidence for offline reading."""

import html
from html.parser import HTMLParser
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import unquote, urljoin, urlsplit


ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs" / "verso"
SITE = DOC / "_out" / "html-single"


def run(*args, capture=False):
    result = subprocess.run(args, cwd=DOC, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None)
    return result.stdout


def bundle_sources():
    # Follow only repository-local imports, including the explicitly imported
    # long example. Archived is outside this dependency closure.
    pending = ["ClausalProofInterpolation", "ClausalProofInterpolation.Z3Proof43Trace"]
    modules = set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            continue
        modules.add(module)
        pending.extend(name for line in re.findall(r"^import (.+)$", source.read_text(), re.M)
                       for name in line.split())
    for module in sorted(modules):
        source = ROOT / (module.replace(".", "/") + ".lean")
        relative = source.relative_to(ROOT)
        destination = SITE / "source" / relative.with_suffix(".lean.html")
        destination.parent.mkdir(parents=True, exist_ok=True)
        lines = "\n".join(
            f'<span id="L{i}"><a href="#L{i}">{i:4}</a>  {html.escape(line)}</span>'
            for i, line in enumerate(source.read_text().splitlines(), 1))
        destination.write_text(
            '<!doctype html><html lang="en"><meta charset="utf-8"><title>'
            + html.escape(str(relative)) + '</title><style>'
            'span:target{background:#fff1a8} a{color:#666} pre{line-height:1.5}'
            '</style><pre>' + lines + '</pre></html>')
    return len(modules)


def localize_assets():
    # This Verso release emits a CDN script despite shipping Marked itself.
    # Use its bundled UMD build so the rendered manual works offline too.
    marked = DOC / ".lake" / "packages" / "verso" / "vendored-js" / "marked"
    shutil.copytree(marked, SITE / "vendor" / "marked", dirs_exist_ok=True)
    for page in SITE.rglob("*.html"):
        content = page.read_text()
        content = re.sub(
            r'<script src="https://cdn.jsdelivr.net/npm/marked@11\.1\.1/marked\.min\.js"[^>]*></script>',
            '<script src="vendor/marked/marked.umd.min.js"></script>', content)
        page.write_text(content)


class Links(HTMLParser):
    def __init__(self, content):
        super().__init__()
        self.urls = []
        self.ids = set()
        self.base = None
        self.feed(content)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "base":
            if self.base is None and "href" in attrs:
                self.base = attrs["href"]
            return
        if "id" in attrs:
            self.ids.add(attrs["id"])
        for attr in ("href", "src"):
            if attr in attrs:
                self.urls.append(attrs[attr])


def check_links(site=SITE):
    pages = {path: Links(path.read_text()) for path in site.rglob("*.html")}
    count = 0
    for page, parsed in pages.items():
        base = urljoin(page.as_uri(), parsed.base or "")
        for raw in parsed.urls:
            url = urlsplit(raw)
            if url.scheme or url.netloc or raw.startswith("/"):
                continue
            resolved = urlsplit(urljoin(base, raw))
            target = Path(unquote(resolved.path)).resolve()
            if target.is_dir():
                target /= "index.html"
            if not target.is_file():
                raise SystemExit(f"Broken link in {page}: {raw}")
            if resolved.fragment and target.suffix == ".html":
                target_page = pages.get(target)
                if target_page is None:
                    target_page = Links(target.read_text())
                if unquote(resolved.fragment) not in target_page.ids:
                    raise SystemExit(f"Missing anchor in {page}: {raw}")
            count += 1
    return count


def audit_axioms():
    report = run("lake", "env", "lean", "AxiomAudit.lean", capture=True)
    expected = re.findall(r"^#print axioms (\S+)", (DOC / "AxiomAudit.lean").read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", report)
    if found != expected:
        raise SystemExit("Incomplete axiom report:\n" + report)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", report):
        unexpected = {name.strip() for name in group.split(",")} - allowed
        if unexpected:
            raise SystemExit("Unexpected axioms: " + ", ".join(sorted(unexpected)))
    (SITE / "axioms.txt").write_text(report)
    return len(expected)


def main():
    if (DOC / "lean-toolchain").read_text() != (ROOT / "lean-toolchain").read_text():
        raise SystemExit("Documentation and proof toolchains differ; review Verso compatibility.")
    if not (DOC / ".lake" / "packages" / "verso").exists():
        raise SystemExit("Initialize documentation dependencies first: cd docs/verso && lake update")
    run("lake", "build", "audit")
    run("lake", "exe", "audit", "--output", "_out")
    localize_assets()
    sources = bundle_sources()
    endpoints = audit_axioms()
    links = check_links()
    print(f"Checked {endpoints} axiom dependencies and {links} local links; bundled {sources} sources.")
    print(f"Manual: {SITE / 'index.html'}")


if __name__ == "__main__":
    main()
