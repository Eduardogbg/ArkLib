#!/usr/bin/env python3
"""ABF26 branch lint.

Runs ArkLib-convention checks on the files listed in
``scripts/abf26/owned-files.txt``. The goal is to keep our branch's
contributions aligned with project style and citation conventions so the
final PR integrates cleanly.

Checks (severity in brackets):
  [error] `fun X => Y` lambdas (must use `↦`)
  [error] trailing whitespace
  [error] tab characters
  [error] lines longer than 100 chars
  [error] file does not end with a newline
  [error] copyright header missing (must start with `/-` + `Copyright`)
  [error] file at least 1500 lines (project long-file cap)
  [error] `autoImplicit true` enabled (project default is false)
  [error] `sorry` without an explanatory tag comment on the same/previous line
   [warn] module docstring (`/-!`) absent after imports
   [warn] public `theorem`/`lemma`/`def` missing docstring (`/--`)
   [warn] public theorem docstring missing a recognized paper citation
          (e.g. `[ABF26]`, `[BCIKS20]`, `[ACFY24]`, `[BCGM25]`, ...)

Run with no arguments to check the entire owned-files manifest. Use
``--no-warn`` to suppress warnings, ``--no-color`` for CI-friendly output,
and ``--files`` to override the manifest (space-separated paths).

Exit code 0 if no errors, 1 if any error finding present.

Usage:
  python3 scripts/abf26/lint.py
  python3 scripts/abf26/lint.py --no-warn
  python3 scripts/abf26/lint.py --files path/to/file.lean
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO = Path(__file__).resolve().parents[2]
MANIFEST = REPO / "scripts/abf26/owned-files.txt"
LINE_CAP_CHARS = 100
LINE_CAP_FILE = 1500
COPYRIGHT_HEAD_LINES = 10  # check for copyright in the first N lines
EXPECTED_CITATIONS = (
    # Common project bracketed-citation keys (extend freely; recognition
    # also accepts unbracketed paper-pointer phrases — see CITATION_RE).
    "[ABF26]", "[BCIKS20]", "[BCGM25]", "[ACFY24]", "[ACFY25]",
    "[ACFY24stir]", "[BCGM26]", "[GRS25]", "[BGKS19]", "[BBHR18]",
    "[GW13]", "[KSY14]", "[GKL24]", "[BCHKS25]", "[BCS16]",
    "[GG25]", "[AGL23]", "[AGL24]", "[AGGLZ25]", "[GX13]",
    "[GCXK25]", "[CS25]", "[GLMRSW22]", "[BKR06]", "[GHSZ02]",
    "[JH01]", "[CZ25]", "[DG25]", "[GK16]", "[ELI57]", "[ST20]",
    "[BDG24]", "[KK25]",
)

# Citation recognition is intentionally generous: a docstring counts as
# "cited" if it matches any of:
#   • a known bracketed citation key (the EXPECTED_CITATIONS list above)
#   • a generic `[XYZ]` or `[Xyz25]`-shaped bracketed key
#   • a paper-section pointer like `ABF26 Lemma 4.6`, `BCIKS20 §1.5`,
#     `paper's Theorem 1`, `Section 4.5 of [ABF26]`, etc.
#   • an explicit "external admit" / "Admitted as external result" marker
#   • an "ABF26-X.Y" tag (the same form the sorry-tag check recognises)
CITATION_RE = re.compile(
    r"(?:"
    r"\[[A-Z][A-Za-z0-9+]{1,15}\]"
    r"|\b(?:[A-Z]{2,}\d{2}(?:[A-Za-z]\w*)?)\s+(?:Theorem|Thm|Lemma|"
    r"Corollary|Cor|Definition|Def|Construction|Claim|Fact|Remark|"
    r"Section|§|Item|Eq\.?)"
    r"|\bpaper(?:'s)?\s+(?:Theorem|Thm|Lemma|Corollary|Cor|Definition|"
    r"Def|Construction|Claim|Fact|Remark|Section|§|Item|Eq\.?)"
    r"|\bConstruction\s+\d"
    r"|\b(?:Admitted|external)\s+(?:as|admit|proof|result)"
    r"|\bABF26[\s:\-][A-Z]?\d"
    r")",
    re.IGNORECASE,
)

# Severity strings used in output + exit-code logic.
ERR = "error"
WRN = "warn"


@dataclass
class Finding:
    severity: str
    file: Path
    line: int
    rule: str
    detail: str


def load_manifest(path: Path) -> list[Path]:
    files = []
    for raw in path.read_text().splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        p = REPO / s
        if not p.exists():
            sys.stderr.write(f"WARN: manifest entry not found on disk: {s}\n")
            continue
        files.append(p)
    return files


# ----- individual checks -----

LAMBDA_BAD = re.compile(r"\bfun\s+[^=]*?=>")
TAB = re.compile(r"\t")
TRAILING_WS = re.compile(r"[ \t]+$")
SORRY = re.compile(r"\bsorry\b")
# Accepts any of:
#   `ABF26-X.Y` / `ABF26 X.Y` / `ABF26 L4.6`           (paper item refs)
#   `external admit` / `external proof` / `tagged sorry` / `admitted`
#   `in-paper proof` / `deferred`
#   Bracketed citation keys: `[ACFY25]`, `[BCIKS20]`, etc.
SORRY_TAG = re.compile(
    r"--.*("
    r"\bABF26[\s\-:]"
    r"|\bexternal\s+(?:admit|proof)\b"
    r"|\btagged\s+sorry\b"
    r"|\badmitted\b"
    r"|\bin[-\s]paper\s+proof\b"
    r"|\bdeferred\b"
    r"|\[(?:ACFY\d*|BCIKS\d*|BCGM\d*|BCHKS\d*|BGKS\d*|GKL\d*|"
    r"GW\d+|KSY\d+|GG\d+|AGL\d*|AGGLZ\d*|GX\d+|ABF\d*)[^\]]*\]"
    r")",
    re.IGNORECASE,
)
AUTOIMPLICIT_TRUE = re.compile(r"set_option\s+autoImplicit\s+true\b")
PUBLIC_DECL = re.compile(
    r"^(?:noncomputable\s+|partial\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev)\s+(?P<name>[A-Za-z_][\w']*)"
)
# Citations are only required on "substantive" docstrings — these are
# theorem-shaped decls whose docstring has at least this many characters.
# Below this threshold we assume the decl is an internal helper / simp
# lemma and skip the citation requirement.
CITATION_DOCSTRING_MIN_CHARS = 200
PRIVATE_PREFIX = re.compile(r"^(?:@\[[^\]]*\]\s*)?private\s+")
DOCSTRING_START = re.compile(r"^\s*/--")


def check_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    raw = path.read_bytes()
    if not raw:
        findings.append(Finding(ERR, path, 1, "empty-file", "file is empty"))
        return findings
    text = raw.decode("utf-8", errors="replace")
    lines = text.splitlines()

    # File-level checks
    if len(lines) >= LINE_CAP_FILE:
        findings.append(Finding(
            ERR, path, len(lines), "file-too-long",
            f"file has {len(lines)} lines (cap: {LINE_CAP_FILE})"))
    if not text.endswith("\n"):
        findings.append(Finding(
            ERR, path, len(lines), "no-final-newline",
            "file does not end with a newline"))

    # Copyright header — must appear in the first N lines.
    head = "\n".join(lines[:COPYRIGHT_HEAD_LINES])
    if "Copyright" not in head:
        findings.append(Finding(
            ERR, path, 1, "no-copyright",
            "missing Copyright header in first 10 lines"))

    # Module docstring — `/-!` somewhere in the first ~30 lines (after imports).
    head30 = "\n".join(lines[:30])
    if "/-!" not in head30:
        findings.append(Finding(
            WRN, path, 1, "no-module-docstring",
            "no module docstring (/-! ... -/) in first 30 lines"))

    # Per-line checks
    in_block_comment = 0
    for i, line in enumerate(lines, start=1):
        # Track /- ... -/ depth coarsely. Lean's lexer handles nesting; we
        # approximate by counting opens/closes outside string literals.
        opens = line.count("/-") - line.count("/--") - line.count("/-!")
        closes = line.count("-/")
        # Crude: treat /-!  and /-- as nested comments too (they close with -/).
        opens_all = line.count("/-")
        closes_all = line.count("-/")
        net = opens_all - closes_all
        was_in_block = in_block_comment > 0
        in_block_comment = max(0, in_block_comment + net)

        if TAB.search(line):
            findings.append(Finding(ERR, path, i, "tab-char", "tab character"))
        if TRAILING_WS.search(line):
            findings.append(Finding(ERR, path, i, "trailing-ws",
                                    "trailing whitespace"))
        if len(line) > LINE_CAP_CHARS:
            findings.append(Finding(
                ERR, path, i, "line-too-long",
                f"{len(line)} chars (cap: {LINE_CAP_CHARS})"))
        # `fun ... =>` — must be `↦`. Skip inside comments/strings (best
        # effort: only flag when outside a block comment and the line has
        # no `--` line comment before the match).
        if not was_in_block:
            line_comment_at = line.find("--")
            for m in LAMBDA_BAD.finditer(line):
                if line_comment_at != -1 and m.start() >= line_comment_at:
                    continue
                findings.append(Finding(
                    ERR, path, i, "fun-arrow",
                    "`fun ... =>` lambda — use `↦`"))
        if AUTOIMPLICIT_TRUE.search(line):
            findings.append(Finding(
                ERR, path, i, "autoimplicit",
                "`set_option autoImplicit true` overrides project default"))

    # Sorry-tag check: every `sorry` must have a tag in
    #   (a) the trailing line comment on the same line, or
    #   (b) the contiguous `--` line-comment block immediately above, or
    #   (c) the `/-- ... -/` docstring immediately above the enclosing decl.
    # Track whether we're inside a `/- ... -/` block comment so we can
    # ignore `sorry`s that appear inside doc prose.
    block_depth = 0
    for i, line in enumerate(lines, start=1):
        # Coarse block-comment depth update (Lean lexer handles nesting; we
        # approximate with /- and -/ counts, not splitting on strings).
        new_depth = block_depth + line.count("/-") - line.count("-/")
        was_in_block = block_depth > 0
        block_depth = max(0, new_depth)
        if not SORRY.search(line):
            continue
        # Skip if we were already inside a block comment at line start.
        if was_in_block:
            continue
        # Skip if `sorry` only appears inside a line comment on this line.
        code_part = line.split("--", 1)[0]
        if not SORRY.search(code_part):
            continue
        # Skip if `sorry` is inside an inline /- ... -/ that opens AND closes
        # on this line before the `sorry`. (Best-effort check.)
        inline_open = code_part.rfind("/-")
        inline_close = code_part.rfind("-/")
        if inline_open != -1 and (inline_close == -1 or inline_close < inline_open):
            sorry_pos = code_part.find("sorry")
            if sorry_pos > inline_open:
                continue
        # (a) Same-line trailing `--` comment.
        same_line_comment_m = re.search(r"--.*", line)
        if same_line_comment_m and SORRY_TAG.search(same_line_comment_m.group(0)):
            continue
        # (b) Walk back through contiguous `--` lines and `/-…-/` blocks.
        j = i - 2  # zero-indexed previous line
        tagged = False
        while j >= 0:
            stripped = lines[j].lstrip()
            if stripped.startswith("--") or stripped.startswith("/-"):
                if SORRY_TAG.search(stripped):
                    tagged = True
                    break
                j -= 1
                continue
            if stripped == "":
                j -= 1
                continue
            # If the line ends a docstring, peek inside it for a tag.
            if stripped.endswith("-/"):
                k = j
                while k >= 0 and not lines[k].lstrip().startswith("/--"):
                    k -= 1
                if k >= 0:
                    block = "\n".join(lines[k:j + 1])
                    if SORRY_TAG.search(block):
                        tagged = True
                        break
                    j = k - 1
                    continue
            break
        if tagged:
            continue
        findings.append(Finding(
            ERR, path, i, "untagged-sorry",
            "`sorry` without a tagging comment (e.g., `-- ABF26-...`, "
            "`-- external admit [Citation]`, `-- tagged sorry`)"))

    # Public-declaration docstring + citation checks.
    for i, line in enumerate(lines):
        m = PUBLIC_DECL.match(line)
        if not m:
            continue
        # Skip private decls.
        if PRIVATE_PREFIX.match(line):
            continue
        decl_kind = m.group("kind")
        decl_name = m.group("name")
        # Walk backward past `@[…]` attribute lines / blank lines, looking
        # for a `/--` docstring close (`-/`) above.
        attrs = []
        j = i - 1
        while j >= 0 and (lines[j].strip().startswith("@[")
                           or lines[j].strip() == ""):
            if lines[j].strip().startswith("@["):
                attrs.append(lines[j].strip())
            j -= 1
        if j < 0 or not lines[j].rstrip().endswith("-/"):
            # Skip no-doc warning for @[simp] boundary lemmas — they're
            # self-explanatory from naming.
            if any("@[simp" in a for a in attrs):
                continue
            findings.append(Finding(
                WRN, path, i + 1, "no-doc",
                f"public `{decl_name}` has no `/--` docstring"))
            continue
        # Find the start of that docstring and check for a citation key.
        k = j
        while k >= 0 and not lines[k].lstrip().startswith("/--"):
            k -= 1
        if k < 0:
            continue
        doc = "\n".join(lines[k:j + 1])
        # Citations only required on substantive theorem docstrings — skip
        # short helpers / simp lemmas / definitions to avoid noise.
        if decl_kind != "theorem":
            continue
        if len(doc) < CITATION_DOCSTRING_MIN_CHARS:
            continue
        if not CITATION_RE.search(doc):
            findings.append(Finding(
                WRN, path, i + 1, "no-citation",
                f"public theorem `{decl_name}` has a substantive docstring "
                f"but no recognized paper citation "
                f"(bracketed `[KEY]`, `KEY25 Lemma X`, paper's Theorem X, "
                f"Admitted as external result, …)"))

    return findings


# ----- output -----

def render(findings: Iterable[Finding], *, show_warn: bool, color: bool) -> str:
    def C(code, txt):
        return f"\033[{code}m{txt}\033[0m" if color else txt
    RED = lambda s: C("31", s)
    YEL = lambda s: C("33", s)
    DIM = lambda s: C("2", s)
    by_file: dict[Path, list[Finding]] = {}
    for f in findings:
        if f.severity == WRN and not show_warn:
            continue
        by_file.setdefault(f.file, []).append(f)
    out = []
    for path, items in by_file.items():
        out.append(DIM(str(path.relative_to(REPO))))
        for f in items:
            tag = RED("error") if f.severity == ERR else YEL("warn")
            out.append(f"  {f.line:>5}  [{tag}] {f.rule:<18}  {f.detail}")
    return "\n".join(out) if out else ""


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-warn", action="store_true",
                        help="Suppress [warn] findings; only show [error].")
    parser.add_argument("--no-color", action="store_true",
                        help="Disable ANSI colors.")
    parser.add_argument("--files", nargs="+", default=None,
                        help="Override manifest with explicit file list.")
    args = parser.parse_args(argv)

    if args.files:
        paths = [REPO / f for f in args.files if (REPO / f).exists()]
    else:
        paths = load_manifest(MANIFEST)
    if not paths:
        print("ABF26 lint: no files to check.", file=sys.stderr)
        return 2

    all_findings: list[Finding] = []
    for p in paths:
        all_findings.extend(check_file(p))

    use_color = sys.stdout.isatty() and not args.no_color
    output = render(all_findings, show_warn=not args.no_warn, color=use_color)
    if output:
        print(output)

    err_count = sum(1 for f in all_findings if f.severity == ERR)
    wrn_count = sum(1 for f in all_findings if f.severity == WRN)
    print()
    print(f"ABF26 lint: {len(paths)} file(s) checked; "
          f"{err_count} error(s), {wrn_count} warning(s).")
    return 1 if err_count else 0


if __name__ == "__main__":
    sys.exit(main())
