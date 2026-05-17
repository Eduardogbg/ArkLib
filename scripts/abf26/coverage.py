#!/usr/bin/env python3
"""ABF26 coverage report.

Verifies that the paper-to-Lean map in
``docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md``
still matches the codebase.

Reads each table row (8 status tables, ~52 content rows total), extracts
the cited Lean symbol-and-file references, and checks:

  * the file exists at the cited path,
  * the symbol is declared (``theorem``/``lemma``/``def``/``abbrev``),
  * whether the declaration body contains ``sorry``.

For each row, prints a verdict glyph:

  ✓ present — symbol(s) declared, no sorry in body
  ◐ stub    — symbol(s) declared but body contains sorry
  ✗ missing — declared symbol(s) not found at cited path
  ⚠ drift   — status says ``missing`` but a Lean ref now exists, or status
              says ``present`` but body has sorry

Exit code 0 if no drift; 1 if any drift detected. Use ``--strict`` to also
fail on ``◐ stub`` rows that are not tagged ``present-but-incomplete`` or
``deferred``.

Usage:
    python3 scripts/abf26/coverage.py [--strict]
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
AUDIT_DOC = REPO / "docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md"

# A content row: starts with `| ` + 5 inner `|` separators + trailing `|`.
# We don't try to be too clever — split on `|` and trim cells.
HEADER_KEYS = ("ABF26 ID", "Paper item", "Status")
SEP_RE = re.compile(r"^\|\s*-+\s*\|")

# Status values the audit doc commits to (see legend at top).
KNOWN_STATUSES = {
    "present",
    "present-but-different",
    "present-but-incomplete",
    "missing",
    "deferred",
    # Parenthetical variants used in a few rows.
    "present (as predicate)",
    "missing (deferred — needs uniform-subset distribution)",
}

# Markdown-cell sentinel: escapes `\|` inside math (used for `|F|` etc.)
PIPE_SENTINEL = "\x00"

# A backticked Lean-symbol-looking token: starts with a letter/underscore,
# may contain `.`, `_`, digits, primes. (Rejects bare math like `δ`.)
SYMBOL_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")

# A `.lean` file link in the cell.
LEAN_FILE_RE = re.compile(r"\[[^\]]+\]\(([^)]+\.lean)\)")

# Tokens to ignore even if they match SYMBOL_RE — these are Lean keywords
# / generic prose words that the audit doc backticks for readability.
SYMBOL_BLACKLIST = frozenset({
    "sorry", "True", "False", "Prop", "Type", "Set", "Sort",
    "by", "let", "have", "fun", "show", "if", "then", "else", "rfl",
    "theorem", "lemma", "def", "abbrev", "noncomputable",
    "match", "with", "and", "or", "not",
    "existing", "missing", "deferred",
    # Mathlib-namespaced symbols we don't expect to find in our paths.
    "Set.Finite.toFinset", "Set.Finite", "Set.Infinite",
    "Mathlib", "Std",
})

# Prefixes of file paths we treat as "ours" — symbols cited but living
# outside these paths are silently skipped (they're Mathlib/lib refs).
OUR_PATH_PREFIXES = ("ArkLib/",)

# Declaration kinds we recognise in Lean source.
DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive",
    "instance", "class", "noncomputable def", "noncomputable abbrev",
)
DECL_RE_TEMPLATE = (
    r"\b(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
    r"(?:[A-Za-z_][\w.]*\.)?{sym}(?![A-Za-z0-9_'])"
)


class Row:
    __slots__ = ("id", "paper_item", "status", "lean_refs_cell",
                 "lean_target", "notes", "lineno")

    def __init__(self, parts, lineno):
        # parts is list of cells; row is `| a | b | c | d | e | f |` so we
        # drop the leading/trailing empty strings.
        cells = [c.strip() for c in parts]
        if cells and cells[0] == "":
            cells = cells[1:]
        if cells and cells[-1] == "":
            cells = cells[:-1]
        if len(cells) < 6:
            # 4-column legacy rows (e.g., earlier-format) — pad.
            cells = cells + [""] * (6 - len(cells))
        self.id = cells[0].strip("`")
        self.paper_item = cells[1]
        self.status = cells[2]
        self.lean_refs_cell = cells[3]
        self.lean_target = cells[4]
        self.notes = cells[5]
        self.lineno = lineno

    @property
    def status_core(self) -> str:
        """Normalise the status field for comparison."""
        s = self.status.strip()
        for known in ("present-but-incomplete", "present-but-different",
                      "present", "missing", "deferred"):
            if s.startswith(known):
                return known
        return s


def parse_audit_table(path: Path):
    rows = []
    in_table = False
    for lineno, raw in enumerate(path.read_text().splitlines(), start=1):
        line = raw.rstrip()
        if not line.startswith("|"):
            in_table = False
            continue
        if any(key in line for key in HEADER_KEYS):
            in_table = True
            continue
        if SEP_RE.match(line):
            continue
        if not in_table:
            continue
        # Preserve escaped pipes (used as `\|` for math like `|F|`).
        cooked = line.replace(r"\|", PIPE_SENTINEL)
        parts = cooked.split("|")
        parts = [p.replace(PIPE_SENTINEL, "|") for p in parts]
        row = Row(parts, lineno)
        rows.append(row)
    return rows


def parse_lean_refs(*cells: str):
    """Extract `(symbol, file_path)` pairs from one or more table cells.

    Strategy: collect every backticked Lean-looking symbol and every
    `.lean` file link. The set of references is the cross-product
    `symbols × files`. If a row's references span both the `Lean refs`
    and `Lean target` columns (one has the file link, the other has the
    symbol), this still pairs them correctly.
    """
    text = " ".join(cells)
    symbols = SYMBOL_RE.findall(text)
    files = LEAN_FILE_RE.findall(text)
    if not symbols or not files:
        return []
    # Drop duplicates while preserving order.
    seen_sym = []
    for s in symbols:
        if s not in seen_sym:
            seen_sym.append(s)
    seen_file = []
    for f in files:
        if f not in seen_file:
            seen_file.append(f)
    return [(s, f) for s in seen_sym for f in seen_file]


def resolve_link(link: str) -> Path:
    p = link
    while p.startswith("../"):
        p = p[3:]
    p = p.lstrip("/")
    return REPO / p


def find_decl_block(text: str, short_sym: str):
    """Find the declaration of ``short_sym`` and return its body slice.

    Returns ``(found, body)`` where ``body`` is everything from the matched
    line until the next top-level declaration or blank-line gap. ``found``
    is ``False`` if no declaration was located.
    """
    decl_re = re.compile(DECL_RE_TEMPLATE.format(sym=re.escape(short_sym)))
    next_decl_re = re.compile(
        r"^(?:@\[[^\]]*\]\s*)?"
        r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|"
        r"section|end|namespace|open)\b"
    )
    lines = text.splitlines()
    n = len(lines)
    for i, line in enumerate(lines):
        if decl_re.search(line):
            j = i + 1
            while j < n:
                stripped = lines[j].strip()
                if stripped == "":
                    # Blank line: break if the *next* line opens a new
                    # decl (or its docstring).
                    if j + 1 < n:
                        nxt = lines[j + 1].lstrip()
                        if next_decl_re.match(nxt) or nxt.startswith("/--"):
                            break
                if next_decl_re.match(lines[j]):
                    break
                # Also break on the start of a `/--` docstring — that's
                # the next decl's documentation, not this decl's body.
                if lines[j].lstrip().startswith("/--"):
                    break
                j += 1
            return True, "\n".join(lines[i:j])
    return False, ""


def short_name(sym: str) -> str:
    return sym.split(".")[-1]


def verify_row(row: Row):
    """Returns dict with verdict info.

    Source-column semantics in the audit doc:
      * ``lean_refs`` lists declarations that *currently exist* in ArkLib.
      * ``lean_target`` is the *canonical post-implementation name*. For
        ``present`` rows this is the existing name; for ``*-different`` /
        ``*-incomplete`` / ``deferred`` / ``missing`` rows it may name
        symbols that don't exist yet.

    Some rows put the existing decl name *only* in ``lean_target`` (with
    the file link alone in ``lean_refs``). We extract symbols from both
    columns and tag them by source so the verdict logic can apply the
    right strictness per status.
    """
    # Strip parentheticals that describe paper notation rather than Lean
    # declarations: `(= paper `X`)`, `(paper's `X`)`, `(which matches paper `X`)`,
    # `(see [...] `X`)`, `(known as `X` in [PaperKey])`.
    paper_ctx = re.compile(
        r"\([^)]*\b(?:paper|spec|notation|alias for|aka|known as|denoted|see\s+\[)"
        r"[^)]*\)",
        flags=re.IGNORECASE,
    )
    refs_text = paper_ctx.sub("", row.lean_refs_cell)
    target_text = paper_ctx.sub("", row.lean_target)
    refs_syms = []
    for s in SYMBOL_RE.findall(refs_text):
        if s in SYMBOL_BLACKLIST:
            continue
        if s not in refs_syms:
            refs_syms.append(s)
    target_syms = []
    for s in SYMBOL_RE.findall(target_text):
        if s in SYMBOL_BLACKLIST:
            continue
        if s not in target_syms and s not in refs_syms:
            target_syms.append(s)
    # Symbols treated as required (must exist): always lean_refs; plus
    # lean_target when status is `present` (since for that status the
    # canonical name IS the existing decl).
    symbols = list(refs_syms)
    if row.status_core == "present":
        symbols.extend(target_syms)
    files = []
    for f in LEAN_FILE_RE.findall(refs_text + " " + target_text):
        if f not in files:
            files.append(f)
    if not symbols or not files:
        return {
            "verdict": "—",
            "detail": "(no parsable Lean ref)",
            "refs_total": 0,
            "refs_present": 0,
            "refs_stub": 0,
            "refs_missing": [],
        }
    # Read each file once.
    file_text = {}
    for f in files:
        path = resolve_link(f)
        if not path.exists():
            file_text[f] = None
        else:
            try:
                file_text[f] = path.read_text()
            except UnicodeDecodeError:
                file_text[f] = None
    present = 0
    stub = 0
    missing = []
    for sym in symbols:
        short = short_name(sym)
        # Search every file in the row for this symbol.
        found_here = False
        has_sorry_here = False
        for f in files:
            txt = file_text.get(f)
            if txt is None:
                continue
            ok, body = find_decl_block(txt, short)
            if ok:
                found_here = True
                if re.search(r"\bsorry\b", body):
                    has_sorry_here = True
                break  # first match wins
        if not found_here:
            missing.append(f"{sym}")
            continue
        if has_sorry_here:
            stub += 1
        else:
            present += 1

    # Verdict logic
    status_core = row.status_core
    n = len(symbols)
    if missing:
        verdict = "✗"
    elif stub and not present:
        verdict = "◐"
    elif stub and present:
        verdict = "◐"  # mixed: at least one sorry
    else:
        verdict = "✓"

    # Drift checks
    drift_reasons = []
    if status_core == "missing" and (present or stub):
        drift_reasons.append("doc says missing but symbol now exists")
    if status_core == "present" and stub:
        drift_reasons.append("doc says present but body has sorry")
    if status_core == "present" and missing:
        drift_reasons.append("doc says present but symbol not found")
    if status_core == "present-but-incomplete" and not (stub or missing):
        drift_reasons.append("doc says incomplete but body has no sorry; consider re-tagging present")
    if drift_reasons:
        verdict = "⚠"

    return {
        "verdict": verdict,
        "detail": "; ".join(drift_reasons) if drift_reasons else "",
        "refs_total": n,
        "refs_present": present,
        "refs_stub": stub,
        "refs_missing": missing,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true",
                        help="Fail if any row is ◐ stub outside of "
                             "present-but-incomplete/deferred status.")
    parser.add_argument("--no-color", action="store_true",
                        help="Disable ANSI colors in output.")
    args = parser.parse_args(argv)

    if not AUDIT_DOC.exists():
        print(f"ERROR: audit doc not found at {AUDIT_DOC}", file=sys.stderr)
        return 2

    use_color = sys.stdout.isatty() and not args.no_color
    def C(code, txt):
        return f"\033[{code}m{txt}\033[0m" if use_color else txt
    GREEN = lambda s: C("32", s)
    YEL = lambda s: C("33", s)
    RED = lambda s: C("31", s)
    DIM = lambda s: C("2", s)

    rows = parse_audit_table(AUDIT_DOC)
    if not rows:
        print(f"ERROR: no table rows parsed from {AUDIT_DOC}", file=sys.stderr)
        return 2

    counts = defaultdict(int)
    drift_rows = []
    stub_rows = []
    out_lines = []
    for row in rows:
        result = verify_row(row)
        counts[result["verdict"]] += 1
        counts[f"status:{row.status_core}"] += 1
        glyph = result["verdict"]
        color = {"✓": GREEN, "◐": YEL, "✗": RED, "⚠": RED, "—": DIM}.get(glyph, DIM)
        out_lines.append(
            f"{color(glyph)} {row.id:<8} {row.status_core:<24} "
            f"refs ok/stub/miss={result['refs_present']}/{result['refs_stub']}/"
            f"{len(result['refs_missing'])}"
            + (f"  {DIM('— ' + result['detail'])}" if result["detail"] else "")
        )
        if glyph == "⚠":
            drift_rows.append((row, result))
        if glyph == "◐":
            stub_rows.append((row, result))

    print("\n".join(out_lines))
    print()
    print(f"  ✓ present:  {counts['✓']}")
    print(f"  ◐ stub:     {counts['◐']}")
    print(f"  ✗ missing:  {counts['✗']}")
    print(f"  ⚠ drift:    {counts['⚠']}")
    print(f"  — n/a:      {counts['—']}")
    print(f"  total rows: {len(rows)}")
    print()
    print("Status distribution (per audit doc):")
    for k in ("present", "present-but-different", "present-but-incomplete",
              "missing", "deferred"):
        print(f"  {k:<24}  {counts.get(f'status:{k}', 0)}")

    missing_rows = [(row, res) for row, res in
                    zip(rows, (verify_row(r) for r in rows))
                    if res["verdict"] == "✗"]

    if drift_rows:
        print()
        print(RED("Drift detected:"))
        for row, res in drift_rows:
            print(f"  {row.id}  ({AUDIT_DOC.name}:{row.lineno})  — {res['detail']}")
            for miss in res["refs_missing"]:
                print(f"    · {miss}")

    if missing_rows:
        print()
        print(RED("Missing symbols (cited in `Lean refs` but not declared):"))
        for row, res in missing_rows:
            print(f"  {row.id}  ({AUDIT_DOC.name}:{row.lineno})")
            for miss in res["refs_missing"]:
                print(f"    · {miss}")

    if drift_rows or missing_rows:
        return 1
    if args.strict:
        # Strict: ◐ stubs are tolerated only if the row's status is one of
        # {present-but-incomplete, deferred} or a "stated (external admit*)"
        # variant (paper-cited result with an intentional placeholder).
        def stub_ok(row):
            s = row.status.lower()
            return (row.status_core in ("present-but-incomplete", "deferred")
                    or "external admit" in s or "external proof" in s)
        bad = [row for row, _ in stub_rows if not stub_ok(row)]
        if bad:
            print()
            print(YEL("Strict mode: stub rows with non-stub status:"))
            for row in bad:
                print(f"  {row.id} ({row.status})")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
