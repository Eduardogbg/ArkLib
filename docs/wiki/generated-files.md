# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `CLAUDE.md` | compatibility symlink | No | Edit `AGENTS.md` |
| `ArkLib.lean` | generated umbrella imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `blueprint/web/`, `blueprint/print/` | generated blueprint output | No | `leanblueprint web`, `leanblueprint pdf`, or `./scripts/build-web.sh` |
| `blueprint/src/print.pdf` | generated blueprint PDF inside source tree | No | `leanblueprint pdf` |
| `home_page/docs/` | copied API docs for the site | No | `./scripts/build-web.sh` |
| `dependency_graphs/` | generated dependency visualizations | No | rerun scripts under `scripts/dependency_analysis/` |
| `docs/kb/_generated/references.json` | normalized bibliography export | No | `python3 ./scripts/kb/sync_from_bib.py` |
| `docs/kb/_generated/lean-citations.json` | generated map from Lean files to cited keys | No | `python3 ./scripts/kb/extract_lean_citations.py` |
| `docs/kb/_generated/declarations.json` | declaration catalog across `ArkLib/` (file, kind, namespace, line, brief signature, docstring head) | No | `python3 ./scripts/kb/extract_declarations.py --root ArkLib --out docs/kb/_generated/declarations.json` |
| `docs/kb/_generated/dedup-report.md` | cross-namespace declaration-similarity report (Jaccard ≥ 0.85 flags) | No | `python3 ./scripts/kb/find_dedup_candidates.py --in docs/kb/_generated/declarations.json --out docs/kb/_generated/dedup-report.md` |

## Important Notes

- `./scripts/update-lib.sh` only uses tracked `ArkLib/**/*.lean` files and now fails fast if
  untracked Lean files would be skipped.
- Generated site and blueprint output are for review and deployment, not authoring.
- If a path looks derived, confirm its source of truth before editing it.
