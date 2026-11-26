"""Fail if a Lean file under WideTrail/ is not reachable from WideTrail.lean.

`lake build` builds only the modules that the default target imports, and
`scripts/AuditAxioms.lean` audits only those modules. A file that nothing
imports is therefore neither compiled nor audited, and nothing reports it.
This script lists every such file.

Usage: python3 scripts/check_imports.py   (from the repository root)
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*import\s+(WideTrail(?:\.[A-Za-z0-9_]+)*)\s*$")


def module_path(module: str) -> pathlib.Path:
    return ROOT.joinpath(*module.split(".")).with_suffix(".lean")


def imports(path: pathlib.Path) -> list[str]:
    found = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if match:
            found.append(match.group(1))
    return found


def main() -> int:
    every = {"WideTrail"} | {
        ".".join(p.relative_to(ROOT).with_suffix("").parts)
        for p in (ROOT / "WideTrail").rglob("*.lean")
    }
    reached = set()
    pending = ["WideTrail"]
    missing_targets = []
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        path = module_path(module)
        if not path.exists():
            missing_targets.append(module)
            continue
        pending.extend(imports(path))

    orphans = sorted(every - reached)
    for module in missing_targets:
        print(f"imported but missing: {module}")
    for module in orphans:
        print(f"not imported by WideTrail: {module} ({module_path(module).relative_to(ROOT)})")
    if orphans or missing_targets:
        return 1
    print(f"All {len(every)} modules are reachable from WideTrail.lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
