"""Fail if a Lean file under WideTrail/ is not reachable from a library root.

The roots are `WideTrail.lean` (the default library) and `WideTrailHeavy.lean`
(the memory-heavy checks). `lake build` builds only the modules a root imports, and
the axiom audits cover only those modules. A file that nothing imports is
therefore neither compiled nor audited, and nothing reports it. This script lists
every such file.

Usage: python3 scripts/check_imports.py   (from the repository root)
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*import\s+(WideTrail(?:Heavy)?(?:\.[A-Za-z0-9_]+)*)\s*$")
ROOTS = ["WideTrail", "WideTrailHeavy"]


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
    every = set(ROOTS) | {
        ".".join(p.relative_to(ROOT).with_suffix("").parts)
        for p in (ROOT / "WideTrail").rglob("*.lean")
    }
    reached = set()
    pending = list(ROOTS)
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
        print(f"not imported by any library root: {module} ({module_path(module).relative_to(ROOT)})")
    if orphans or missing_targets:
        return 1
    print(f"All {len(every)} modules are reachable from WideTrail.lean or WideTrailHeavy.lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
