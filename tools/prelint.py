#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
import tomllib
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = ROOT / "ExactReductionLimits"
UMBRELLA = ROOT / "ExactReductionLimits.lean"

errors: list[str] = []

# TOML parses and globs enumerate the local modules.
try:
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
except Exception as exc:
    errors.append(f"lakefile.toml does not parse: {exc}")
    lake = {}

globs: set[str] = set()
for lib in lake.get("lean_lib", []):
    if lib.get("name") == "ExactReductionLimits":
        globs.update(lib.get("globs", []))

lean_files = sorted([UMBRELLA, *LIB.rglob("*.lean")])
module_of: dict[Path, str] = {}
path_of: dict[str, Path] = {}
for p in lean_files:
    if p == UMBRELLA:
        mod = "ExactReductionLimits"
    else:
        rel = p.relative_to(ROOT).with_suffix("")
        mod = ".".join(rel.parts)
    module_of[p] = mod
    path_of[mod] = p

expected_globs = set(path_of)
if globs != expected_globs:
    missing = sorted(expected_globs - globs)
    extra = sorted(globs - expected_globs)
    if missing:
        errors.append("Lake globs missing: " + ", ".join(missing))
    if extra:
        errors.append("Lake globs contain unknown modules: " + ", ".join(extra))

# Imports resolve and no forbidden proof escape hatches occur.
import_re = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)
# Match declarations, not prose in comments.
forbidden_re = re.compile(r"^\s*(sorry|admit|axiom)\b", re.M)
graph: dict[str, set[str]] = defaultdict(set)
for p in lean_files:
    text = p.read_text()
    if forbidden_re.search(text):
        errors.append(f"forbidden proof escape hatch in {p.relative_to(ROOT)}")
    mod = module_of[p]
    for imp in import_re.findall(text):
        if imp.startswith("ExactReductionLimits"):
            if imp not in path_of:
                errors.append(f"unresolved local import {imp} in {p.relative_to(ROOT)}")
            else:
                graph[mod].add(imp)

# Detect local import cycles.
WHITE, GRAY, BLACK = 0, 1, 2
state = {m: WHITE for m in path_of}
stack: list[str] = []

def dfs(m: str) -> None:
    state[m] = GRAY
    stack.append(m)
    for n in graph[m]:
        if state[n] == WHITE:
            dfs(n)
        elif state[n] == GRAY:
            i = stack.index(n)
            errors.append("import cycle: " + " -> ".join(stack[i:] + [n]))
    stack.pop()
    state[m] = BLACK

for m in path_of:
    if state[m] == WHITE:
        dfs(m)

# Every local source module must be reachable from the umbrella.
reachable: set[str] = set()
q = deque(["ExactReductionLimits"])
while q:
    m = q.popleft()
    if m in reachable:
        continue
    reachable.add(m)
    q.extend(graph[m])

unreachable = sorted(set(path_of) - reachable)
if unreachable:
    errors.append("modules unreachable from umbrella: " + ", ".join(unreachable))

if errors:
    print("PRELINT: FAIL")
    for e in errors:
        print("-", e)
    sys.exit(1)

print("PRELINT: PASS")
print(f"- {len(lean_files)} Lean files")
print("- every local import resolves")
print("- local import graph is acyclic")
print("- all local modules are umbrella-reachable")
print("- Lake globs match the source tree")
print("- no sorry/admit/axiom declaration")
