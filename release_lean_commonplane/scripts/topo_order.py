#!/usr/bin/env python3
"""Topological import order of the NPT modules needed by the given roots.

usage: topo_order.py PROJECT_DIR ROOT_MODULE...

Reads the `import NPT...` lines at the top of each `NPT/....lean` file under PROJECT_DIR (block comments
and line comments are skipped; the import block ends at the first other command) and prints every module
reachable from the roots, dependencies first, one per line. Exits with status 1 on a missing module file
or an import cycle.
"""
import os
import re
import sys

IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.']+)\s*$")


def strip_comments(text):
    """Remove (nested) block comments and line comments."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def imports_of(path):
    with open(path, encoding="utf-8") as fh:
        text = strip_comments(fh.read())
    mods = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        m = IMPORT_RE.match(line)
        if m is None:
            break  # end of the import block
        mods.append(m.group(1))
    return [m for m in mods if m == "NPT" or m.startswith("NPT.")]


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    root_dir, roots = sys.argv[1], sys.argv[2:]
    order, state = [], {}  # state: 1 = on stack, 2 = done

    def visit(mod, chain):
        if state.get(mod) == 2:
            return
        if state.get(mod) == 1:
            sys.exit("import cycle: " + " -> ".join(chain + [mod]))
        path = os.path.join(root_dir, *mod.split(".")) + ".lean"
        if not os.path.isfile(path):
            sys.exit("missing module file for %s (imported via %s)" % (mod, " -> ".join(chain) or "roots"))
        state[mod] = 1
        for dep in imports_of(path):
            visit(dep, chain + [mod])
        state[mod] = 2
        order.append(mod)

    for r in roots:
        visit(r, [])
    print("\n".join(order))


if __name__ == "__main__":
    main()
