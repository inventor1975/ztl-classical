#!/usr/bin/env python3
"""Compare the edge lists in the Lean statements with kscert's unresolved.json.

Usage: python3 KS23/scripts/check_edges.py PATH/TO/kscert/unresolved.json

For each KS23/G*/Main.lean: reads the sha256 in its docstring and the literal `Realization n [...]` edge list,
finds the entry with that sha256 in unresolved.json, and checks: same order n, the same edge list (same pairs,
same order), no duplicate edges, no loops, every vertex in 1..n. Prints OK or the first mismatch per graph.
"""
import ast, glob, json, os, re, sys

def main(path):
    entries = {e["sha256"]: e for e in json.load(open(path))["entries"]}
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    bad = 0
    for main_lean in sorted(glob.glob(os.path.join(here, "G*", "Main.lean"))):
        s = open(main_lean).read()
        sha = re.search(r"`([0-9a-f]{64})`", s).group(1)
        m = re.search(r"Realization (\d+) (\[.*?\]) → False", s, re.S)
        n, E = int(m.group(1)), ast.literal_eval(m.group(2).replace("(", "[").replace(")", "]"))
        ref = entries.get(sha)
        name = os.path.basename(os.path.dirname(main_lean))
        problems = []
        if ref is None: problems.append("sha256 not in unresolved.json")
        else:
            if n != int(ref["order"]): problems.append("order differs")
            if E != [list(e) for e in ref["edges"]]: problems.append("edge list differs")
        if len(E) != len({tuple(sorted(e)) for e in E}): problems.append("duplicate edge")
        if any(a == b for a, b in E): problems.append("loop")
        if any(not (1 <= a <= n and 1 <= b <= n) for a, b in E): problems.append("vertex out of range")
        print(name, sha[:12], len(E), "edges:", "OK" if not problems else "; ".join(problems))
        bad += bool(problems)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main(sys.argv[1])
