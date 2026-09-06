#!/usr/bin/env python3
"""Fast Lean proof checker for this repo.

Sends Lean files (or code on stdin) to the local Kimina Lean server, which keeps
a warm REPL with `import Mathlib` already loaded, so checks take ~1s instead of
the ~3 minutes a cold `lake env lean` run takes.

Usage:
    python3 scripts/check.py Conjectures/Foo.lean [Conjectures/Bar.lean ...]
    echo 'import Mathlib\ntheorem t : 1+1=2 := rfl' | python3 scripts/check.py -
    python3 scripts/check.py --timeout 600 Conjectures/Foo.lean

Exit code 0 iff every file checks with no errors and no sorries.
"""

import argparse
import json
import pathlib
import sys
import urllib.request

SERVER = "http://127.0.0.1:7071/api/check"


def check(snippets: list[dict], timeout: int) -> dict:
    body = json.dumps(
        {"snippets": snippets, "timeout": timeout, "reuse": True}
    ).encode()
    req = urllib.request.Request(
        SERVER, data=body, headers={"Content-Type": "application/json"}
    )
    with urllib.request.urlopen(req, timeout=timeout + 30) as r:
        return json.load(r)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+", help=".lean files, or '-' for stdin")
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()

    snippets = []
    for f in args.files:
        if f == "-":
            snippets.append({"id": "<stdin>", "code": sys.stdin.read()})
        else:
            snippets.append({"id": f, "code": pathlib.Path(f).read_text()})

    try:
        resp = check(snippets, args.timeout)
    except Exception as e:
        print(f"FATAL: cannot reach Kimina server at {SERVER}: {e}", file=sys.stderr)
        print(
            "Start it with: cd ~/kimina-lean-server && python -m server",
            file=sys.stderr,
        )
        return 2

    ok = True
    for res in resp["results"]:
        rid = res["id"]
        if res.get("error"):
            ok = False
            print(f"✗ {rid}: server error: {res['error']}")
            continue
        r = res.get("response") or {}
        msgs = r.get("messages", [])
        errors = [m for m in msgs if m.get("severity") == "error"]
        sorries = r.get("sorries", [])
        t = res.get("time", 0)
        if errors:
            ok = False
            print(f"✗ {rid} ({t:.1f}s): {len(errors)} error(s)")
        elif sorries:
            ok = False
            print(f"⚠ {rid} ({t:.1f}s): contains {len(sorries)} sorry(ies)")
        else:
            print(f"✓ {rid} ({t:.1f}s): OK")
        for m in msgs:
            pos = m.get("pos") or {}
            print(
                f"  [{m.get('severity')}] line {pos.get('line')}, col {pos.get('column')}: "
                + str(m.get("data", "")).strip()
            )
        for s in sorries:
            pos = s.get("pos") or {}
            print(f"  [sorry] line {pos.get('line')}: goal: {s.get('goal', '')}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
