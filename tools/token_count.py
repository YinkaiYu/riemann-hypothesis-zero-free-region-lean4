#!/usr/bin/env python3
"""Approximate the official anti-code-golf normalized token count.

Official rules: comments, whitespace and `import` lines are stripped; identifier
length is ignored. This counters tokens with a Lean-ish lexer over the stripped
source. Reported: tokens (regex-lexer), chars, bytes.
"""
import re
import sys
from pathlib import Path

LEXER = re.compile(r"[\w']+|[!#$%&*+./:<=>?@^|~\-]+|[^\w\s]", re.U)
BLOCK = re.compile(r"/\-[\s\S]*?\-/")
LINE_COMMENT = re.compile(r"--[^\n]*")
IMPORT = re.compile(r"(?m)^\s*import[^\n]*")


def clean(s: str) -> str:
    s = BLOCK.sub(" ", s)
    s = LINE_COMMENT.sub("", s)
    return IMPORT.sub("", s)


def tokens(s: str) -> int:
    return len(LEXER.findall(clean(s)))


def report(path: Path) -> dict:
    raw = path.read_text(encoding="utf-8-sig")
    stripped = clean(raw)
    return {
        "file": str(path),
        "tokens": tokens(raw),
        "chars": len(stripped),
        "raw_chars": len(raw),
        "lines": raw.count("\n") + 1,
    }


if __name__ == "__main__":
    paths = [Path(p) for p in sys.argv[1:]]
    total = 0
    for p in paths:
        if p.is_dir():
            files = sorted(p.rglob("*.lean"))
        else:
            files = [p]
        for f in files:
            r = report(f)
            total += r["tokens"]
            print(f"{r['tokens']:7d} tok  {r['chars']:7d} chars(stripped)  {r['lines']:5d} lines  {f}")
    if len(paths) > 1 or (paths and paths[0].is_dir()):
        print(f"TOTAL tokens = {total}")
