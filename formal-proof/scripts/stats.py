#!/usr/bin/env python3
"""Development statistics with Coq comments stripped (nested (* *) aware)."""
import re, sys, glob, os
def strip(src):
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith("(*", i): depth += 1; i += 2; continue
        if src.startswith("*)", i) and depth: depth -= 1; i += 2; continue
        if not depth: out.append(src[i])
        i += 1
    return "".join(out)
files = sorted(glob.glob("src/**/*.v", recursive=True))
raw = {f: open(f).read() for f in files}
code = {f: strip(v) for f, v in raw.items()}
allc = "\n".join(code.values())
lines = sum(len(v.splitlines()) for v in raw.values())
def cnt(pat, anchored=False):
    p = (r"(?m)^[ \t]*(?:" + pat + r")\b") if anchored else (r"\b(?:" + pat + r")\b")
    return len(re.findall(p, allc))
print(f"files                         {len(files)}")
print(f"lines (raw, incl. comments)   {lines}")
print(f"Definitions                   {cnt('Definition', True)}")
print(f"Lemma/Theorem/Corollary       {cnt('Lemma|Theorem|Corollary', True)}")
print(f"Proof. markers                {len(re.findall(r'(?m)^[ \t]*Proof[ \t]*\.', allc))}")
print(f"Qed. markers                  {len(re.findall(r'(?m)^[ \t]*Qed[ \t]*\.', allc))}")
print(f"destruct                      {cnt('destruct')}")
print(f"induction                     {cnt('induction')}")
print(f"auto/eauto/lia/tauto/congr    {cnt('auto|eauto|lia|tauto|congruence')}")
print(f"firstorder/intuition          {cnt('firstorder|intuition')}")
