#!/usr/bin/env python3
"""Generate coverage table for README.
   Counts Lean proofs without `sorry` and pytest summary.
"""
import subprocess, pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PROOFS = ROOT / "artifact" / "proofs"

lean_files = sorted(p for p in PROOFS.glob("*.lean") if p.name != "TableCorrespondence.lean")

no_sorry = []
for f in lean_files:
    if 'sorry' not in f.read_text():
        no_sorry.append(f.name)

passed = 0
try:
    out = subprocess.check_output([sys.executable, '-m', 'pytest', '-q'], cwd=ROOT, text=True)
    m = re.search(r"([0-9]+) passed", out)
    if m:
        passed = int(m.group(1))
except Exception:
    pass

print("## Auto-generated status\n")
print(f"Lean proofs closed: {len(no_sorry)}/{len(lean_files)}")
print(f"Python demos passed: {passed}") 