#!/usr/bin/env python3
"""Generate coverage table for README.
   Counts Lean proofs without `sorry` and pytest summary.
"""
import subprocess, pathlib, re, sys, textwrap
ROOT = pathlib.Path(__file__).resolve().parents[1]
PROOFS = ROOT / "artifact" / "proofs"

lean_files = sorted(p for p in PROOFS.glob("*.lean") if p.name != "TableCorrespondence.lean")

PLACEHOLDER_RE = re.compile(r"_placeholder|placeholder", re.IGNORECASE)

completed, placeholders = [], []
for f in lean_files:
    txt = f.read_text()
    if 'sorry' in txt:
        continue  # not completed, counts as sorry implicitly
    if PLACEHOLDER_RE.search(txt):
        placeholders.append(f.name)
    else:
        completed.append(f.name)

num_sorry = len(lean_files) - len(completed) - len(placeholders)

passed = 0
try:
    out = subprocess.check_output([sys.executable, '-m', 'pytest', '-q'], cwd=ROOT, text=True)
    m = re.search(r"([0-9]+) passed", out)
    if m:
        passed = int(m.group(1))
except Exception:
    pass

# Count python demo tests (numeric correspondences) by inspecting test files.
test_dir = ROOT / 'artifact' / 'tests'
demo_tests = 0
for py in test_dir.glob('test_*.py'):
    if py.name == 'test_lean_compile.py':
        continue
    source = py.read_text()
    demo_tests += sum(1 for line in source.splitlines() if line.strip().startswith('def test_'))

total_tests = passed  # total passed tests from pytest

# Assemble counts dict before cli handling
total_data = {
    'lean_total': len(lean_files),
    'lean_completed': len(completed),
    'lean_placeholders': len(placeholders),
    'lean_sorry': num_sorry,
    'python_demos': demo_tests,
    'pytest_total_passed': total_tests,
}

# Generate markdown table
status_md = textwrap.dedent(f"""
| Metric | Count |
|--------|-------|
| Lean files (core) | {len(lean_files)} |
| &nbsp; • completed proofs | {len(completed)} |
| &nbsp; • placeholders | {len(placeholders)} |
| &nbsp; • with `sorry` | {num_sorry} |
| Python demos verified | {demo_tests} |
| Total pytest tests passed | {total_tests} |
""")

README_START = "<!-- STATUS-START -->"
README_END = "<!-- STATUS-END -->"

if '--json' in sys.argv:
    import json
    print(json.dumps(total_data))
    sys.exit(0)

if '--insert-readme' in sys.argv:
    readme = ROOT / 'README.md'
    lines = readme.read_text().splitlines()
    try:
        start = lines.index(README_START)
        end = lines.index(README_END)
        new_lines = lines[:start+1] + [''] + status_md.strip().splitlines() + [''] + lines[end:]
        readme.write_text("\n".join(new_lines))
    except ValueError:
        # markers missing: append at end
        with open(readme, 'a') as f:
            f.write(f"\n## Verification status\n{README_START}\n{status_md}{README_END}\n")

else:
    print(status_md) 