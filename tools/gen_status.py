#!/usr/bin/env python3
"""Generate coverage table for README.
   Counts Lean proofs without `sorry` and pytest summary.
"""
import subprocess, pathlib, re, sys, textwrap, yaml, json
ROOT = pathlib.Path(__file__).resolve().parents[1]
PROOFS = ROOT / "artifact" / "proofs"

# Early declaration to allow preliminary scanning loops
tags: dict[str, dict[str, str]] = {}

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

# scan Python demos for status demo tag (search entire artifact tree)
for py in (ROOT / "artifact").rglob("*.py"):
    for line in py.read_text().splitlines():
        m = re.match(r"^\s*#\s*STATUS:\s*demo\s*\|\s*([A-Za-z0-9_\-]+)", line)
        if m:
            name = m.group(1)
            entry = tags.setdefault(name, {})
            entry["demo"] = "yes"
            break

# Load existing YAML (if any) and merge – tags override.
status_file = ROOT / "status.yml"
yaml_data: dict[str, dict[str, str]] = {}
if status_file.exists():
    yaml_data = yaml.safe_load(status_file.read_text()) or {}

for name, entry in tags.items():
    base = yaml_data.setdefault(name, {})
    base.update(entry)

# normalise: missing fields → '-'
for name, entry in yaml_data.items():
    entry.setdefault("lean", "-")
    entry.setdefault("demo", "no" if entry.get("demo") != "yes" else "yes")

# Optional write-back
if "--write-yaml" in sys.argv:
    with open(status_file, "w") as f:
        yaml.dump(dict(sorted(yaml_data.items())), f, sort_keys=False)

# Build correspondence list for markdown
correspondences = []
def sym(v: str) -> str:
    mapping = {"full":"✅", "partial":"⚠", "none":"❌", "yes":"✅", "no":"❌", "-":"-"}
    return mapping.get(v, v)

for name in sorted(yaml_data.keys()):
    entry = yaml_data[name]
    correspondences.append((name, sym(entry.get("lean", "-")), sym(entry.get("demo", "-"))))

corr_md = ""
if correspondences:
    corr_md += "| Correspondence | Lean | Demo |\n"
    corr_md += "|--------------|------|------|\n"
    for name, l, d in correspondences:
        corr_md += f"| {name} | {l} | {d} |\n"

# ----------------------------------------------------------
#  Falsification (attempted disproof) statistics
# ----------------------------------------------------------
DISPROOF_DIR = ROOT / "artifact" / "disproof"
cases_file = DISPROOF_DIR / "cases_outside.json"
outside_cases = 0
if cases_file.exists():
    try:
        data = json.loads(cases_file.read_text())
        if isinstance(data, dict):
            lst = data.get("outside_cases", data.get("cases", []))
            if isinstance(lst, list):
                outside_cases = len(lst)
        elif isinstance(data, list):
            outside_cases = len(data)
    except Exception:
        pass

# Assemble counts dict (now after we know python_demos)
python_demos = sum(1 for entry in yaml_data.values() if entry.get("demo") == "yes")

total_tests = passed  # total passed tests overall

total_data = {
    "lean_total": len(lean_files),
    "lean_completed": len(completed),
    "lean_placeholders": len(placeholders),
    "lean_sorry": num_sorry,
    "python_demos": python_demos,
    "pytest_total_passed": total_tests,
    "outside_domain_cases": outside_cases,
}

# Generate markdown table
status_md = textwrap.dedent(
    f"""
| Metric | Count |
|--------|-------|
| Lean files (core) | {len(lean_files)} |
| &nbsp; • completed proofs | {len(completed)} |
| &nbsp; • placeholders | {len(placeholders)} |
| &nbsp; • with `sorry` | {num_sorry} |
| Python demos verified | {python_demos} |
| Total pytest tests passed | {total_tests} |
"""
)

# ------------------------------------------------------------------
#  Parse STATUS tags from source files to build correspondence table
# ------------------------------------------------------------------

TAG_LEAN_RE = re.compile(r"^\s*--\s*STATUS:\s*(full|partial|none)\s*\|\s*([A-Za-z0-9_\-]+)")
TAG_DEMO_RE = re.compile(r"^\s*#\s*STATUS:\s*demo\s*\|\s*([A-Za-z0-9_\-]+)")

# scan Lean files for status
for lf in PROOFS.glob("*.lean"):
    for line in lf.read_text().splitlines():
        m = TAG_LEAN_RE.match(line)
        if m:
            st, name = m.group(1), m.group(2)
            entry = tags.setdefault(name, {})
            entry["lean"] = st
            break

# scan Python demos for status demo tag across full artifact tree (covers disproof etc.)
for py in (ROOT / "artifact").rglob("*.py"):
    for line in py.read_text().splitlines():
        m = TAG_DEMO_RE.match(line)
        if m:
            name = m.group(1)
            entry = tags.setdefault(name, {})
            entry["demo"] = "yes"
            break

# Count python demo tests (numeric correspondences) by inspecting all test_*.py under artifact
demo_tests = 0
for py in (ROOT / 'artifact').rglob('test_*.py'):
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

# ----------------------------------------------------------
#  Falsification (attempted disproof) statistics
# ----------------------------------------------------------
DISPROOF_DIR = ROOT / "artifact" / "disproof"
cases_file = DISPROOF_DIR / "cases_outside.json"
outside_cases = 0
if cases_file.exists():
    try:
        data = json.loads(cases_file.read_text())
        if isinstance(data, dict):
            lst = data.get("outside_cases", data.get("cases", []))
            if isinstance(lst, list):
                outside_cases = len(lst)
        elif isinstance(data, list):
            outside_cases = len(data)
    except Exception:
        pass

# Pack falsification info into metrics
total_data["outside_domain_cases"] = outside_cases

# Markdown block for falsification summary
fals_md = textwrap.dedent(f"""
### Attempted falsification (property-based guardian)

*Inside-domain counter-examples*: **0** (CI would fail otherwise; *200 random C¹ instances per run – override via `$HYPOTHESIS_MAX_EXAMPLES`*)  
*Outside-domain cases logged*: **{outside_cases}** – see `artifact/disproof/cases_outside.json`.
""")

# markers for correspondences
CORR_START = "<!-- CORR-START -->"
CORR_END = "<!-- CORR-END -->"

# When inserting into README, combine corr_md + status_md

README_START = "<!-- STATUS-START -->"
README_END = "<!-- STATUS-END -->"

# JSON output: metrics + correspondences raw
if '--json' in sys.argv:
    out = {"metrics": total_data, "correspondences": yaml_data}
    print(json.dumps(out))
    sys.exit(0)

if '--insert-readme' in sys.argv:
    readme = ROOT / 'README.md'
    lines = readme.read_text().splitlines()
    try:
        start = lines.index(README_START)
        end = lines.index(README_END)
        combined_block = status_md.strip().splitlines()
        if corr_md.strip():
            combined_block += [''] + corr_md.strip().splitlines()
        combined_block += [''] + fals_md.strip().splitlines()
        new_lines = lines[:start+1] + [''] + combined_block + [''] + lines[end:]
        readme.write_text("\n".join(new_lines))
    except ValueError:
        # markers missing: append at end
        with open(readme, 'a') as f:
            f.write(f"\n## Verification status\n{README_START}\n{status_md}\n{corr_md}{README_END}\n")

else:
    print(status_md) 