import subprocess, sys, re, math, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / "artifact" / "code"

FLOAT_RE = re.compile(r"([+-]?[0-9]+(?:\.[0-9]+)?(?:e[+-]?\d+)?)")


def _run(script_rel):
    cmd = [sys.executable, str(script_rel), "--ci"]
    out = subprocess.check_output(cmd, text=True).strip()
    return out


def test_stokes_mini():
    out = _run(CODE / "physics" / "stokes_mini.py")
    val = float(FLOAT_RE.findall(out)[-1])
    assert abs(val - 1.0) < 0.05  # within 5% of analytic ratio


def test_ou_chain():
    out = _run(CODE / "stats" / "ou_chain_entropy.py")
    val = float(FLOAT_RE.findall(out)[-1])
    assert val >= -0.1  # entropy non-decreasing on average (allow noise) 