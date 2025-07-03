import subprocess
import sys
import re
import math
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]  # project root
CODE = ROOT / "artifact" / "code"

# Allow importing demo modules
sys.path.append(str(CODE / "neuro"))
from hh_spike import simulate as hh_simulate  # type: ignore

FLOAT_RE = re.compile(r"([+-]?[0-9]+(?:\.[0-9]+)?(?:e[+-]?\d+)?)")

def _extract_last_float(text: str) -> float:
    matches = FLOAT_RE.findall(text)
    assert matches, f"No float found in output: {text}"
    return float(matches[-1])

def _run_py(script_rel: Path):
    """Run a Python demo script with --ci flag and return stdout string."""
    cmd = [sys.executable, str(script_rel), "--ci"]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return result.stdout.strip()


def test_landauer():
    out = _run_py(CODE / "physics" / "landauer.py")
    # Choose the smallest float in output (energy value) to avoid picking temperature.
    floats = [float(x) for x in FLOAT_RE.findall(out)]
    val = floats[-1]
    k_B = 1.380649e-23
    T = 300.0
    expected = k_B * T * math.log(2)
    assert math.isclose(val, expected, rel_tol=0.05), f"Landauer energy off: {val} vs {expected}"


def test_shannon_cap():
    out = _run_py(CODE / "info" / "shannon_cap.py")
    val = _extract_last_float(out)
    B, SNR = 1e3, 10
    expected = B * math.log2(1 + SNR)
    assert math.isclose(val, expected, rel_tol=0.05), f"Capacity off: {val} vs {expected}"


def test_pid_phi():
    out = _run_py(CODE / "control" / "pid_phi.py")
    nums = FLOAT_RE.findall(out)
    assert len(nums) >= 3, "Could not parse PID ratios"
    phi_calc = (1 + 5 ** 0.5) / 2
    kp, ki, kd = float(nums[0]), float(nums[1]), float(nums[2])
    assert math.isclose(ki, phi_calc, rel_tol=0.01)
    assert math.isclose(kd, phi_calc ** 2, rel_tol=0.01)


def test_gd_energy():
    out = _run_py(CODE / "ml" / "gd_energy.py")
    val = _extract_last_float(out)

    # Recompute expected loss locally using same algorithm to high precision.
    x, y = -1.2, 1.0
    lr = 0.001
    for _ in range(100):
        grad_x = -2 * (1 - x) - 400 * x * (y - x ** 2)
        grad_y = 200 * (y - x ** 2)
        x -= lr * grad_x
        y -= lr * grad_y
    expected = (1 - x) ** 2 + 100 * (y - x ** 2) ** 2
    assert math.isclose(val, expected, rel_tol=1e-4)
    assert val < 5.0  # sanity check, should have decreased considerably


def test_hh_spike():
    out = _run_py(CODE / "neuro" / "hh_spike.py")
    try:
        data = json.loads(out)
        energy = data["energy"]
        bits = data["bits"]
    except json.JSONDecodeError:
        # fallback to old format
        floats = [float(x) for x in FLOAT_RE.findall(out)]
        energy = min(floats)
        bits = max(floats)

    expected = hh_simulate()
    assert math.isclose(energy, expected, rel_tol=2e-4)
    assert 1e8 < bits < 1e12  # broad plausible window


def test_ns_energy():
    out = _run_py(CODE / "physics" / "ns_energy.py")
    val = _extract_last_float(out)
    assert abs(val) < 1e-4  # residual near zero


# --- Fokker–Planck / entropy production ---


def test_fp_entropy():
    out = _run_py(CODE / "stats" / "fokker_planck_entropy.py")
    # extract the min derivative value
    val = _extract_last_float(out)
    assert val >= -2e-3, "Entropy derivative decreased beyond acceptable numeric noise"


# --- Noether energy conservation ---

def test_noether_energy():
    out = _run_py(CODE / "physics" / "harmonic_energy.py")
    val = _extract_last_float(out)
    assert val < 1e-4


# --- FFT operations ratio ---

def test_fft_ratio():
    out = _run_py(CODE / "alg" / "fft_ops.py")
    nums = FLOAT_RE.findall(out)
    ratio = float(nums[0])
    logN = float(nums[-1])
    N_val = float(int(2 ** round(logN)))
    expected = 2 * N_val / logN
    assert abs(ratio - expected) / expected < 0.05 

# --- Nash equilibrium gradient descent ---

def test_nash_grad():
    out = _run_py(CODE / "game" / "nash_gradient.py")
    val = _extract_last_float(out)
    assert val < 1e-3 