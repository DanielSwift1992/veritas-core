import subprocess, sys, pathlib, shutil, pytest

ROOT = pathlib.Path(__file__).resolve().parents[2]
PROOFS = ROOT / "artifact" / "proofs"

@pytest.mark.skipif(not shutil.which("lake"), reason="Lean toolchain not installed")
def test_lean_build_success():
    """Run `lake build` in artifact/proofs and assert it exits with code 0."""
    result = subprocess.run(["lake", "build"], cwd=PROOFS, capture_output=True, text=True)
    if result.returncode != 0:
        # Print stderr/stdout for easier debugging in CI logs
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
    assert result.returncode == 0, "Lean build failed — see log above"