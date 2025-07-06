import subprocess, pathlib, sys, os, tempfile, shutil
import pytest

CPP_SRC = pathlib.Path(__file__).resolve().parent.parent / "cpp" / "delta_kernel.cpp"

@pytest.mark.skipif(not shutil.which("c++"), reason="C++ compiler not available")
def test_cpp_kernel_passes(tmp_path):
    """Compile C++ reference implementation and run its internal asserts."""
    exe = tmp_path / "delta_kernel"
    cmd = [
        "c++",
        "-std=c++17",
        "-O2",
        str(CPP_SRC),
        "-DUNIT_TEST_MAIN",
        "-o",
        str(exe),
    ]
    subprocess.check_call(cmd)
    subprocess.check_call([str(exe)]) 