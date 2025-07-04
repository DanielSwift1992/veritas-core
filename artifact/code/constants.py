import math

"""Shared physical/mathematical constants used across numeric demos and tests."""

k_B: float = 1.380649e-23  # Boltzmann constant, J/K (CODATA 2019)
PHI: float = (1 + 5 ** 0.5) / 2  # golden ratio φ ≈ 1.618...
LN2: float = math.log(2)

# Default numeric tolerances
REL_TOL: float = 1e-4
ABS_TOL: float = 1e-9 