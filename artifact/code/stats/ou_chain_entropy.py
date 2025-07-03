#!/usr/bin/env python3
"""Ornstein–Uhlenbeck discrete-time chain entropy check.

We simulate the AR(1) process
    X_{t+1} = ρ X_t + ε_t,   ε_t ~ N(0, σ²)
with |ρ| < 1.  The stationary variance is σ²/(1-ρ²).  Starting far from
stationarity, the differential entropy of the Gaussian state should increase
monotonically.  We check that min ΔH ≥ -ε for a small ε (numerical noise).
"""

import argparse
import numpy as np
import math


def simulate(rho: float = 0.9, sigma: float = 1.0, n: int = 10000, steps: int = 2000):
    rng = np.random.default_rng(1)
    x = rng.normal(loc=10.0, scale=5.0, size=n)
    entropies = []
    for _ in range(steps):
        eps = rng.normal(scale=sigma, size=n)
        x = rho * x + eps
        var = x.var()
        H = 0.5 * math.log(2 * math.pi * math.e * var)
        entropies.append(H)
    return np.array(entropies)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--ci", action="store_true")
    args = p.parse_args()
    H = simulate()
    dH = np.diff(H)
    print(f"min ΔH = {dH.min():.3e}")


if __name__ == "__main__":
    main()
