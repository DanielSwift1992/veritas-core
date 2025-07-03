#!/usr/bin/env python3
"""Mini Stokes (Poiseuille) demo on a 1-D channel.

We consider an incompressible, steady, pressure-driven Stokes flow between two
parallel plates separated by distance 2 (y ∈ [-1,1]).  Choosing units where the
pressure gradient and dynamic viscosity satisfy G/(2μ)=1 gives the analytical
velocity profile

    u(y) = 1 − y².

The viscous dissipation rate per unit length is

    Φ = μ ∫_{-1}^{1} (du/dy)² dy = ∫ 4 y² dy = 8/3.

This script discretises the domain with a small grid (default 15 points),
computes the numerical derivative with second-order central differences and
approximates the integral.  It prints the ratio Φ_num / Φ_exact which should be
within 5 % of 1.
"""

import argparse
import numpy as np


def u_profile(y: np.ndarray):
    return 1.0 - y ** 2


def dissipation(grid: int = 15):
    y = np.linspace(-1.0, 1.0, grid)
    dy = y[1] - y[0]
    u = u_profile(y)
    # central difference for du/dy (periodic not needed, interior points only)
    du_dy = np.gradient(u, dy, edge_order=2)
    integrand = du_dy ** 2  # μ = 1
    phi_num = np.trapz(integrand, y)
    phi_exact = 8.0 / 3.0
    return phi_num / phi_exact


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--N", type=int, default=15, help="grid points (default 15)")
    p.add_argument("--ci", action="store_true")
    args = p.parse_args()
    ratio = dissipation(args.N)
    print(f"Φ_num / Φ_exact ≈ {ratio:.3f}")


if __name__ == "__main__":
    main()