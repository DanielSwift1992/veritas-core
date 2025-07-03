#!/usr/bin/env python3
"""Navier–Stokes energy check on an analytical divergence-free field.

We use the 2-D steady vortex field
    u(x,y) =  sin x cos y
    v(x,y) = -cos x sin y
which satisfies ∇·u = 0.  For this field the volumetric energy rate
    \int u · (u·∇)u  dA
is analytically zero over a rectangular integer-multiple-π domain because the
integrand is a total derivative that integrates to zero.
The script samples the domain [0,2π]² on an N×N grid and confirms that the
numerical integral is ≈ 0.  No magic constants: all parameters are CLI flags.
"""

import argparse
import numpy as np


def velocity_field(x: np.ndarray, y: np.ndarray):
    """Return (u, v) for the analytic field."""
    u = np.sin(x) * np.cos(y)
    v = -np.cos(x) * np.sin(y)
    return u, v


def convective_term(u: np.ndarray, v: np.ndarray, dx: float):
    """Compute u·∇u component-wise (central differences, periodic)."""
    # Periodic shift helpers
    def roll(f, axis, shift):
        return np.roll(f, shift, axis=axis)

    dudx = (roll(u, 1, 1) - roll(u, -1, 1)) / (2 * dx)
    dudy = (roll(u, 1, 0) - roll(u, -1, 0)) / (2 * dx)
    dvdx = (roll(v, 1, 1) - roll(v, -1, 1)) / (2 * dx)
    dvdy = (roll(v, 1, 0) - roll(v, -1, 0)) / (2 * dx)

    conv_x = u * dudx + v * dudy
    conv_y = u * dvdx + v * dvdy
    return conv_x, conv_y


def f_dot_grad_p(u: np.ndarray, v: np.ndarray, grad_x: np.ndarray, grad_y: np.ndarray):
    """Generic Δ-Kernel contraction F·∇P for 2-D vector fields.

    Parameters
    ----------
    u, v : ndarray
        Components of the vector field **F**.
    grad_x, grad_y : ndarray
        Components of the gradient ∇P.
    """
    return u * grad_x + v * grad_y


def main():
    p = argparse.ArgumentParser(description="Navier–Stokes energy consistency test")
    p.add_argument("--N", type=int, default=64, help="Grid resolution (default 64)")
    p.add_argument("--ci", action="store_true")
    args = p.parse_args()

    N = args.N
    L = 2 * np.pi
    x = np.linspace(0, L, N, endpoint=False)
    y = np.linspace(0, L, N, endpoint=False)
    X, Y = np.meshgrid(x, y)

    u, v = velocity_field(X, Y)
    dx = L / N
    conv_x, conv_y = convective_term(u, v, dx)

    # Energy rate integrand u·conv
    integrand = f_dot_grad_p(u, v, conv_x, conv_y)
    dE_dt = integrand.mean()  # average over domain ≈ integral / area

    print(f"∫ u·(u·∇)u dA / Area ≈ {dE_dt:.3e}")


if __name__ == "__main__":
    main() 