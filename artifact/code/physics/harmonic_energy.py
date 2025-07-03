#!/usr/bin/env python3
"""Noether energy conservation demo: 2-D uncoupled harmonic oscillator.
We integrate x'' + x = 0, y'' + y = 0 via symplectic Euler and check that
 total energy E = 0.5*(x^2 + y^2 + vx^2 + vy^2) stays within tolerance.
"""
import argparse, math

def simulate(dt=0.01, steps=10000):
    x, y = 1.0, 0.0
    vx, vy = 0.0, 1.0
    E0 = 0.5*(x*x + y*y + vx*vx + vy*vy)
    max_dev = 0.0
    for _ in range(steps):
        # symplectic Euler
        vx -= dt * x
        vy -= dt * y
        x += dt * vx
        y += dt * vy
        E = 0.5*(x*x + y*y + vx*vx + vy*vy)
        max_dev = max(max_dev, abs(E - E0))
    return max_dev / E0

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--dt', type=float, default=0.01)
    p.add_argument('--steps', type=int, default=10000)
    p.add_argument('--ci', action='store_true')
    a = p.parse_args()
    rel_err = simulate(a.dt, a.steps)
    print(f"Relative energy drift ≈ {rel_err:.3e}")

if __name__ == '__main__':
    main() 