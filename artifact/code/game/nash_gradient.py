#!/usr/bin/env python3
"""Two-player potential game: gradient descent to Nash equilibrium.
Players choose continuous strategies s_A,s_B ∈ [0,1]. Potential function
Φ(s_A,s_B)= -((s_A-0.5)^2 + (s_B-0.5)^2). Best response gradient ascent
should converge to (0.5,0.5). We output final gradient norm.
"""
import argparse, math


def simulate(lr=0.05, steps=2000):
    sa, sb = 0.9, 0.1  # far from equilibrium
    for _ in range(steps):
        grad_a = -2 * (sa - 0.5)
        grad_b = -2 * (sb - 0.5)
        sa += lr * grad_a
        sb += lr * grad_b
        # project to [0,1]
        sa = min(max(sa, 0.0), 1.0)
        sb = min(max(sb, 0.0), 1.0)
    grad_norm = math.hypot(-2 * (sa - 0.5), -2 * (sb - 0.5))
    return grad_norm


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lr', type=float, default=0.05)
    p.add_argument('--steps', type=int, default=2000)
    p.add_argument('--ci', action='store_true')
    a = p.parse_args()
    g = simulate(a.lr, a.steps)
    print(f"Gradient norm at final step ≈ {g:.3e}")


if __name__ == '__main__':
    main() 