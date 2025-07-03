#!/usr/bin/env python3
import math, argparse, textwrap

def rosenbrock(x: float, y: float) -> float:
    """Classic Rosenbrock banana function."""
    return (1 - x) ** 2 + 100 * (y - x ** 2) ** 2

def main():
    parser = argparse.ArgumentParser(
        description="Gradient descent on Rosenbrock function",
        epilog=textwrap.dedent(
            """Defaults reproduce the classical starting point (-1.2,1.0) with 100 steps and lr=1e-3.""",
        ),
    )
    parser.add_argument("--x0", type=float, default=-1.2, help="Initial x (default -1.2)")
    parser.add_argument("--y0", type=float, default=1.0, help="Initial y (default 1.0)")
    parser.add_argument("--lr", type=float, default=1e-3, help="Learning rate (default 1e-3)")
    parser.add_argument("--steps", type=int, default=100, help="Number of iterations (default 100)")
    parser.add_argument("--ci", action="store_true", help="Flag used by test runner")
    args = parser.parse_args()

    x, y = args.x0, args.y0
    for _ in range(args.steps):
        grad_x = -2 * (1 - x) - 400 * x * (y - x ** 2)
        grad_y = 200 * (y - x ** 2)
        x -= args.lr * grad_x
        y -= args.lr * grad_y
    print(
        f"Final loss after {args.steps} steps with lr={args.lr} → {rosenbrock(x, y):.4f}"
    )

if __name__ == "__main__":
    main() 