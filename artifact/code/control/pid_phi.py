#!/usr/bin/env python3
import math, argparse

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ci", action="store_true")
    args = parser.parse_args()

    phi = (1 + 5 ** 0.5) / 2
    print(f"Optimal PID ratio ≈ 1:{phi:.3f}:{phi**2:.3f}")

if __name__ == "__main__":
    main() 