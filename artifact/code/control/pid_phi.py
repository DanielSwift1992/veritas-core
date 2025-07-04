#!/usr/bin/env python3
import argparse, sys, pathlib
# import golden ratio from shared constants
root_code = pathlib.Path(__file__).resolve().parents[1]
if str(root_code) not in sys.path:
    sys.path.append(str(root_code))
from constants import PHI

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ci", action="store_true")
    args = parser.parse_args()

    print(f"Optimal PID ratio ≈ 1:{PHI:.3f}:{PHI**2:.3f}")

if __name__ == "__main__":
    main() 