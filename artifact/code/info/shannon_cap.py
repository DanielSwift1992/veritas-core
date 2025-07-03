#!/usr/bin/env python3
"""Shannon–Hartley Channel Capacity Calculator.

Formula: C = B * log2(1 + S/N)
Units: B Hz; S/N linear; output bits/s.
"""
import argparse, math

def capacity(bandwidth_hz: float, snr_linear: float) -> float:
    return bandwidth_hz * math.log2(1.0 + snr_linear)

def main() -> None:
    p = argparse.ArgumentParser(description="Shannon–Hartley capacity")
    p.add_argument("--bw", type=float, default=1000.0, help="Bandwidth in Hz")
    p.add_argument("--snr", type=float, default=10.0, help="Signal-to-noise ratio (linear)")
    p.add_argument("--ci", action="store_true")
    a = p.parse_args()
    c = capacity(a.bw, a.snr)
    print(f"Capacity = {a.bw:.2f} Hz * log2(1 + {a.snr:.2f}) = {c:.2f} bits/s")

if __name__ == "__main__":
    main()
