#!/usr/bin/env python3
import math, argparse, textwrap

# Physical constants
k_B = 1.380649e-23  # Boltzmann constant, J/K (CODATA 2019)

def main():
    """Compute the Landauer limit E_min = k_B * T * ln 2.

    The temperature T can be given via --temp. If omitted, defaults to the
    textbook room-temperature 300 K.  No other hidden constants are used.
    """

    parser = argparse.ArgumentParser(
        description="Compute minimal energy required to erase one bit (Landauer).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """Example:
            --------
            $ python landauer.py --temp 310
            E_min ≈ 2.97e-21 J (300.00 K → 310.00 K)""",
        ),
    )
    parser.add_argument("--temp", type=float, default=300.0, help="Temperature in Kelvin (default: 300K)")
    parser.add_argument("--ci", action="store_true", help="flag used only by the test-runner")
    args = parser.parse_args()

    T = args.temp
    e_min = k_B * T * math.log(2)
    print(f"E_min = k_B·T·ln2 = {k_B:.3e} * {T:.2f} * ln2 = {e_min:.3e} J")

if __name__ == "__main__":
    main() 