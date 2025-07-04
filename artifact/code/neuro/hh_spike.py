#!/usr/bin/env python3
"""Minimal Hodgkin–Huxley single-compartment simulation.
Outputs estimated energy (J) dissipated by ionic currents during an action potential
triggered by a brief current pulse. Designed to run in <1 s for CI."""

import argparse, math, sys, json, pathlib
# ensure constants module importable
root_code = pathlib.Path(__file__).resolve().parents[1]
if str(root_code) not in sys.path:
    sys.path.append(str(root_code))
from constants import k_B, LN2

# HH parameters (classic squid axon, Hodgkin & Huxley 1952)
DEFAULTS = {
    "C_M": 1.0,         # µF/cm^2
    "G_NA": 120.0,      # mS/cm^2
    "G_K": 36.0,
    "G_L": 0.3,
    "E_NA": 50.0,       # mV
    "E_K": -77.0,
    "E_L": -54.387,
    "dt": 0.025,        # ms
    "t_max": 50.0,      # ms
    "pulse_amp": 10.0,  # µA/cm^2
    "pulse_start": 5.0, # ms
    "pulse_end": 6.0,   # ms
    "area": 1e-4,       # cm^2 (100 µm^2)
    "temp": 300.0,      # K
}

def alpha_n(v):
    return 0.01 * (v + 55) / (1 - math.exp(-(v + 55) / 10))


def beta_n(v):
    return 0.125 * math.exp(-(v + 65) / 80)


def alpha_m(v):
    return 0.1 * (v + 40) / (1 - math.exp(-(v + 40) / 10))


def beta_m(v):
    return 4.0 * math.exp(-(v + 65) / 18)


def alpha_h(v):
    return 0.07 * math.exp(-(v + 65) / 20)


def beta_h(v):
    return 1 / (1 + math.exp(-(v + 35) / 10))


def simulate(params: dict = DEFAULTS):
    """Run HH model and return time series and dissipated energy (J)."""
    # Unpack parameters locally for speed
    C_M = params["C_M"]
    G_NA = params["G_NA"]
    G_K = params["G_K"]
    G_L = params["G_L"]
    E_NA = params["E_NA"]
    E_K = params["E_K"]
    E_L = params["E_L"]
    dt = params["dt"]
    t_max = params["t_max"]
    steps = int(t_max / dt)
    area_cm2 = params["area"]

    # Prepare external current vector
    I_EXT = [0.0] * steps
    start = int(params["pulse_start"] / dt)
    stop = int(params["pulse_end"] / dt)
    for i in range(start, stop):
        I_EXT[i] = params["pulse_amp"]

    v = -65.0  # mV initial
    # initialise gating variables at steady-state for v
    n = alpha_n(v) / (alpha_n(v) + beta_n(v))
    m = alpha_m(v) / (alpha_m(v) + beta_m(v))
    h = alpha_h(v) / (alpha_h(v) + beta_h(v))

    # Convert µF* mV to Joules: 1 µF = 1e-6 F, 1 mV = 1e-3 V, energy = C V^2/2.
    C = C_M * 1e-6 * area_cm2  # Farads

    total_energy = 0.0  # Joules (per cm^2 converted)

    for i in range(steps):
        I_ext = I_EXT[i]

        g_na = G_NA * m ** 3 * h
        g_k = G_K * n ** 4
        g_l = G_L

        I_na = g_na * (v - E_NA)
        I_k = g_k * (v - E_K)
        I_l = g_l * (v - E_L)

        dv = (I_ext - I_na - I_k - I_l) * dt / C_M
        v += dv

        dn = (alpha_n(v) * (1 - n) - beta_n(v) * n) * dt
        dm = (alpha_m(v) * (1 - m) - beta_m(v) * m) * dt
        dh = (alpha_h(v) * (1 - h) - beta_h(v) * h) * dt
        n += dn
        m += dm
        h += dh

        # Instantaneous power (µA/cm^2 * mV = µW/cm^2). Convert to Watts.
        power_uw_per_cm2 = -(I_na + I_k + I_l) * v  # negative sign: dissipation
        power_w = power_uw_per_cm2 * 1e-6 * area_cm2
        total_energy += power_w * (dt * 1e-3)  # ms to s

    return total_energy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ci", action="store_true", help="test-runner flag")
    parser.add_argument("--pulse", type=float, default=DEFAULTS["pulse_amp"], help="Pulse amplitude µA/cm^2")
    parser.add_argument("--area", type=float, default=DEFAULTS["area"], help="Patch area cm^2")
    parser.add_argument("--temp", type=float, default=DEFAULTS["temp"], help="Temperature K for bits calc")
    args = parser.parse_args()

    params = DEFAULTS.copy()
    params["pulse_amp"] = args.pulse
    params["area"] = args.area
    energy_j = simulate(params)
    # Estimate equivalent number of k_B T ln2 bits at 300 K
    T = args.temp
    bits = energy_j / (k_B * T * LN2)
    if args.ci:
        json.dump({"energy": energy_j, "bits": bits}, sys.stdout)
    else:
        print(f"ΔE_membrane ≈ {energy_j:.3e} J per {params['area']:.2e} cm^2 patch → {bits:.0f} bits")


if __name__ == "__main__":
    main() 