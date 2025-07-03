#!/usr/bin/env python3
"""FFT operation count vs naive DFT.
Prints ratio complex_mult_naive / complex_mult_fft and compares to log2 N.
"""
import argparse, math

def counts(N:int):
    cmul_fft = N / 2 * math.log2(N)
    cmul_naive = N*N
    return cmul_naive / cmul_fft, math.log2(N)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--N', type=int, default=1024, help='size (power of 2)')
    p.add_argument('--ci', action='store_true')
    a=p.parse_args()
    ratio, logN = counts(a.N)
    print(f"Ratio = {ratio:.2f}, log2N = {logN:.2f}")

if __name__=='__main__':
    main() 