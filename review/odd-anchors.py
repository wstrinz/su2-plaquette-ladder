"""Compute odd-sector energy-density lower bounds at selected couplings on two plaquettes."""
from fractions import Fraction
from pathlib import Path
import argparse
import json
import math
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "handoff/zero_winding"))
from even_replay import ZUp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("couplings", nargs="+", type=Fraction)
    parser.add_argument("--penalty", type=Fraction, default=Fraction(12))
    args = parser.parse_args()
    if args.penalty <= 0:
        parser.error("the block penalty must be positive")
    model = ZUp(6, args.penalty, parity=1)
    for coupling in args.couplings:
        # Keep the lower endpoint as an exact dyadic rational after outward rounding.
        ball = model.ground_lower(coupling)
        lower = math.nextafter(float(ball.lower()), -math.inf)
        penalty = int(args.penalty) if args.penalty.denominator == 1 else str(args.penalty)
        print(json.dumps(dict(x=str(coupling), two_j_star=6, penalty=penalty,
                              omega_lower=str(Fraction.from_float(lower)))), flush=True)


if __name__ == "__main__":
    main()
