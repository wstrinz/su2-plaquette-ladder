# How sharply must winding flux polarize the ladder?

This follow-up uses the archived revision 2 inputs for the periodic, one-square-wide SU(2) ladder at fixed lattice spacing, with all link representations. It concerns equilibrium ground energies at zero temperature. Here x is the magnetic coupling in electric units and h multiplies the difference of the rail center signs. Polarization is the mean of that difference divided by two, so full polarization has magnitude one.

## A bound for every even ring and its thermodynamic limit

At every cut set A = (s_bottom − s_top)/2 with s = (−1)^(2j). In the even sector A vanishes as an operator. In the odd sector it takes values ±1. Add −h times the sum of A over cuts. At fixed x write d(h) for the odd ground energy per square minus the even one. The same argument works for finite rings and their even-length limit. Each trial energy is affine in h, so d is concave. Rail exchange makes it even. If d(0) ≥ σ > 0 and d(H) ≤ 0, the unique positive crossing satisfies σ ≤ h_c ≤ H. Indeed d is 1-Lipschitz, and its right derivative at a zero is at most −d(0)/h_c. The full energy follows the constant even branch below the crossing and the odd branch above it. Its conjugate polarization therefore jumps by at least σ/H.

The trial is a fundamental loop on the favored rail multiplied by a product of plaquette functions f = Σ v_n χ_(n/2). Write N = Σ v_n². On an odd state A equals the signed center operator on the unoccupied rail of the original loop, choosing the loop orientation to give positive polarization. At a single cut that flip sends one plaquette variable U to −U and fixes the loop. Haar integration and character parity give the exact mean m_v = Σ (−1)^n v_n² / N. The zero-field trial energy per square is 1 + u_v(x), where u_v is the primary manuscript's Proposition 4. For m_v > 0 and an even energy lower bound b(x), a valid upper field is (1 + u_v(x) − b(x))/m_v.

On each of the 180 source intervals take b(x) to be the negative of the linearly interpolated upper bound on log Z_even(2,β₁), divided by 2β₁. This follows from length comparison and the ground term in the heat trace. For a fixed trial, the upper field is affine, so its two endpoint values control the entire interval. The script minimizes the larger endpoint over nine explicit integer trial vectors, then rounds the reported field up and jump down. Its only numerical inputs are the archived rational tension rows. The physical hypotheses are those of the manuscript and its rail-field supplement.

| Coupling x | Upper bound on h_c | Lower bound on polarization jump |
| --- | ---: | ---: |
| [0,1] | 1.0208 | 0.9442 |
| [1,2] | 1.0820 | 0.8200 |
| 2.14 | 1.0927 | 0.8008 |
| [2,4] | 1.3035 | 0.5741 |
| [4,6] | 1.6247 | 0.4088 |
| [6,8] | 2.0102 | 0.3057 |
| [8,10] | 2.4367 | 0.2388 |
| [10,12] | 2.8872 | 0.1934 |

At x = 2.14 the same row gives σ = 0.8751, enclosing h_c between 0.8751 and 1.0927. These are bounds on the size and location of the switch. The thresholds and jump magnitudes can vary within them. Run `python research/rail-scaling/field-bands.py` from the campaign root to reproduce the table using Python's rational arithmetic.

## Two checks on the interpretation

At x = 0 the branches are exactly 0 and 1 − |h|. A bare loop saturates both the minimum electric cost and the maximum polarization. Hence h_c = 1 and the jump is one for every even length. At fixed finite even length, perturbation about the favored simple loop at h near one gives odd energy per square 1 − h − x²[(1/16)/(2+2h) + (3/16)/(14/3+2h)] + O_L(x⁴). The two channels are the zero- and spin-one projections of a single plaquette insertion on the occupied link. Differentiating the analytic branch and using h_c = 1 + 3x²/160 + O_L(x⁴) gives a crossing polarization of 1 − 13x²/800 + O_L(x⁴). This expansion is a finite-volume prediction. The interval bounds above hold uniformly in length.

The two winding sectors are exactly conserved, even for a time-dependent bias h(t). An isolated ring initialized in the even sector stays there when the field is swept. A simulation can locate the transition by preparing each sector separately and comparing its energy. The slope of the odd energy gives the polarization of the winning branch. Localizing a zero-field Ising transition inside the prepared odd string requires separate evidence.
