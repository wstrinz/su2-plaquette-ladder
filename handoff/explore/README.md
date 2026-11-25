# Exploration after referee round 1 (not part of the claimed theorem)

Floating point unless stated. Uses ../replay/ladder_ops.jl (operators) and ../replay/ladder_replay.jl (interval machinery).

- `gap_scan.jl`, `gaps_L*_J*.json/.log`   lowest levels by ring length, cutoff and winding charge c = (-1)^(2 j_b + 2 j_t).
     L=2 at cutoff 3 (and 7/2, 4), L=3 at 5/2, L=4 at 3/2, 2, 5/2, L=6 at 3/2.
     Finding: the smallest gap over even L is at L = 2 and is a winding state (2.00 at lam = 0, 1.33 at 6, 1.09 at 14).
     For L >= 6 the lowest excitation is a plaquette excitation near 4, rising with lam.
- `horizon.py`, `horizon.json`            best bound the two-plaquette seed could give with exact inputs, all sectors and c = +1;
     also the convexity test of log Z_2 in lam (Lemma 4 (b)): smallest second difference 0.0015 > 0.
- `sector_moment_check.jl/.json`          the three moment inequalities sector by sector (18 cases each): hold for c = +1 and c = -1,
     fail in 15 of 18 for the twisted trace Z_+ - Z_- (about which nothing is claimed).
- `sector_bounds.jl`, `sector_bounds.py`, `sector_scan.json`, `sector_scan_best.json`, `sector_scan_beyond6.json`
     rigorous interval seeds restricted to c = +1 on sample intervals, and the resulting bounds (Arb mirror of the recurrence):
     2.79 at lam = 0.25, 2.58 at 1, 2.18 at 2, 1.85 at 4, 1.55 at 6, 1.38 at 8, 1.21 at 10.
     NOT a tiling, NOT in Lean, NOT replayed. Needs the candidate Lemma 5 of the note (sector penalty is an on-site,
     real, reflection-invariant term).

The sector option added to ../replay/ladder_replay.jl defaults to all sectors; the replay of the theorem was rerun after
the change: 240 of 240.
