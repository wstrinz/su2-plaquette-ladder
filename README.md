# SU(2) plaquette ladder

[Download the computational companion (r2)](https://github.com/wstrinz/su2-plaquette-ladder/releases/download/r2/su2-ladder-companion-r2.zip). SHA-256 `a762a6747125f033a1bc7914ca4adc56f538dbc7b06a7014788d5acbe6c6dd95`. This repository contains the primary paper’s computational evidence. The release asset is the exact archive identified in the manuscript.

The review packet contains the primary manuscript and single-file pdfLaTeX source. In the working project they are `paper/ladder.pdf` and `paper/ladder.tex`. The original note and scripts are preserved in `handoff/`. The original source ZIP has SHA-256 `15b0bc622ffddc58d98b9c5770c4ea98fc103a261ab98aeab461033d2c068f39`.

## Claim status for revision 2

| Range in electric units | Claim for every even ring of length at least two |
| --- | --- |
| 0 through 12 | Unique even-winding ground state. Full spectral gap above 1. Odd-winding energy cost at least 0.5584 per plaquette. |
| 12 through 12.25 | Full gap above 1. The winding energy cost exceeds 0.5499 per plaquette. |
| 12.25 through 14 | Full gap above 0.76. |
| 14 through 16 | Full gap above 0.46. |
| 12 through 32 | Winding energy per plaquette at least 0.42 on [12,16], 0.40 on [16,20], 0.36 on [20,24], 0.20 on [24,30] and 0.1425 on [30,32]. At 12 its upper bound is 1.05722. |
| Every fixed nonnegative coupling | Both sector ground-energy densities converge along even lengths. Their difference defines a finite thermodynamic winding tension. |

Start with the reflection lemma in Section 2. Check the midpoint generator orientations, the identification of the penalty kernel with the physical space, and restriction of each split cell to its winding charge before gluing. Section 3 uses these inequalities to pass from interval enclosures to all even lengths and remove the cutoff. A second reviewer can start in Section 4 with the plaquette-product trial. In particular check the mixed electric derivative at a shared rung for length two, and the odd trial obtained by inserting a fundamental rail loop. The numerical implementations share the same operator inequalities and recoupling convention.

At coupling 32 the complementary-block estimate for penalty 16 is too low to prove positive winding tension. Penalty 15 gave 0.0999 in revision 1. The rational penalty 15523/1000 gives 0.1425 on [30,32] with the same 1,734-dimensional retained block. A next experiment at larger coupling is to increase the retained spin cutoff and compare the resulting enclosure with the same explicit trial. The full gap beyond 16 requires separate control of even-sector excitations.

The optional string supplement proves small-coupling rail order on paper and reports a cutoff-free four/six-square crossing. The finite-coupling critical point and Ising universality in the unrestricted infinite string are conjectural. A field coupled to the difference of rail signs produces a separate first-order sector crossing wherever the winding tension is positive. See `review/REVISION.md` for the changes and verification record.

## Reproduce the checks

Run commands from the campaign root or the unpacked companion root. The small audit reads archived numerical outputs and actual Lean table literals. Python 3.10 or later suffices.

```sh
python review/check-certificates.py
```

The audit checks 240 A, 760 B and 180 C intervals, the final original C replay, both sets of 11 extended even intervals against the actual Lean literals, and the variational endpoint arithmetic. The stored Julia seed decimals have explicit slack in the extended checks. Odd-sector endpoint files record binary lower endpoints as exact fractions. Regenerating them exercises operator assembly and spectral enclosures.

For a numerical replay use Python 3.12, NumPy 1.26.4, SciPy 1.13.1, SymPy 1.13.3 and python-flint 0.8.0. Choose a new directory for outputs because the interval drivers resume existing JSONL files.

```sh
out=$(mktemp -d)
python3.12 -m venv "$out/env"
"$out/env/bin/pip" install numpy==1.26.4 scipy==1.13.1 sympy==1.13.3 python-flint==0.8.0
export OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2
"$out/env/bin/python" handoff/tension/tension_replay.py compute handoff/tension/tiling.json "$out/tension-180.jsonl" 180 180
"$out/env/bin/python" review/odd-anchors.py 14 16 18 20 22 > "$out/odd-anchors.jsonl"
mkdir -p "$out/extended"
"$out/env/bin/python" review/odd-anchors.py 24 26 28 30 > "$out/extended/odd-python.jsonl"
"$out/env/bin/python" review/odd-anchors.py --penalty 16 30 32 > "$out/extended/penalty16-python.jsonl"
"$out/env/bin/python" review/odd-anchors.py --penalty 15 32 > "$out/extended/penalty15-python.jsonl"
"$out/env/bin/python" review/odd-anchors.py --penalty 15523/1000 32 > "$out/extended/refined-python.jsonl"
"$out/env/bin/python" handoff/zero_winding/even_replay.py compute review/extended/tiling.json "$out/extended/python.jsonl" 1 11
```

The archived replay of interval 180 gave a raw tension lower enclosure of 0.55841751681875 against the rational target 0.5584. For an isolated validation of fresh output, copy the companion into a scratch directory and replace the corresponding rows in its `review/` directory before running the small audit. Last digits of independently recomputed enclosures can vary with the choice of trial coordinates.

The second new-anchor run used Julia 1.12.6 and the upstream Julia project at commit `77b55881495a059ed22123e4e85eaaa8c3faa422`. With that repository checked out at `$certified_gaps`, run:

```sh
julia --project="$certified_gaps/code/julia" -e 'using Pkg; Pkg.instantiate()'
julia --project="$certified_gaps/code/julia" review/odd-anchors.jl "$out/odd-julia.jsonl" 14 16 18 20 22
julia --project="$certified_gaps/code/julia" review/odd-anchors.jl "$out/extended/odd-julia.jsonl" 24 26 28 30 32 36 40
julia --project="$certified_gaps/code/julia" review/odd-anchors.jl "$out/extended/penalty16-julia.jsonl" --penalty 16 30 32
julia --project="$certified_gaps/code/julia" review/odd-anchors.jl "$out/extended/penalty15-julia.jsonl" --penalty 15 32
julia --project="$certified_gaps/code/julia" review/odd-anchors.jl "$out/extended/refined-julia.jsonl" --penalty 15523/1000 32
julia --project="$certified_gaps/code/julia" handoff/zero_winding/even_seeds.jl review/extended/tiling.json "$out/extended/julia.jsonl"
```

For the pinned Lean build, install elan and place its binaries on PATH. Git, Python 3, Bash and network access to the dependency repositories and mathlib cache are needed. The helper builds in a new temporary directory and corrects the producer's absolute dependency path in the working copy only.

```sh
bash review/build-lean.sh
```

The build covers the original interval and full-gap declarations, the reflection algebra, the scalar secant argument in `WindingContinuation.lean`, the eleven interval chains and conditional gap theorem in `ExtendedGap.lean`, and the refined winding chord in `RefinedTension.lean`. Set `SU2_DEPENDENCY_CACHE` to a previous build directory to reuse the pinned clean upstream checkout and installed packages. The helper still rebuilds the ladder project in a fresh directory. The new gap theorem printed only `propext`, `Classical.choice` and `Quot.sound`. Identifying the physical hypotheses, computing the variational expectations and passing to the infinite ring are paper arguments.

## Hexagon preparation

The source ZIP contains only `ladder.tex` at its root. Build with pdfLaTeX twice. The external review packet contains the exact `su2-ladder-companion-r2.zip` cited by the paper, alongside the expanded files for convenient auditing. It includes the tables, historical note, numerical evidence, new proofs and reproduction instructions. For deposit, give the companion a stable public location and cite that version in the manuscript. A focused independent specialist read is still outstanding.

Suggested subject is Mathematical Physics (math-ph). The manuscript carries the human author named in the handoff and a note describing Claude's and Codex's contributions. Contributor approval, the human-understanding declaration, ORCID and the license are decisions for the contributor. The work has not been submitted. [Hexagon deposit information](https://hexagonmath.org/about)
