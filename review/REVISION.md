# Response to the independent computational review

Revision 2, 24 November 2026. The primary article treats a periodic SU(2) ladder one square wide at fixed lattice spacing. The full gap exceeds 1 through coupling 12.25, 0.76 through 14, and 0.46 through 16 at every even length. The new numerical result concerns the winding energy per square.

| Review point | Change and supporting evidence |
| --- | --- |
| Stronger last winding bound | In Section 4, the rational penalty 15523/1000 at coupling 32 gives the common rounded two-square odd lower bound −39.523661. The retained block still has 1,734 states. With trial coefficients (40,50,34,16,5,1), the even trial energies per square at 30 and 32 are −152359/8307 and −165346/8307. Concavity of the odd energy and the affine even trial give a winding cost per square of at least 57/400 throughout [30,32], for every even length and in the limit. |
| Local center sector | Lemma 2 now imposes the center charge on each split cell before gluing. It checks both orientations at length two and the real antisymmetric midpoint factors against Lu, Supplement Eq. (S10) and Sec. SI.B. The proof identifies the finite-cutoff penalty kernel with the physical winding sector. |
| Scope of formalization | The table in Section 5 identifies the paper, interval-arithmetic and Lean components. The new Lean file verifies the rational chord implication under its two energy hypotheses. The physical operator argument and the spectral inputs are separate obligations. |
| Historical wording | The historical note flags the unproved monotonicity of the winding difference. Section 4 proves compact-uniform convergence to its thermodynamic limit. The current README and string notes distinguish small-coupling order, finite-size evidence and the proposed zero-field transition. |
| Research implications | Section 2 gives the moment construction for any fixed transverse width with open transverse boundaries. Wider strips need new spectral seeds. The optional rail supplement proves a field-induced thermodynamic sector crossing and a lower bound on the polarization jump wherever the winding tension is positive. |
| Artifact identification | The manuscript identifies the exact versioned computational ZIP by filename and SHA-256. The reviewer packet contains those bytes, an expanded copy, and the single-file TeX submission ZIP. The source can be rebuilt without the companion. |

## What was checked for revision 2

- The supplied independent check archive passed all 17 manifest entries. Its report documents a fresh Python penalty refinement. The project then recomputed the coupling-32 anchor in Python and Julia. Both exact lower endpoints exceed −39.523661. See `review/extended/refined-{python,julia}.jsonl`.
- Python and Julia independently recomputed the final even-sector row [15.5,16]. The small audit compares those outputs and both archived sets of eleven rows against the actual Lean literals. The implementations share the physical inequalities and recoupling convention.
- A fresh ladder-project build used Lean 4.36.0-rc1 with previously installed dependencies and the pinned CertifiedGaps checkout 77b55881495a059ed22123e4e85eaaa8c3faa422. The extension and refined-chord declarations printed only propext, Classical.choice and Quot.sound. The build transcript is `review/extended/lean-revision-build.log`.
- The ordinary Python audit checks stored evidence for 240 A, 760 B, and 180 C intervals. The README gives separate commands for numerical regeneration. A reviewer can start with Lemma 2, followed by the shared-rung term of the variational trial at length two.

## Open research target

At coupling 6 the finite-cutoff pilot ratio is about 0.9470914 against a target of 0.93. If a rigorous twelve-square trial energy worsens by δT and a six-square log-trace upper bound by δℓ, their combined loss must satisfy βδT + 2δℓ < log(0.9470914/0.93), approximately 0.01821, for this pilot margin to survive. The unrestricted tail and the certified variational expectation remain to be controlled. The infinite-string zero-field critical coupling and universality class remain open.
