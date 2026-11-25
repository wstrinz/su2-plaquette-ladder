> Historical v14 note, annotated after review. The current claim table is in the campaign README and the revised manuscript. The two sector energy densities are separately monotone in even length. Length dependence of their difference in the exploratory data is empirical.

# Two certified gap theorems for the SU(2) plaquette ladder

Nov 23, 2026 · @Will Strinz

## Summary

**Claims.** For the SU(2) Kogut–Susskind plaquette ladder on gauge-invariant states, with no cutoff on the flux and for every even ring length:

- Theorem A: at every coupling ratio λ/e from 0 to 6 the Hamiltonian has a nondegenerate ground state and a gap of at least 1.084 at small coupling, falling to 0.387 at λ/e = 6.
- Theorem B: at every coupling ratio from 0 to 12, inside the sector with no odd flux winding around the ring, the gap is at least 2.82 at small coupling, falling to 1.03 at λ/e = 12. It is above 1 throughout. Theorem C: over the same range, a flux line wound once around a ring of L plaquettes costs at least σL, with σ at least 0.99 at small coupling, falling to 0.558 at λ/e = 12; this is a lower bound on the string tension. Corollary: over the same range the ground state on all gauge-invariant states is unique, has no winding, and the gap above it is at least min(Theorem B's bound, σL), which is above 1 everywhere.

Energies are in units where one unit of fundamental flux on a link costs 1.

**Status: unreviewed.** Everything here was produced from 22 to 24 November 2026 by Claude, an AI, working with Will Strinz. No person has checked the lemmas. Nothing has been submitted or sent to anyone.

**What supports the claims.**

- Machine-checked in Lean: the purity criterion and the moment inequalities for reflection-positive rings (upstream library); the step from seed bounds to a gap on each of the 240 and 760 coupling intervals; that the intervals cover the ranges; that the bound of Theorem B exceeds 1; the step from four input bounds to σ on each of the 180 intervals of Theorem C; and the combination of Theorems B and C into a gap above 1 for the whole spectrum (theorem full\_gap\_gt\_one).
- Computed twice: the seed bounds on every interval, with rigorous arithmetic, by two separately written implementations per theorem. All three replays pass on every interval: 240 of 240, 760 of 760 and, for Theorem C, 180 of 180.
- Also machine-checked in Lean: the algebraic core of Lemma 1 (the reflection, the left and right translations, the plaquette identity with its four plus signs) and the whole of Lemma 6 (string tension from the moment inequalities). On paper only: Lemmas 1 to 5 and a limit argument, each a page or less, each with a numerical test designed to fail if the lemma were wrong. They are the part a referee needs to read, and the analytic part of Lemma 1 is what carries the most weight.
- Cited, not derived: the plaquette matrix elements in the spin-network basis, tested by exact identities at the sizes used, and equal, configuration by configuration, to the formula printed for this model in the quantum-simulation literature.

**Which theorem to care about.** Theorems B and C and their corollary. The bound of Theorem A is dragged down by a state that exists only because the ring is short: on 2 plaquettes a flux line winding once around the ring is the lowest excitation, and it gets lighter as the coupling grows. Theorem B is the gap with that state removed, Theorem C says how much that state costs, and together they give a gap for the whole spectrum that is three times Theorem A's at λ/e = 6 and reaches twice as far. Theorem A is kept as the first, separately computed result; it is weaker than the corollary everywhere. The section on what the bounds mean has the numbers.

## For a reviewer

The computations are done twice and the combinatorial steps are machine-checked, so a reviewer's time is best spent on the few paragraphs of analysis that nothing else covers. In order of how much rests on them:

1. **Lemma 1, steps 1, 2 and 5** (about half a page). Is complex conjugation a real structure on the gauge-invariant cutoff space, commuting with the Casimirs and anticommuting with the generators? Does the reflection preserve the cell space and commute with the cutoff and the on-site term? After compression, is the bond exactly −Σ (ΠCΠ) ⊗ R(ΠCΠ)R with each factor real and symmetric or antisymmetric, which is what the library's ring structure asks for? The algebra of steps 3 and 4 is in Lean and need not be rechecked.
2. **Lemma 2 (ii) and (iii).** Is the kernel of the midpoint penalty the ladder space, and do the two half-link electric terms add up to the full one there?
3. **Lemma 5.** Three lines. Is the sector penalty an on-site term of the kind Lemma 1 allows, and is its sum L(1 − c) on the constrained space?
4. **Lemma 3.** The operator inequality H ≥ A ⊕ B, and the count of one basis vector per admissible labeling.
5. **The corner formula** in the section on the plaquette matrix elements. Is it the right transcription of the cited sources? It now agrees, configuration by configuration, with the formula printed for the plaquette chain in arXiv:2303.14264, and it is tested; it is still not derived here.
6. **Lemma 4 and the limit of infinite cutoff.**

Not needed: Lemma 6 and the purity recurrence (Lean), and the numerics (two implementations each), unless you want to rerun them from the bundle.

What I would most like to be told: prior work that already contains these bounds or makes them easy; a flaw in passing from bounds uniform in the cutoff to the Hamiltonian without cutoff; and whether the statements, for a ladder, are of interest to anyone working on lattice gauge theory.

## Setting and statements

**The ladder.** The periodic ladder on L plaquettes has vertices (x, bottom) and (x, top) for x in Z/L, leg links b(x) and t(x) from rung x to rung x+1, and rung links r(x) from bottom to top. The Hilbert space is the space of functions on SU(2)^(3L), square integrable for Haar measure, that are invariant under gauge transformations at the 2L vertices. C(ℓ) is the Casimir of link ℓ (minus the Laplacian on that factor, with eigenvalue j(j+1) on the spin-j part), and U(p) = b(x) r(x+1) t(x)⁻¹ r(x)⁻¹ is the holonomy of plaquette x.

**Hamiltonian.** H(L, λ) = e′ Σ over links of C(ℓ) − (λ/2) Σ over plaquettes of tr U(p), with e′ = 4e/3 and e = 1, so one unit of fundamental flux on a link costs 1. This is the Kogut–Susskind Hamiltonian restricted to gauge-invariant states, with no cutoff on the flux. For a cutoff J, Π(J) is the projection onto states with every link at spin at most J; the compression of H to its range is finite dimensional.

**Winding charge.** c = (−1)^(2j(b(x)) + 2j(t(x))) does not depend on x on gauge-invariant states and commutes with H (see Lemma 5). States with c = −1 carry an odd amount of flux around the ring.

**Theorem A (claimed).** For every λ in \[0, 6\] and every even L ≥ 2, H(L, λ) has a nondegenerate lowest eigenvalue and a gap above it of at least g(λ), where g is the step function with 240 steps recorded in `LadderIntervals.lean`: at least 1.084 on \[0, 0.7\], 1.070 on \[0.7, 1.5\], 0.966 on \[1.5, 2\], 0.817 on \[2, 2.5\], 0.651 on \[2.5, 4\] and 0.387 on \[4, 6\].

**Theorem B (claimed).** For every λ in \[0, 12\] and every even L ≥ 2, the restriction of H(L, λ) to the sector c = +1 has a nondegenerate lowest eigenvalue and a gap above it of at least g₊(λ), where g₊ is the step function with 760 steps recorded in `LadderEvenIntervals.lean`: at least 2.82 on \[0, ½\], 2.58 on \[½, 1\], 2.26 on \[1, 2\], 2.03 on \[2, 3\], 1.86 on \[3, 4\], 1.70 on \[4, 5\], 1.55 on \[5, 6\], 1.38 on \[6, 8\], 1.21 on \[8, 10\] and 1.03 on \[10, 12\].

On each step the bound is log r / β for rational r and β written in the Lean file.

**Theorem C (claimed): string tension.** Write E₊(L, λ) and E₋(L, λ) for the lowest eigenvalues of H(L, λ) in the sectors c = +1 and c = −1. For every λ in \[0, 12\] and every even L ≥ 2,

E₋(L, λ) − E₊(L, λ) ≥ σ(λ) · L,

where σ is the step function with 180 steps recorded in `TensionIntervals.lean`: at least 0.99 on \[0, ½\], 0.963 on \[½, 1\], 0.887 on \[1, 2\], 0.810 on \[2, 3\], 0.748 on \[3, 4\], 0.700 on \[4, 5\], 0.664 on \[5, 6\], 0.614 on \[6, 8\], 0.582 on \[8, 10\] and 0.558 on \[10, 12\]. So a flux line wound once around the ring costs energy at least proportional to its length. At λ = 0 the exact cost is 1 per plaquette.

**Corollary (claimed): the whole spectrum.** For every λ in \[0, 12\] and every even L ≥ 2, the ground state of H(L, λ) on all gauge-invariant states is nondegenerate and lies in the sector c = +1, and the gap above it is at least min(g₊(λ), Lσ(λ)). For L ≥ 4 this is g₊(λ). For L = 2 it is at least 1.98 on \[0, ½\], 1.92 on \[½, 1\], 1.77 on \[1, 2\], 1.62 on \[2, 3\], 1.49 on \[3, 4\], 1.40 on \[4, 5\], 1.32 on \[5, 6\], 1.22 on \[6, 8\], 1.16 on \[8, 10\] and 1.03 on \[10, 12\]. In particular the gap is above 1 for every λ in \[0, 12\] and every even L. Proof: Theorem B bounds the gap inside c = +1, Theorem C puts every level of c = −1 at least Lσ above the lowest level of c = +1, and the two combine by the Lean lemma `gapGT_sum`. That the gap is above 1 on the whole range is itself a Lean theorem, full\_gap\_gt\_one, whose hypotheses are those of the two certificate lists. This supersedes Theorem A on its whole range: at λ = 6, for example, Theorem A gives 0.387 and the corollary gives 1.32.

**Remarks.** Theorem A is kept because it was obtained first and by a separate computation; it is consistent with the corollary and weaker than it wherever both apply. The statements are called claimed because their proofs rest on lemmas that no person has read; what is and is not machine-checked is set out in the next section.

## Proof chain and what rests on what

Fix a flux cutoff J.

1. Lemma 1 (split-link positivity): cutting every leg link at its midpoint and adding a Gauss-law penalty μ at the midpoints gives, at cutoff J, a reflection-positive ring in the sense of the CertifiedGaps library, for every μ ≥ 0 and λ ≥ 0.
2. The library proves three moment inequalities for the partition functions of every such ring.
3. Lemma 2 (penalty limit): as μ → ∞ the partition functions converge to those of the cutoff-J ladder, and the inequalities survive the limit. Lemma 5 (winding sector): the same holds for each winding sector separately.
4. Lemma 3 (truncation inequality) and a trial vector give bounds on the two seed purities, at 2 and 4 plaquettes, that hold for every J at once. Lemma 4 extends them from a point to an interval of λ.
5. The library's abstract theorem turns the seeds into a nondegenerate lowest level and a gap at every even L ≥ 2, with a bound that does not depend on J.
6. Limit: for fixed L the eigenvalues at cutoff J converge to those of H as J → ∞, so the bound holds for H.

| Part | How it is supported |
| --- | --- |
| Step 2, and the abstract theorem of step 5 | Lean theorems of the upstream library |
| Step 5 applied to each interval | Lean, in this project: a chain certificate per interval, checked by the kernel, together with the fact that the intervals tile the range (`LadderIntervals.lean` for Theorem A, `LadderEvenIntervals.lean` for Theorem B). The two seed inequalities stay hypotheses of those Lean theorems |
| The seed inequalities of step 4 | Rigorous numerics, by two independently written implementations for each theorem |
| Lemmas 1 to 5 and step 6 | Proofs on paper in this note, each with a numerical test. No person has read them |
| The plaquette matrix elements used in step 4 | A cited formula, checked against constructions and identities that use no 6j symbol |

Theorem C uses steps 1 to 3 and the same numerical ingredients as step 4, and replaces step 5 by Lemma 6, which turns bounds on two plaquettes into a lower bound on the cost of winding at every even length. Lemma 6 is a Lean theorem of this project. Its four numerical inputs on each coupling interval are computed by two implementations; the arithmetic that combines them into σ is checked by the Lean kernel on each of the 180 intervals (TensionIntervals.lean), so the four inputs are hypotheses of a Lean theorem in the same way as the seeds of Theorems A and B.

Trusted software: the Lean kernel and Mathlib, IntervalArithmetic.jl, FLINT and Arb. Not trusted: the eigenvalue and Lanczos routines (any vectors give valid bounds) and the script that produces the chain certificates (the kernel checks them).

## Lemma 1: split-link positivity

**The split model.** Cut the leg link b(x) at its midpoint into b″(x), from the vertex (x, bottom) to the midpoint, and b′(x+1), from the midpoint to (x+1, bottom). Cut t(x) into t″(x) and t′(x+1) in the same way. Cell x consists of the five links b′(x), b″(x), t′(x), t″(x), r(x). Its space K is the space of square-integrable functions of these five group elements that are invariant under gauge transformations at the two vertices of rung x. The split space on L cells is the L-fold tensor product of K. No invariance is imposed at the midpoints.

**Generators.** For a link variable u write (L(h)ψ)(u) = ψ(h⁻¹u) and (R(h)ψ)(u) = ψ(uh). Let Sᴸ(a) and Sᴿ(a), a = 1, 2, 3, be the self-adjoint generators: L(exp(−iθσ(a)/2)) = exp(−iθ Sᴸ(a)), and the same for R. The sum over a of Sᴸ(a)² equals the sum of Sᴿ(a)² and is the Casimir C of the link. A gauge transformation h at the midpoint of b(x) sends the pair (b″(x), b′(x+1)) to (b″(x)h⁻¹, h b′(x+1)). On functions it is generated by G(a) = Sᴿ(a) on b″(x) plus Sᴸ(a) on b′(x+1).

**Split Hamiltonian.** Let N ≥ 0 be the sum of G(a)² over a and over all 2L midpoints, and let Ũ(p) be the plaquette holonomy written with b(x) = b″(x) b′(x+1) and t(x) = t″(x) t′(x+1). Then

H-split(λ, μ) = (e′/2) Σ over half-links of C + e′ Σ over rungs of C − (λ/2) Σ over plaquettes of tr Ũ(p) + μN.

Expanding G(a)² gives H-split = Σ o(x) + Σ h(x, x+1) with

o = (e′/2 + μ)(C(b′) + C(b″) + C(t′) + C(t″)) + e′ C(r),

h(x, x+1) = 2μ Σ over a of \[ Sᴿ(a) on b″(x) ⊗ Sᴸ(a) on b′(x+1) + Sᴿ(a) on t″(x) ⊗ Sᴸ(a) on t′(x+1) \] − (λ/2) tr Ũ(p(x)).

**Statement.** Let Π be the projection of K onto the states with all five Casimirs at most J(J+1). For every J, μ ≥ 0 and λ ≥ 0 there is an orthonormal basis of ΠK in which o is real symmetric, a real symmetric involution R commutes with o, and the compressed bond is −Σ C(α) ⊗ (R C(α) R) for ten real matrices C(α), six antisymmetric and four symmetric. This is the library's `RPRing` structure, and its ring Hamiltonian on L cells is the compression of H-split(λ, μ) to cutoff J.

**Proof.**

Step 1, the real structure. Let K₀ be complex conjugation of functions. Translations L(h) and R(h) map real functions to real functions, so K₀ exp(−iθS) K₀ = exp(−iθS) for each generator S. The left side is exp(+iθ K₀SK₀), hence K₀SK₀ = −S. So K₀ commutes with every Casimir, with Π, with every iS(a), and with multiplication by any real function. K₀ is an antiunitary involution preserving ΠK, so ΠK has an orthonormal basis of real functions. In that basis every operator commuting with K₀ is a real matrix. Hence o is real symmetric, and each iS(a) is real and, being anti-Hermitian, antisymmetric.

Step 2, the reflection. Define ρ on cell configurations by ρ(b′, b″, t′, t″, r) = (b″⁻¹, b′⁻¹, t″⁻¹, t′⁻¹, r) and Rψ = ψ∘ρ. Since ρ is an involution preserving Haar measure, R is a unitary involution, and it maps real functions to real functions, so it is real symmetric. A vertex gauge transformation g at (x, bottom) sends (b′, b″, r) to (b′g⁻¹, gb″, gr); applying ρ before or after gives the same result, and the same holds at the top vertex, so R preserves K. Inversion and permutation of group factors preserve Laplacians, so R C(b″) R = C(b′), R C(t″) R = C(t′) and R C(r) R = C(r). Hence R commutes with o and with Π.

Step 3, the penalty term. For a cell configuration c, (R R(h on b″) R ψ)(c) is ψ evaluated at ρ applied to ρ(c) with its b″ entry b′⁻¹ replaced by b′⁻¹h. That is c with b′ replaced by h⁻¹b′. So R R(h on b″) R = L(h on b′), and therefore R Sᴿ(a on b″) R = Sᴸ(a on b′) for each a; the same holds for t. Put D(a) = √(2μ) i Sᴿ(a on b″) and D′(a) = √(2μ) i Sᴿ(a on t″). Then −D(a) ⊗ (R D(a) R) = 2μ Sᴿ(a on b″) ⊗ Sᴸ(a on b′), which is the penalty part of h. This uses μ ≥ 0.

Step 4, the plaquette. The SU(2)-valued function P = b″⁻¹ r t″ on a cell is invariant under the two vertex gauge transformations, and P∘ρ = b′ r t′⁻¹ =: Q. By cyclicity of the trace, tr Ũ(p(x)) = tr(Q P⁻¹) with P taken on cell x and Q on cell x+1. Write P = p₀ + i p·σ and Q = q₀ + i q·σ with real components. Since P⁻¹ = p₀ − i p·σ, tr(Q P⁻¹) = 2 Σ over k = 0..3 of q(k) p(k). All four signs are plus. Let M(k) be multiplication by p(k) on K. It commutes with K₀ and is self-adjoint, so it is real symmetric, and R M(k) R is multiplication by p(k)∘ρ = q(k). Therefore −(λ/2) tr Ũ(p(x)) = −Σ over k of (√λ M(k)) ⊗ R(√λ M(k))R. This uses λ ≥ 0.

Step 5, the cutoff. Steps 3 and 4 give h = −Σ C(α) ⊗ (R C(α) R) on K ⊗ K with C(α) running over D(a), D′(a) and √λ M(k). Because Π commutes with R, (Π⊗Π) h (Π⊗Π) = −Σ (ΠC(α)Π) ⊗ R(ΠC(α)Π)R, and the compressions keep their reality and symmetry type. ∎

**In Lean: the algebraic core.** The realistic way for this lemma to be wrong is a slip of orientation or sign in steps 2 to 4, so those identities are checked in `Lemma1Algebra.lean`, for an arbitrary group where the group plays no role:

- ρ is an involution and commutes with the gauge transformations at both vertices (`rho_rho`, `rho_gaugeBot`, `rho_gaugeTop`), so R preserves the gauge-invariant functions;
- R ∘ (right translation by h in b″) ∘ R is left translation by the same h in b′, and likewise for t (`refl_rightBpp_refl`, `refl_rightTpp_refl`); this is the plus sign of step 3;
- P and Q are invariant under the vertex gauge transformations and P∘ρ = Q (`P_gaugeBot`, `P_gaugeTop`, `Q_gaugeBot`, `Q_gaugeTop`, `P_rho`); conjugating multiplication by a function with R gives multiplication by the function composed with ρ (`refl_mul_refl`);
- the plaquette holonomy with the legs rejoined is conjugate to Q of one cell times the inverse of P of the previous one (`plaquette_eq_conj`);
- for P, Q in SU(2), tr(Q P⁻¹) = 2(q₀p₀ + q₁p₁ + q₂p₂ + q₃p₃), real and with all four signs plus (`trace_mul_inv_su2`).

Not in Lean: the analytic part, namely that complex conjugation is a real structure commuting with the Casimirs and anticommuting with the generators, that inversion and permutation of the variables preserve Haar measure and the Laplacians, and that compressing by Π preserves the structure. These are standard facts about L² of a compact group.

## Lemma 2 (penalty limit) and Lemma 5 (winding sector)

Notation: Z(L, β) is the trace of exp(−βH) for the cutoff-J ladder on L plaquettes; the cutoff is suppressed where it plays no role. W is half the sum of tr U(p) over the L plaquettes, so H = H₀ − λW with H₀ the electric term. Since |tr U| ≤ 2 pointwise, each plaquette contributes norm at most 1 to W, so ‖W‖ ≤ L, and the same holds for compressions.

**Lemma 2 (penalty limit).** Fix J, L, λ ≥ 0 and β > 0. Let A be the compression of H-split(λ, 0) to cutoff J on the split space, and N the midpoint penalty. Then (i) N commutes with A; (ii) the kernel of N is the space of the cutoff-J ladder, and A restricted to it is H at cutoff J; (iii) the trace of exp(−β(A + μN)) converges to Z(L, β) as μ → ∞; (iv) the three moment inequalities of the library hold for the functions Z(L, β).

Proof. (i) N is built from generators of midpoint gauge transformations. The electric term, the plaquette holonomies written through the products b″b′ and t″t′, and the Casimirs defining the cutoff are all invariant under those transformations. (ii) A function is killed by N exactly when it is invariant under every midpoint gauge transformation, that is, when it depends on each pair (b″, b′) only through the product b = b″b′. This identifies the kernel with the ladder space, isometrically for Haar measure. For f(b″b′), bi-invariance of the Laplacian gives C(b″)f = C(b′)f = (Cf)(b″b′), so the two half-link terms (e′/2)C add up to e′C(b), the cutoffs agree, and A restricts to H at cutoff J. (iii) On the finite-dimensional cutoff space A and N commute, so the trace splits over the eigenvalues ν of N as the sum of exp(−βμν) times the trace of exp(−βA) on that eigenspace. Every term with ν > 0 tends to zero. (iv) By Lemma 1 and the library, the inequalities hold for the left side of (iii) at every μ. They are non-strict inequalities between continuous expressions in finitely many values of Z, so they pass to the limit. ∎

The three inequalities are: Z(2n) ≤ Z(n)²; 2(Z(2n)² − Z(4n)) ≤ (Z(n)² − Z(2n))²; and Z(q) ≤ Z(p)^(q/p) for even p ≤ q; each at fixed β.

**The winding charge.** On the spin-j part of the functions of a link variable u put σ(u) = (−1)^(2j). At a vertex the three spins sum to an integer, so on gauge-invariant states σ(b(x−1))σ(b(x)) = σ(r(x)) = σ(t(x−1))σ(t(x)), and therefore c = σ(b(x))σ(t(x)) does not depend on x. The electric term is diagonal in the spins, and each plaquette operator changes b(x) and t(x) by ±½ together, so c commutes with H. States with c = −1 carry an odd amount of flux around the ring. Write Z₊ and Z₋ for the partition functions of the sectors c = +1 and c = −1.

**Lemma 5 (winding sector).** In the split cell let q = \[1 − σ(b″)σ(t″)\]/2 + \[1 − σ(b′)σ(t′)\]/2. (a) For every ν ≥ 0 the ring with on-site term o + νq and the same bond term satisfies the conclusion of Lemma 1. (b) For every cutoff J, the three moment inequalities hold for the functions Z₊(L, β) alone, and likewise for Z₋ alone.

Proof. (a) σ(u) is a function of the Casimir of u, so q commutes with the cutoff projection Π and with complex conjugation K₀ (each spin-j part of L²(SU(2)) is closed under complex conjugation). So q is real symmetric in the basis of Lemma 1. The reflection ρ exchanges b′ with the inverse of b″ and t′ with the inverse of t″, and inversion preserves each spin-j part, so RqR = q. The bond term is unchanged. (b) The sum of q over the cells is a function of half-link Casimirs, so it commutes with the midpoint penalty N, and the proof of Lemma 2 applies with A replaced by A + ν Σq. On the kernel of N the two halves of a leg carry the same spin, so with the vertex relation above σ(b″)σ(t″) = σ(b′)σ(t′) = c in every cell, and Σq = L(1 − c). Hence the moment inequalities hold for Z₊(L, β) + exp(−2βνL) Z₋(L, β) at every ν ≥ 0. Let ν → ∞: the second term tends to zero for each L, and the inequalities pass to the limit as in Lemma 2 (iv). Replacing 1 − σσ by 1 + σσ in q gives the statement for Z₋. ∎

In Lean: closure of the inequalities under limits is the upstream lemma `SpatialMomentBounds.of_tendsto`; statement (iii) of Lemma 2 for commuting diagonal data is `PenaltyLimit.lean`. Not in Lean: the simultaneous diagonalisation behind (iii), statement (ii), and Lemma 5.

## Lemmas 3 and 4, the assembly, and the limit

**Lemma 3 (truncation inequality).** Fix j\* and c > 0. Let P project onto states with every link at most j\*, and let Q′ project onto states with every link at most j\* + ½ and some link above j\*. For every cutoff J ≥ j\*, every λ ≥ 0 and β > 0,

Z(L, β) ≤ Tr over ran P of exp(−β \[PHP − (λ²/c) P W Q′ W P\]) + exp(β(λL + c)) · \[S − S(j\*)\],

where S(j) is the sum over admissible labelings with every spin at most j of exp(−β e′ Σ j(j+1)), and S is the sum over all admissible labelings. The right side does not depend on J. The same holds for Z₊ with P, Q′, the trace and the labelings restricted to the sector c = +1.

Proof. Work at cutoff J with Q = Π(J) − P. Step 1. H₀ is diagonal in the spin-network basis, so it commutes with P and Q, and H = PHP + QHQ − λ(PWQ + QWP). Expanding the square of √c Q − (λ/√c) QWP gives 0 ≤ cQ − λ(PWQ + QWP) + (λ²/c) PWQWP. Hence H ≥ A ⊕ B with A = PHP − (λ²/c)PWQWP on ran P and B = QHQ − cQ on ran Q. Step 2. Each plaquette operator changes each of its four links by ±½, so W maps ran P into states with links at most j\* + ½, and PWQWP = PWQ′WP whenever J ≥ j\* + ½. If J = j\* then Q = 0 and A is larger still. Step 3. On ran Q, QHQ ≥ QH₀Q − λL, so B ≥ H₀ − (λL + c). Step 4. If X ≥ Y are Hermitian matrices then Tr exp(−βX) ≤ Tr exp(−βY), by min–max. Applying this to H ≥ A ⊕ B and to step 3 bounds Z by the first term plus exp(β(λL + c)) times the trace of exp(−βH₀) on ran Q. Step 5. The gauge-invariant space has an orthonormal basis with exactly one vector per admissible labeling (spin networks on a graph whose vertices are all trivalent, where the intertwiner is unique), and H₀ is e′ Σ j(j+1) on it. So the last trace is S(J) − S(j\*) ≤ S − S(j\*). For the sector: P, Q, H₀ and W commute with c, so every step restricts to c = +1. ∎

In Lean upstream: the trace monotonicity of step 4 (`sum_le_sum_of_posSemidef`). Computed: S(j) on 2 plaquettes, and S bounded by S(8) plus a remainder for labelings with some link above 8, with the triangle and sector constraints dropped: 3L · τ · (Σ over all spins of the link weight)^(3L−1), where τ is a geometric bound on the weights above 8.

**Lemma 4 (interval).** Fix an interval \[λ(a), λ(b)\] of width d, a unit vector ψ on 4 plaquettes supported on links at most J(trial), and numbers ℓ(a), ℓ(b) with log Z(2, β) ≤ ℓ at the two endpoints for every cutoff. Put θ = ⟨ψ, H(λ(a))ψ⟩ and w = ⟨ψ, Wψ⟩. For λ = λ(a) + td with t in \[0, 1\] and every cutoff J ≥ max(j\*, J(trial)):

(a) the ground energy on 4 plaquettes is at most θ − tdw; (b) log Z(2, β) ≤ (1 − t)ℓ(a) + tℓ(b); (c) the spatial purity Z(4, β)/Z(2, β)² is at least exp(−β(θ − tdw) − 2\[(1 − t)ℓ(a) + tℓ(b)\]); (d) the thermal purity Z(4, 2β)/Z(4, β)² is at least the square of that. Both exponents are affine in t, so each purity is bounded below on the whole interval by the smaller of its two endpoint values. The same holds in the sector c = +1 with ψ in the sector and Z replaced by Z₊.

Proof. (a) H(λ) = H(λ(a)) − tdW, so the Rayleigh quotient of ψ is θ − tdw exactly; ψ lies in every cutoff space with J ≥ J(trial), and its Rayleigh quotient there is the same. (b) For Hermitian X, log Tr exp(X) is the supremum over density matrices ρ of Tr(ρX) minus Tr(ρ log ρ) (Gibbs variational principle). With X = −β(H₀ − λW) each term in the supremum is affine in λ, so λ → log Z(2, β) is convex, and a convex function lies below its chord. (c) Z(4, β) ≥ exp(−βE₀) with E₀ the ground energy, then (a) and (b). (d) Z(4, 2β) ≥ exp(−2βE₀), and Z(4, β) ≤ Z(2, β)², which is the first moment inequality (Lemma 2 for all sectors, Lemma 5 for one sector). ∎

Any unit vector gives a valid line in (a). The certificates of Theorem A take the Lanczos vector at λ(a); those of Theorem B take it at the midpoint of the interval, which quarters the loss at the endpoints.

In Lean: the inequality that a quantity bounded this way is at least the smaller endpoint value (`Interval.lean`). Not in Lean: the convexity in (b).

**Assembly.** For each interval the certificate fixes β, j\*, J(trial) and c. Lemma 3 at the two endpoints supplies ℓ(a) and ℓ(b). By Lemma 4 the two seed defects bound the purities at n = 2 for every λ in the interval and every cutoff at least max(j\*, J(trial)). By Lemma 2 (Theorem A) or Lemma 5 (Theorem B) the spectra at even L satisfy the hypotheses of the library's abstract theorem `gapGT_of_chainCertificate`, which then gives a nondegenerate lowest level and the gap at every even L ≥ 2, with a bound that does not depend on the cutoff.

**The limit J → ∞.** Fix L and λ. H₀ is diagonal with eigenvalues tending to infinity and finite multiplicities, and W is bounded, so H has compact resolvent, and finite combinations of spin-network states form a core. The operators at cutoff J are compressions of H to an increasing family of subspaces whose union is that core, so by min–max the k-th eigenvalue at cutoff J decreases to the k-th eigenvalue of H. The difference of the first two eigenvalues of H is therefore a limit of numbers at least the bound. The same argument applies inside a sector. ∎

## Lemma 6: a string tension from the moment inequalities

Write E₊(L) and E₋(L) for the lowest eigenvalue of H on L plaquettes in the sectors c = +1 and c = −1, and Z₊, Z₋ for the partition functions of the sectors, all at one flux cutoff.

**Lemma 6.** Let β > β₁ > 0. Suppose ω ≤ E₋(2); log Z₊(2, β₁) ≤ ℓ₁; E₊(2) ≤ θ; and 1 − ε ≤ Z₊(4, β)/Z₊(2, β)², with ε < 1 and f(ε) ≤ ½, where f(ε) = ε²/(2(1 − ε)²). Then for every even L ≥ 2

E₋(L) − E₊(L) ≥ σL, with σ = ω/2 − (ℓ₁/2 + βθ/2 + D)/(β − β₁) and D = −¼ log(1 − ε) − ¼ log(1 − f(ε)).

In words: an odd amount of flux wound around a ring of length L costs at least σL. This is a lower bound on the string tension.

Proof. By Lemma 5 the three moment inequalities hold for Z₊ alone and for Z₋ alone.

(i) The odd sector. For every b > 0, Z₋(L, b) ≤ Z₋(2, b)^(L/2). The left side is at least exp(−bE₋(L)), and the right side is at most (N exp(−bω))^(L/2), with N the dimension of the odd sector on 2 plaquettes at the cutoff. Taking logarithms and dividing by b gives E₋(L) ≥ (L/2)ω − (L/2)(log N)/b for every b, hence E₋(L) ≥ (L/2)ω.

(ii) The even sector at β₁. Z₊(L, β₁) ≤ Z₊(2, β₁)^(L/2), so log Z₊(L, β₁) ≤ (L/2)ℓ₁.

(iii) The even sector at β. Write P(n) = Z₊(2n, β)/Z₊(n, β)². The first inequality says P(n) ≤ 1, and the squaring inequality is equivalent to 1 − P(2n) ≤ f(1 − P(n)). From 1 − P(2) ≤ ε we get 1 − P(4) ≤ f(ε), and since f(x) ≤ x for 0 ≤ x ≤ ½, 1 − P(2^k) ≤ f(ε) for every k ≥ 2. Because log Z(2n) = 2 log Z(n) + log P(n), induction gives log Z₊(2^(j+2), β) ≥ 2^(j+1) log Z₊(2, β) + 2^j log(1 − ε) + (2^j − 1) log(1 − f(ε)). For even L ≤ q = 2^(j+2) the third inequality, Z₊(q) ≤ Z₊(L)^(q/L), gives log Z₊(L, β) ≥ (L/q) log Z₊(q, β) ≥ L(½ log Z₊(2, β) − D). Finally log Z₊(2, β) ≥ −βE₊(2) ≥ −βθ.

(iv) Comparing the two temperatures. Each term of Z₊(L, β₁) is exp(−β₁E) = exp(−βE) exp((β − β₁)E) ≥ exp(−βE) exp((β − β₁)E₊(L)). So Z₊(L, β₁) ≥ exp((β − β₁)E₊(L)) Z₊(L, β), and with (ii) and (iii), (β − β₁)E₊(L) ≤ (L/2)ℓ₁ + L(βθ/2 + D).

(v) Subtract the bound of (iv) from the bound of (i). ∎

**In Lean.** The whole of Lemma 6, for any two families of spectra that satisfy the moment inequalities: theorem `string_tension` in `StringTension.lean`, with only the three standard axioms. The same file has `gapGT_sum`: a gap inside one sector together with a lower bound on every level of the other sector gives a gap for the two sectors together. TensionIntervals.lean applies the lemma to the 180 coupling intervals: each entry holds rational bounds on ω, ℓ₁ and θ at the two endpoints, one ε for the interval, and σ. The kernel checks that σ is at most the bound of the lemma at both endpoints, with −log(1 − x) replaced by a rational upper bound proved in the same file, and that the entries tile \[0, 12\]. The theorem tension\_on\_interval then gives E₋(L) − E₊(L) ≥ σL at every point of an interval, from the four inputs interpolated linearly between the endpoints. FullSpectrum.lean combines it with the certificates of Theorem B.

**The inputs on a coupling interval, for every cutoff.** ω: the proof of Lemma 3 gives H ≥ A ⊕ B, so E₋(2) is at least the smaller of the lowest eigenvalue of A in the odd sector and the smallest electric energy of an odd labeling with a link above j\*, minus (2λ + c); this holds for every cutoff at least j\*. E₋(2) is concave in λ, being the lowest eigenvalue of H₀ − λW, so on an interval it lies above the chord through its endpoint lower bounds. ℓ₁: Lemma 3 at the endpoints and the chord of Lemma 4 (b). θ: the affine trial energy of Lemma 4 (a), on 2 plaquettes. ε: the spatial seed defect of Theorem B at inverse temperature β, one value for the whole interval. With these, σ is an affine function of the position in the interval, so it is at least the smaller of its two endpoint values. The bound σL does not depend on the cutoff, and E₊(L), E₋(L) at cutoff J decrease to their values without cutoff, so the inequality holds for H itself.

## Tests of the lemmas

None of these tests is part of a proof. Each is chosen so that a specific way the lemma could be wrong would show up, and where possible a control shows that the test is able to fail.

| Lemma | What would falsify it | Test | Result |
| --- | --- | --- | --- |
| 1 | An orientation or sign slip: R sending Sᴿ(b″) to minus Sᴸ(b′), or Q being the adjoint of P∘ρ, which would turn three of the four plus signs into minus | Pointwise identities on 2,000 random SU(2) configurations: loop = 2 Σ p(k)q(k), Q = P∘ρ, gauge covariance (`lemma1_orientation_test.py`) | hold to 10⁻¹⁵; the adjoint variant fails by order one |
| 1 | The same, at the level of matrices | Cell matrices at cutoff ½ (dimension 41) and cutoff 1 (dimension 813), built by exact quadrature on the binary icosahedral group with no 6j symbols and no fitted reflection (`lemma1_cell_test.py`): R a unitary involution, R G(b″) R = G(b′), R M(k) R = multiplication by q(k), R o R = o, all real with the stated symmetry | hold to 10⁻⁹ or better; the wrong-sign pairings fail by order one |
| 1, 2 | The split ring not reproducing the ladder | Two-cell ring assembled from those matrices with a midpoint penalty, against the spin-network Hamiltonian (`cell_ring_check.py`) | all 8 levels at cutoff ½ and the lowest 6 of 49 at cutoff 1 agree to 3 × 10⁻¹³ |
| 2 | A moment inequality failing for the gauge-invariant spectra | Direct evaluation at 18 parameter sets, cutoff ½ up to 12 plaquettes and cutoff 1 up to 4 (`moment_check.py`) | 18 of 18 hold |
| 3 | A higher cutoff whose partition function exceeds the right side | L = 2; j\* = ½, 1, 3/2; c = 2, 6, 12; λ = 0.5, 2, 5; β = 1.5, 4; every cutoff from j\* to 3 (`lemma3_bracket_test.py`) | 0 violations in 54 cases, tightest slack 3 × 10⁻⁷ in the logarithm; a control with the correction term dropped is violated in 3 cases |
| 4 | log Z(2, β) not convex in λ | Second differences on 57 couplings from 0 to 14 at four values of β (`explore/horizon.py`) | all positive, smallest 0.0015 |
| 5 | A moment inequality failing inside a winding sector | The three inequalities for each sector separately, 18 cases: cutoff ½ up to 12 plaquettes, cutoff 1 up to 6 (`explore/sector_moment_check.jl`) | hold in 18 of 18 for c = +1 and for c = −1; for the twisted trace Z₊ − Z₋, about which nothing is claimed, they fail in 15 of 18 |

Not tested: Lemma 1 with constructed matrices above cutoff 1 (the proof does not depend on the cutoff), and the affine trial energy in Lemma 4, which is an identity.

**Lemma 6.** What would falsify it: a ring on which the winding cost per plaquette is below σ, or on which the lowest even-sector energy per plaquette is above the bound of step (iv). Test (`tension/lemma6_test.py`): at one flux cutoff (3/2) on 2, 4 and 6 plaquettes, 6 couplings and 12 choices of the two temperatures, 72 cases. No violation; the bound of step (iv) is tight, with margins down to 7 × 10⁻⁸, and the energy per plaquette of the odd sector increases with length as step (i) requires (at λ = 2: 0.646, 0.700, 0.709 for 2, 4, 6 plaquettes). Control: with the correction D dropped the bound is violated in 57 of the 72 cases. The lemma itself is machine-checked, so this test is mainly a check that the Lean statement says what the note means.

## The plaquette matrix elements

The computations of step 4 are done in the spin-network basis, one basis vector per admissible labeling of the links by spins. There the plaquette operator changes its four links by ±½ with an amplitude that is a product of four corner factors, one per corner, each a 6j symbol times dimension factors and a sign:

F = (−1)^(a + j(out) + ½ + j′(in)) √((2j(in) + 1)(2j′(out) + 1)) {a j(out) j(in); ½ j′(in) j′(out)},

with a the spin of the third leg at the corner and primes marking the new spins. The source is Burgio, De Pietri, Morales-Técotl, Urrutia and Vergara, hep-lat/9911019, who compute these matrix elements in general. I have not re-derived the formula on paper. It is checked in three ways, none of which uses a 6j symbol in its target.

**A second printed source, for exactly this geometry.** The supplemental material of Yao, arXiv:2303.14264, citing Klco, Stryker and Savage (2020) and ARahman, Lewis, Mendicelli and Powell (2021), prints the matrix element of tr U on a plaquette chain in one piece: a factor (−1)^j for each of the four external links, a factor (−1)^(j + J) √((2j + 1)(2J + 1)) for each of the four loop links, and four 6j symbols {j(ext) j(k) j(k+1); ½ J(k+1) J(k)}, with lower case for the old spins and capitals for the new. The product of the four corner factors F is the same expression: every loop link is the outgoing link at one corner and the incoming link at the next, so the square roots and the signs collect into the product over loop links, the four half-integers in the exponents add up to 2, and the 6j symbols coincide. The code confirms it exactly. For every local configuration in the operator tables (238,944 on 2 plaquettes at cutoff 9/2, 1,386,328 on 3 plaquettes at cutoff 7/2, 133,900 on 4 plaquettes at cutoff 5/2) the sign and the rational square of the entry equal those of the printed formula evaluated in one piece; with the corner sign rule switched off, 2,348 of 4,580 configurations disagree (`replay/published_formula_test.jl`). So the matrix elements used here are the ones the quantum-simulation literature uses for this model. I took the printed formula from the arXiv text by machine extraction, twice with the same result; a reader should compare it with the paper.

**Spectra against constructions without 6j symbols (cutoff up to 1).**

| Construction | Sizes | Agreement |
| --- | --- | --- |
| Peter–Weyl cell model in the variables (B, T, P) with a midpoint penalty (`su2_plaq.py`) | 2 plaquettes at cutoff ½ and 1; 3 plaquettes at cutoff ½ | spectra agree |
| Cell built by exact quadrature on the binary icosahedral group, in different variables (`lemma1_cell_test.py`, `cell_ring_check.py`) | 2 plaquettes at cutoff ½ (all 8 levels) and cutoff 1 (lowest 6 of 49 levels, ring dimension 660,969) | 3 × 10⁻¹³ |

**Exact identities at the cutoffs the certificates use.** Theorem A uses labels up to 5/2 on 2 plaquettes and up to 2 on 4 plaquettes; Theorem B uses labels up to 7/2 on 2 plaquettes and up to 5/2 on 4 plaquettes. A local configuration means the eight spins around a plaquette together with a move.

| Identity | Sizes | Result | Controls |
| --- | --- | --- | --- |
| Plaquette operators on different plaquettes commute, because they are multiplication operators. With a cutoff this holds exactly on states whose labels are at most the cutoff minus 1 (`replay/commutator_test.jl`) | 2 plaquettes at cutoffs 7/2 and 9/2; 3 plaquettes at cutoffs 3 and 7/2. This covers every local configuration with labels up to 7/2 on 2 plaquettes and up to 5/2 between neighbouring plaquettes | largest commutator entry 9 × 10⁻¹⁷ | Sign of one local configuration flipped: detected for 59,862 of 59,864 (2 plaquettes, labels up to 7/2), for 28,982 of 28,984 (3 plaquettes, labels up to 2), and for 3,000 of a sample of 3,000 out of 130,412 (3 plaquettes, labels up to 5/2). The two missed are the move out of the vacuum and its reverse, which only change the sign of one basis vector; the spectrum is exactly unchanged. One configuration rescaled by 5%: detected in every case. Corner sign rule removed: detected on 3 plaquettes (0.30); not on 2 plaquettes, where the spectrum does not depend on it |
| The functions χ(B) · ∏ χ(U(p)), with B the loop around the ring along the bottom legs (or the top legs), are orthonormal, because these loops are independent and Haar distributed. A single excited plaquette of spin j over a ring loop of spin j(B) has weight (2k+1) / ((2j(B)+1)(2j+1)) on leg label k (`replay/peter_weyl_test.jl`) | 2 plaquettes at cutoff 5/2 (69 vectors), 3 at cutoff 5/2 (225), 4 at cutoff 2 (390) | Gram matrix equals the identity to 5 × 10⁻¹⁶; weights exact to 10⁻¹⁶ | One configuration rescaled by 5%: detected in 18 of 60, 25 of 40 and 10 of 20 samples, so coverage is partial. Blind to signs: the run with the corner sign rule removed passes |

**Two evaluations of the formula.** The two implementations of each theorem evaluate the 6j symbols differently (sympy; Racah's sum in exact rationals) and build the basis and operators separately. Their bounds on log Z agree to 2 × 10⁻⁹ or better on every interval of both theorems. This guards against a coding error in either, not against an error in the formula.

**A published special case.** At flux cutoff ½ the sector c = +1 of the ladder is a spin chain, one spin per plaquette, written out by Yao (arXiv:2303.14264, eq. 11): an Ising chain with a longitudinal field whose transverse term carries a factor 1 or −½ for each neighbouring plaquette, according to whether that neighbour is empty or excited. In the units of this note it reads Σ (4n(x) − 2n(x)n(x+1)) − (λ/2) Σ f(n(x−1)) f(n(x+1)) σˣ(x). The operators built here at cutoff ½ have the same spectrum as that chain to 2 × 10⁻¹³, on rings of 2 to 8 plaquettes at λ = 0.5, 2, 6 and 12; with the neighbour factor changed from ½ to 0.45 the spectra differ by 0.016 or more (`replay/ising_map_test.jl`). This ties the normalisation of the electric term and the sizes 1, ½, ¼ of the lowest plaquette amplitudes to an independent source. It is blind to signs, and it says nothing about labels above ½.

**What these checks show and do not show.** The commutator test catches an error of sign or size in any single local configuration within the label range the certificates use. It cannot see a common rescaling of all plaquette operators; the orthonormality test fixes that scale. Neither is a proof of the formula: an error that preserved every commutator and every character norm would pass both. With the spectral agreement up to cutoff 1 and the citation, a wrong matrix element looks unlikely to me, but a derivation on paper is still missing.

## Certificates, Lean, and the replays

**What is in Lean.** For each coupling interval the Lean files hold the interval, the seed inverse temperature β, and a chain certificate: rational upper bounds on the two seed defects and on their images under the recurrence of the purity criterion, ending in a rate r. The kernel checks every certificate and that the intervals tile the range. The theorem `gap_on_interval` is the library's abstract theorem applied to one interval: for any family of spectra that satisfies the moment inequalities and that interval's two seed inequalities, the gap at every even L ≥ 2 exceeds log r / β. For Theorem B there are two more statements: `exists_interval`, every real coupling in \[0, 12\] lies in one of the intervals, and `gap_gt_one_on_interval`, on every interval the rate exceeds 1, checked in rational arithmetic. All of these depend only on the three standard axioms. The seed inequalities themselves are hypotheses in Lean; they are what the numerics establish. For Theorem C the corresponding statements are intervals\_ok, intervals\_tile, exists\_interval and tension\_on\_interval in TensionIntervals.lean, with the four inputs of Lemma 6 as hypotheses, and full\_gap\_gt\_one in FullSpectrum.lean joins the lists of Theorems B and C.

|  | Theorem A | Theorem B |
| --- | --- | --- |
| Range and sector | 0 ≤ λ ≤ 6, all gauge-invariant states | 0 ≤ λ ≤ 12, sector c = +1 |
| Intervals | 240: width 1/80 on \[0, 2\], 1/20 on \[2, 6\] | 760: width 1/320 on \[0, 1\], 1/160 on \[1, 2\], 1/40 on \[2, 6\], 1/20 on \[6, 12\] |
| β | 6 falling to 15/4 | 13/4 falling to 33/20 |
| Cutoffs (j\*, trial vector) | 3/2 and 3/2 up to λ = 2; 2 and 2 beyond | 5/2 and 2 up to λ = 6; 3 and 5/2 beyond |
| Seeds computed by | Python: Arb balls at 160 bits, ball matrix exponential, sympy 6j symbols | Julia: Float64 intervals, approximate eigenvectors with Gershgorin row sums and Courant–Fischer, Racah's sum for 6j symbols |
| Margin added to the seeds | 1 part in 10⁴ | 3 parts in 10⁴ |
| Replayed by | Julia, as in the column to the right | Python: exact integer arithmetic (FLINT) for the similarity transform, Arb balls for scalars, sympy 6j symbols, 26-bit integer trial vectors |
| Replay result | 240 of 240; smallest margin 9.7 × 10⁻⁵ of the defect | 760 of 760; smallest margin 2.98 × 10⁻⁴ of the defect |
| Agreement of the two implementations | bounds on log Z to 3 × 10⁻¹⁰, trial energies to 3 × 10⁻¹⁰ | bounds on log Z to 2 × 10⁻⁹, trial energies to 3 × 10⁻⁹, defects to 1 part in 10⁵ |
| Lean files | `LadderIntervals.lean` | `LadderEven/Defs`, `Part1` to `Part4`, `LadderEvenIntervals.lean`, `LadderEvenGtOne.lean` |
| Certified bound | 1.084 falling to 0.387 | 2.82 falling to 1.03; above 1 everywhere, in Lean |

**Theorem C.** 180 intervals: width 1/20 on \[0, 6\] and 1/10 on \[6, 12\]; β = 20 up to λ = 10 and 16 beyond, β₁ = 3; j\* = 5/2 with trial vectors at cutoff 2 on 4 plaquettes and 3 on 2 plaquettes up to λ = 6, and j\* = 3 with cutoffs 5/2 and 7/2 beyond. The inputs were computed in Julia with interval arithmetic. The certificate takes Julia's bounds on ω, ℓ₁ and θ at the two endpoints moved by 2 × 10⁻⁶ in the safe direction and ε enlarged by 3 parts in 10⁴, and σ is the bound of Lemma 6 evaluated on those rationals and rounded down to four decimals; Lean checks that evaluation. The replay is the Python implementation (exact integers, Arb balls, sympy 6j symbols, integer trial vectors). For every entry it proves the seven inequalities that tension\_on\_interval needs: three bounds at each endpoint and the bound on the defect. Result: 180 of 180, with at least 2.0 × 10⁻⁶ to spare on ω, ℓ₁ and θ and at least 2.9 parts in 10⁴ on ε. The two implementations agree on ω, ℓ₁ and θ to 8 × 10⁻¹⁰, on ε to 5 parts in 10⁶, and on σ to 1.5 × 10⁻⁹. Lean files: StringTension.lean, TensionIntervals.lean, FullSpectrum.lean. After the code changes made for Theorem C, the replay of Theorem A was rerun in full (240 of 240, same margins) and five intervals of Theorem B were recomputed (identical numbers).

**What a replay establishes.** Each replay reads the seeds from the Lean files and proves, with its own code and its own arithmetic, the two inequalities that `gap_on_interval` takes as hypotheses, for every coupling in the interval and every flux cutoff at least the ones used. In both cases the replay was written from the statements of Lemmas 3 and 4 (and 5) and the corner formula, not from the other implementation.

**What the first replay found.** For Theorem A the first replay run passed 238 of 240 intervals. The two failures missed by 6 × 10⁻⁶ and 5 × 10⁻⁷ of the defect, because the seeds had been set only one part in 10⁶ above the computed values, while two valid trial vectors for the same interval give slopes that differ by up to 3 × 10⁻⁸, enough to move the defect by 9 parts in 10⁶. The margin was widened and both theorems now pass in full. The failed run is kept in the bundle.

**What the replays do not make independent.** The mathematics is shared: an error in Lemma 3, 4 or 5 or in the corner formula would pass both implementations. Both were written by the same author, an AI, within two days. The arithmetic libraries are trusted. The replay of Theorem B relies on exact integer matrix products and ball arithmetic; the replay of Theorem A relies on an interval library whose matrix products use directed rounding.

**Where the files are.** Bundle `recon_scripts_v14.zip`: `lean/` (Lean project), `replay/` (Julia machinery, replay of Theorem A, matrix-element tests), `zero_winding/` (Theorem B: tiling, seeds, Lean generator, Python replay, results), tension/ (Theorem C: tiling, inputs, certificate and Lean generator, Python replay, results), `explore/` (numerics), and the Python scripts of the first implementation at the top level.

## What the bounds mean

This section is floating-point numerics, for orientation only. The table gives the lowest excitation energy above the ground state by ring length and winding sector, next to the two certified bounds at the same coupling.

| λ | 2 plaquettes, c = −1 | 2 plaquettes, c = +1 | 4 plaquettes, c = −1 | 4 plaquettes, c = +1 | 6 plaquettes, c = +1 | Theorem A | Theorem B |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0.5 | 1.98 | 3.92 | 3.99 | 4.01 | 4.01 | 1.09 | 2.80 |
| 1 | 1.93 | 3.87 | 3.95 | 4.05 | 4.05 | 1.18 | 2.57 |
| 2 | 1.77 | 3.83 | 3.77 | 4.21 | 4.21 | 0.87 | 2.21 |
| 3 | 1.62 | 3.80 | 3.49 | 4.47 | 4.47 | 0.77 | 2.02 |
| 4 | 1.50 | 3.72 | 3.24 | 4.81 | not computed | 0.64 | 1.85 |
| 6 | 1.33 | 3.53 | 2.91 | 5.62 | not computed | 0.38 | 1.55 |
| 8 | 1.23 | 3.37 | 2.71 | 6.47 | not computed | none | 1.38 |
| 10 | 1.17 | 3.26 | 2.59 | 6.76 | not computed | none | 1.21 |
| 12 | 1.13 | 3.18 | 2.51 | 6.61 | not computed | none | 1.03 |

**Why Theorem A falls with λ.** The smallest gap over all even ring lengths is on 2 plaquettes, and it is a winding state. Its energy falls from 2 at λ = 0 to 1.33 at λ = 6 and 1.09 at λ = 14. On longer rings winding costs more, about 0.8 per plaquette at λ = 6, and from 6 plaquettes on the lowest excitation is a plaquette excitation near 4 whose energy rises with λ. So Theorem A's bound falls because the two-plaquette ring has a light winding state, not because the gap of the long ladder shrinks. Read as a statement about the long ladder it is loose by a factor of about 4 at small λ and more than 10 at λ = 6.

**Why Theorem B is the more useful statement.** Removing the odd-winding sector removes that state. Inside c = +1 the smallest gap over ring lengths is still on 2 plaquettes, but it is between 3.2 and 4 over the whole range, and the certified bound is 70% of it at λ = 0.5, 44% at 6 and 32% at 12.

**The string tension.** The cost of one winding, per plaquette, from the same numerics, next to the certified σ:

| λ | 2 plaquettes | 4 plaquettes | 6 plaquettes | Certified σ |
| --- | --- | --- | --- | --- |
| 1 | 0.964 | 0.989 | 0.990 | 0.960 |
| 2 | 0.887 | 0.942 | 0.951 | 0.883 |
| 4 | 0.749 | 0.811 | not computed | 0.745 |
| 6 | 0.666 | 0.726 | not computed | 0.664 |
| 8 | 0.617 | 0.678 | not computed | 0.612 |
| 10 | 0.585 | 0.648 | not computed | 0.580 |
| 12 | 0.563 | 0.628 | not computed | 0.558 |

The certified value sits just below the two-plaquette cost, as the proof makes it: the bound is half the two-plaquette winding energy minus a small correction for the even sector, between 0.001 and 0.005. The sampled cost per plaquette rises with length (by about a tenth relative to σ at λ = 6 on four plaquettes). These samples do not give a monotonicity theorem for the winding cost. Seeding the odd sector on 4 plaquettes would close most of that distance; it needs a rigorous lower bound on the lowest odd level on 4 plaquettes, which I have not attempted.

**How much the certificates lose.** With exact inputs (the exact two-plaquette partition function and the exact four-plaquette ground energy) the two-plaquette seed scheme would give, for Theorem A, 1.44 at λ = 0.5, 1.04 at 2, 0.68 at 4 and 0.48 at 6; the certificates reach 75% to 95% of that, the loss at small λ being interval width. For Theorem B it would give 2.86 at 0.5, 2.27 at 2, 1.60 at 6 and 1.27 at 10, and the certificates reach 95% or more. The remaining distance to the true gaps is a property of seeding at 2 plaquettes, not of the certificates.

Cutoffs for the numerics: 3 on 2 plaquettes (checked against 4), 5/2 on 4 plaquettes (checked against 2; the values at λ ≥ 10 in the c = +1 column may still move in the second decimal), 3/2 on 6 plaquettes. Files: `explore/gap_scan.jl`, `explore/horizon.py`.

## Prior work, what is new, and open items

**The method.** The purity criterion comes from the OpenAI proof of the periodic spin-one Haldane gap and is formalised in CertifiedGaps (Sirui Lu). Nothing about the criterion is new here.

**Reflection positivity.** That lattice gauge theories are reflection positive, with the plaquettes crossing the reflection plane supplying the positive terms, goes back to Osterwalder and Seiler (1978). The antiferromagnetic form of the midpoint term is the Dyson–Lieb–Simon mechanism (1978). Lemma 1 adapts both to the Hamiltonian ring format of the library; I do not know of a reference that states it in this form. Lemma 5 is elementary, and I have not searched for it specifically.

**Strong-coupling gaps.** A gap uniform in volume for small λ/e is known in several forms: cluster expansions (Osterwalder–Seiler), and perturbation theory for gapped classical lattice systems under relatively bounded perturbations (Yarotsky, math-ph/0412040), which applies with the electric term as the classical part. These results are perturbative in λ/e and, as far as I found, give no explicit bound at λ/e of order one.

**The truncated ladder.** The SU(2) plaquette chain with a flux cutoff is a standard model in the quantum-simulation literature, studied numerically at cutoffs ½ to 3/2 (Yao, arXiv:2303.14264; Ebner, Schäfer and Seidl, arXiv:2401.15184; Zache, González-Cuadra and Zoller, arXiv:2304.02527). Those papers contain numerical gaps on small chains, not bounds uniform in length. Two more recent papers on the truncated chain concern strings: Siew, Chandrasekharan and Bhattacharya (arXiv:2512.11068) map a qubit-regularised plaquette chain to an Ising chain in transverse and longitudinal fields and report a ratio of string tension to glueball mass; John and coauthors (arXiv:2605.05841) observe string dynamics of a truncated SU(2) ladder on a trapped-ion quantum computer. Neither contains a bound. The plain mixed-field Ising chain is one of the families the CertifiedGaps library already certifies at some parameter points. That does not transfer to the ladder with a flux cutoff of ½: by Yao's formula its transverse term depends on the neighbouring spins, so it is a different chain from the qubit-regularised one.

**String tension.** In Euclidean lattice gauge theory the area law for Wilson loops at strong coupling is due to Osterwalder and Seiler, and in lattice Monte Carlo the energy of a flux tube closed around a periodic direction (a torelon) is a standard way to measure the string tension. Theorem C is a lower bound on that energy for the ladder, in the Hamiltonian formulation and at couplings up to 12. A ladder is one-dimensional in the thermodynamic sense, where a cost of flux linear in the length is expected at every coupling, so the statement carries no information about confinement in two or three dimensions. I did not find an explicit bound of this kind for a non-abelian Hamiltonian without flux cutoff; the search was short.

**Recent unrefereed claims.** Searches from 22 to 24 November 2026 turned up several self-published claims of gaps for lattice gauge Hamiltonians, among them Mihajlovic, arXiv:2611.11534, arXiv:2503.15539 (an explicit strong-coupling gap for SU(3) at magnetic-to-electric ratio at most 1/648) and several Zenodo records. I have not assessed them. None that I read claims an explicit bound on a coupling interval reaching order-one λ/e for an untruncated non-abelian model.

**What is claimed as new.** Explicit lower bounds on the gap of an untruncated SU(2) lattice gauge Hamiltonian with a plaquette term, uniform in the length of the ladder: on 0 ≤ λ/e ≤ 6 for the whole gauge-invariant space (Theorem A), on 0 ≤ λ/e ≤ 12 inside the zero-winding sector (Theorem B); and on the same range an explicit lower bound, linear in the length, on the energy of a flux line wound around the ladder (Theorem C), which together with Theorem B gives a gap above 1 for the whole gauge-invariant spectrum. The ladder is one-dimensional in the thermodynamic sense, so this says nothing about two or three space dimensions, a continuum limit, or confinement. My literature search is three days of web searches, not a review by someone in the field.

**Open items.**

- A person reading Lemmas 1 to 5 and the limit argument. Nothing done so far replaces this.
- A derivation on paper of the corner formula for the plaquette matrix elements. The identity tests are evidence, not proof. That the formula is the one printed in the literature for this model lowers the risk of a transcription error; it is not a derivation either.
- Both implementations of each computation have the same author. A third by different hands would remove that weakness.
- Lean: the analytic part of Lemma 1 (steps 1, 2 and 5), the simultaneous diagonalisation in Lemma 2, the convexity in Lemma 4 and the concavity used for Theorem C, and Lemma 5. Done since the first version: the algebra of Lemma 1, all of Lemma 6, and the per-interval arithmetic of Theorem C. Putting the ladder Hamiltonian itself into Lean, so that the seed inequalities stop being hypotheses, is a much larger job because the matrix elements are irrational.
- Past λ/e = 12 the limit is memory: the four-plaquette trial vector needs flux cutoff 3 or more, which does not fit in the 7 GB machine used here.
- Seeds on 4 plaquettes instead of 2 would give bounds for rings of length at least 4, where the true gaps are larger. Not attempted.

  A rigorous lower bound on the lowest odd-winding level on 4 plaquettes would raise σ for rings of length at least 4, to about 0.72 at λ/e = 6. It would not improve the corollary: at length 2 the bound is already within 0.005 of half the true winding energy, and at length 4 and beyond the corollary is set by Theorem B. Not attempted.
