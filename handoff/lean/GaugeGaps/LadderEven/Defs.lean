import CertifiedGaps.ChainCheck

/-!
# Zero-winding sector of the SU(2) ladder: intervals with chain certificates (definitions)
-/

open CertifiedGaps

namespace GaugeGaps.LadderEven

/-- A coupling interval with its seed temperature and chain certificate. -/
structure Interval where
  la : ℚ
  lb : ℚ
  β₀ : ℚ
  cert : ChainCertificate

/-- `tilesB l a b`: the intervals of `l` are nondegenerate, the first starts at `a`, each ends where the next starts,
and the last ends at `b` (for the empty list: `a = b`). -/
def tilesB : List Interval → ℚ → ℚ → Bool
  | [], a, b => decide (a = b)
  | I :: l, a, b => decide (I.la = a) && (decide (I.la < I.lb) && tilesB l I.lb b)

theorem tilesB_append {l₁ l₂ : List Interval} {a b c : ℚ} (h₁ : tilesB l₁ a b = true) (h₂ : tilesB l₂ b c = true) :
    tilesB (l₁ ++ l₂) a c = true := by
  induction l₁ generalizing a with
  | nil =>
    have : a = b := by simpa [tilesB] using h₁
    subst this; simpa using h₂
  | cons I l ih =>
    simp only [tilesB, Bool.and_eq_true, decide_eq_true_eq] at h₁
    simp only [List.cons_append, tilesB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h₁.1, h₁.2.1, ih h₁.2.2⟩

/-- A tiling covers every real point between its ends. -/
theorem exists_mem_of_tilesB {l : List Interval} {a b : ℚ} (h : tilesB l a b = true) (hab : a < b) (x : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) : ∃ I ∈ l, (I.la : ℝ) ≤ x ∧ x ≤ (I.lb : ℝ) := by
  induction l generalizing a with
  | nil =>
    have : a = b := by simpa [tilesB] using h
    exact absurd this (ne_of_lt hab)
  | cons I l ih =>
    simp only [tilesB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hIa, hI, hl⟩ := h
    by_cases hx : x ≤ (I.lb : ℝ)
    · exact ⟨I, List.mem_cons_self, by rw [hIa]; exact hax, hx⟩
    · have hx' : (I.lb : ℝ) < x := lt_of_not_ge hx
      have hlt : I.lb < b := by exact_mod_cast lt_of_lt_of_le hx' hxb
      obtain ⟨J, hJ, hJx⟩ := ih hl hlt (le_of_lt hx')
      exact ⟨J, List.mem_cons_of_mem _ hJ, hJx⟩

end GaugeGaps.LadderEven
