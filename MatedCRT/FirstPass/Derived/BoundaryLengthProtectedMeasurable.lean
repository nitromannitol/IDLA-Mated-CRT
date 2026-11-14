import MatedCRT.FirstPass.Derived.BoundaryLengthPastMeasurable

/-!
# Past measurability of protected cell minima

A path staying above the minimum of a mesh cell up to a later mesh point is
measurable from the path up to any time beyond that point.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- Protection of a cell minimum up to a later mesh endpoint is determined
measurably by past path evaluations. -/
theorem measurableSet_cellMin_protected_of_past {Ω : Type} [MeasurableSpace Ω]
    (B : Ω → C(ℝ, ℝ × ℝ)) (s ε : ℝ)
    (hB : ∀ t ≤ s, Measurable fun ω => B ω t)
    (hε : 0 ≤ ε) (j n : ℤ) (hjn : j ≤ n) (hn : ε * n ≤ s)
    (q : ℝ × ℝ → ℝ) (hq : Continuous q) :
    MeasurableSet {ω | ∀ u ∈ Icc (ε * j) (ε * n),
      sInf ((fun t => q (B ω t)) '' Icc (ε * j - ε) (ε * j)) ≤ q (B ω u)} := by
  have hjnR : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hjn' : ε * j ≤ ε * n := mul_le_mul_of_nonneg_left hjnR hε
  let Bstop : Ω → C(ℝ, ℝ × ℝ) := fun ω =>
    ⟨fun t => B ω (min t s), (B ω).continuous.comp (continuous_id.min continuous_const)⟩
  have hstop : Measurable Bstop := by
    apply ContinuousMap.measurable_iff_eval.2
    intro t
    exact hB (min t s) (min_le_right t s)
  have hcomp : MeasurableSet {ω |
      sInf ((fun t => q (Bstop ω t)) '' Icc (ε * j - ε) (ε * j)) ≤
      sInf ((fun t => q (Bstop ω t)) '' Icc (ε * j) (ε * n))} :=
    measurableSet_le ((continuous_path_interval_inf _ _ q hq).measurable.comp hstop)
      ((continuous_path_interval_inf _ _ q hq).measurable.comp hstop)
  convert hcomp using 1
  ext ω
  have heq : ∀ t ≤ ε * n, Bstop ω t = B ω t := by
    intro t ht
    simp only [Bstop, ContinuousMap.coe_mk, min_eq_left (ht.trans hn)]
  have heqCell : (fun t => q (Bstop ω t)) '' Icc (ε * j - ε) (ε * j) =
      (fun t => q (B ω t)) '' Icc (ε * j - ε) (ε * j) := by
    apply image_congr
    intro t ht
    rw [heq t (ht.2.trans hjn')]
  have heqMid : (fun t => q (Bstop ω t)) '' Icc (ε * j) (ε * n) =
      (fun t => q (B ω t)) '' Icc (ε * j) (ε * n) := by
    apply image_congr
    intro t ht
    rw [heq t ht.2]
  simp only [mem_ofPred_eq, heqCell, heqMid]
  constructor
  · intro h
    exact le_csInf ((nonempty_Icc.mpr hjn').image _) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)
  · intro h t ht
    exact h.trans (csInf_le (isCompact_Icc.image (hq.comp (B ω).continuous)).bddBelow ⟨t, ht, rfl⟩)

end MatedCRT
