import MatedCRT.FirstPass.Derived.AreaCellExactRoot
import LatticeProb.Prob.CellConfigCellDiameterSublinear

/-! # Rooted sums for area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- At a singleton-fibre time, a weighted rooted sum has exactly the two
terms indexed by the cells immediately before and after time zero. -/
theorem tsum_originAreaRatio_euclideanCell_eq_two_terms
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (hf : ∀ t, η t = η 0 → t = 0)
    (w : ℤ → ℝ≥0∞) :
    (∑' k : ℤ, originAreaRatio (euclideanCell ε η h.1 hε k) * w k) =
      originAreaRatio (euclideanCell ε η h.1 hε 0) * w 0 +
        originAreaRatio (euclideanCell ε η h.1 hε 1) * w 1 := by
  classical
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro k hk
    have hn : (0 : ReflectedGMS.Plane) ∉
        (euclideanCell ε η h.1 hε k : Set ReflectedGMS.Plane) := by
      intro hmem
      have := (zero_mem_euclideanCell_iff h hε hf k).1 hmem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact this.elim hk.1 hk.2
    rw [originAreaRatio, Set.indicator_of_notMem (show
      euclideanCell ε η h.1 hε k ∉
        {K : Cell | (0 : ReflectedGMS.Plane) ∈ (K : Set ReflectedGMS.Plane)} from hn)]
    simp

/-- The two-term identity holds simultaneously for every positive mesh and
weight on the fixed almost-sure singleton-fibre event. -/
theorem MatedCRTEnv.IsValid.ae_tsum_originAreaRatio_euclideanCell
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (h : IsAreaParametrized (S.μ ω) (S.η ω))
      (ε : ℝ) (hε : 0 < ε) (w : ℤ → ℝ≥0∞),
      (∑' k : ℤ, originAreaRatio (euclideanCell ε (S.η ω) h.1 hε k) * w k) =
        originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 0) * w 0 +
          originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 1) * w 1 := by
  filter_upwards [hS.ae_fixedTime_singleton_fibre 0] with ω hf h ε hε w
  exact tsum_originAreaRatio_euclideanCell_eq_two_terms h hε hf w

end MatedCRT
