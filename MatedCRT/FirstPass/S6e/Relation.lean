import Mathlib
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.GeometryId

/-!
# Lemma 6.8 bridge, section 5 (fp-S6e, z9): local sparsity gives the sparsity clause (15)

Write-up (14)-(15) of Lemma 6.8 (Admissible, clause (15)): for every nonempty `B ⊆ A`, `x ≤ c_B` or `t_B < x`.
The printed Lemma 6.8 hypothesis is the local sparsity `|A ∩ V^ε(B_r(z))| < s₁ r^{2β⁻} ε⁻¹` for all `z ∈ ℂ`
(lemma:constant-order-lower-bound-div). This file shows that local sparsity at scale `r` gives (15) at `x = r`:
if `c_B < r` then `B` lies in one ball `B_r(z)` (capacity radius, `capRadius_eq_iInf_complex`), so `|B|` is below the
local bound and `t_B < r`.
-/

namespace MatedCRT

namespace Lemma68Relation

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

open Lemma68Geometry Lemma68GeometryId Lemma68Admissible

/-- Each cell is nonempty (`cell ε η k = η '' Icc (ε (k-1)) (ε k)`). -/
theorem cell_nonempty' {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty :=
  ⟨η (ε * k), ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- The capacity radius of a nonempty finite set of cells is finite. -/
theorem capRadius_ne_top {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (B : Finset ℤ) :
    capRadius ε η B ≠ ⊤ := by
  rw [capRadius_eq_iInf_complex hη hε]
  refine ne_top_of_le_ne_top ?_ (iInf_le _ 0)
  have hfin : ∀ v : B, Metric.infEDist (0 : ℂ) (cell ε η v.1) ≠ ⊤ := fun v =>
    Metric.infEDist_ne_top (cell_nonempty' hε.le η v.1)
  exact iSup_ne_top hfin

/-- **Local sparsity gives (15).** If `B ⊆ A` is nonempty and `|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` for every `z ∈ ℂ`,
then `r ≤ c_B` or `t_B < r` (the clause (15) of `Lemma68Admissible.Admissible` at `x = r`). -/
theorem sparse15_of_local {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {A B : Finset ℤ} {r s1 βm : ℝ}
    (hs1 : 0 < s1) (hr : 0 < r) (hβ : 0 < βm) (hBne : B.Nonempty) (hBA : B ⊆ A)
    (hloc : ∀ z : ℂ, (((A : Set ℤ) ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * βm) / ε) :
    r ≤ cRad ε η B ∨ tRad ε s1 βm B < r := by
  by_cases hc : r ≤ cRad ε η B
  · exact Or.inl hc
  right
  rw [not_le] at hc
  have hlt : capRadius ε η B < ENNReal.ofReal r :=
    (ENNReal.lt_ofReal_iff_toReal_lt (capRadius_ne_top hη hε B)).2 hc
  rw [capRadius_eq_iInf_complex hη hε] at hlt
  obtain ⟨z, hz⟩ := iInf_lt_iff.1 hlt
  have hsub : (B : Set ℤ) ⊆ (A : Set ℤ) ∩ cellVertices ε η (ball z r) := by
    intro v hv
    refine ⟨hBA hv, ?_⟩
    have h1 : Metric.infEDist z (cell ε η v) < ENNReal.ofReal r :=
      lt_of_le_of_lt (le_iSup (fun w : B => Metric.infEDist z (cell ε η w.1)) ⟨v, hv⟩) hz
    obtain ⟨w, hw, hzw⟩ := Metric.infEDist_lt_iff.1 h1
    rw [edist_lt_ofReal] at hzw
    exact ⟨w, hw, by rw [mem_ball, dist_comm]; exact hzw⟩
  have hnc : ((B : Set ℤ).ncard : ℝ) ≤ (((A : Set ℤ) ∩ cellVertices ε η (ball z r)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.Finite.inter_of_left (Finset.finite_toSet A) _)
  rw [Set.ncard_coe_finset] at hnc
  have hlt2 := lt_of_le_of_lt hnc (hloc z)
  rw [lt_div_iff₀ hε] at hlt2
  have hx : (B.card : ℝ) * ε / s1 < r ^ (2 * βm) := by
    rw [div_lt_iff₀ hs1]
    nlinarith [hlt2]
  unfold tRad
  calc ((B.card : ℝ) * ε / s1) ^ (1 / (2 * βm)) < (r ^ (2 * βm)) ^ (1 / (2 * βm)) :=
        Real.rpow_lt_rpow (by positivity) hx (by positivity)
    _ = r := by
        rw [← Real.rpow_mul hr.le, mul_one_div_cancel (by positivity : (2 * βm) ≠ 0), Real.rpow_one]

end Lemma68Relation

end MatedCRT
