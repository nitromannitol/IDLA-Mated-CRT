import Mathlib
import MatedCRT.Defs.Setting

/-!
# Locality of the local obstacle clusters

Deterministic part of H3 (equation (7)): the local obstacle problem in `B_r`
depends only on the restriction of the measure to `B_r`. The supersolutions `S_{B_r;z}(t)` are defined through the
distributional inequality `LaplacianLE w μ (B_r)`, whose test functions have support in `B_r`, and the Green function
`G_{B_r}` does not involve the measure. Hence equal restrictions to `B_r` give equal supersolutions, least
supersolutions, raw clusters `Λ_{B_r;z}(t)` and regularized clusters `int closure Λ_{B_r;z}(t)` (Armitage-Gardiner:
the restriction of a Riesz/Green potential datum to an open set).

Used for the transfer from a good source measure `μ⁰` to the cone measure `μ`, which agree on `B_{3/4}`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- Integrals of a test function supported in `U` against `μ` and `ν` agree when `μ` and `ν` have the same restriction
to `U`, and integrability transfers likewise. -/
theorem integral_test_congr_of_restrict {μ ν : Measure ℂ} {U : Set ℂ}
    (h : μ.restrict U = ν.restrict U) {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) :
    (Integrable φ μ ↔ Integrable φ ν) ∧ ∫ x, φ x ∂μ = ∫ x, φ x ∂ν := by
  have hsupp : Function.support φ ⊆ U := (subset_tsupport φ).trans hφ.2.2
  have hzero : ∀ x, x ∉ U → φ x = 0 := fun x hx => by
    by_contra hne
    exact hx (hsupp hne)
  have hint : ∀ ρ : Measure ℂ, Integrable φ ρ ↔ IntegrableOn φ U ρ := fun ρ =>
    (integrableOn_iff_integrable_of_support_subset hsupp).symm
  have hI : ∀ ρ : Measure ℂ, ∫ x, φ x ∂ρ = ∫ x in U, φ x ∂ρ := fun ρ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  refine ⟨?_, ?_⟩
  · rw [hint μ, hint ν]
    unfold IntegrableOn
    rw [h]
  · rw [hI μ, hI ν, h]

/-- The distributional inequality `Δw ≤ μ` in `U` depends only on the restriction of `μ` to `U`. -/
theorem laplacianLE_congr_of_restrict {w : ℂ → ℝ} {μ ν : Measure ℂ} {U : Set ℂ}
    (h : μ.restrict U = ν.restrict U) : LaplacianLE w μ U ↔ LaplacianLE w ν U := by
  unfold LaplacianLE
  constructor
  · rintro ⟨hloc, H⟩
    refine ⟨hloc, fun φ hφ h0 hint => ?_⟩
    have hk := integral_test_congr_of_restrict h hφ
    rw [← hk.2]
    exact H φ hφ h0 (hk.1.mpr hint)
  · rintro ⟨hloc, H⟩
    refine ⟨hloc, fun φ hφ h0 hint => ?_⟩
    have hk := integral_test_congr_of_restrict h hφ
    rw [hk.2]
    exact H φ hφ h0 (hk.1.mp hint)

/-- The supersolutions `S_{B_r;z}(t)` depend only on the restriction of `μ` to `B_r`. -/
theorem supersolutions_congr_of_restrict {μ ν : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (h : μ.restrict (ball 0 r) = ν.restrict (ball 0 r)) :
    supersolutions μ r z t = supersolutions ν r z t := by
  ext w
  simp only [supersolutions, Set.mem_ofPred_eq]
  rw [laplacianLE_congr_of_restrict h]

/-- The least supersolution `v_{B_r;z}(t)` depends only on the restriction of `μ` to `B_r`. -/
theorem leastSupersolution_congr_of_restrict {μ ν : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (h : μ.restrict (ball 0 r) = ν.restrict (ball 0 r)) (x : ℂ) :
    leastSupersolution μ r z t x = leastSupersolution ν r z t x := by
  unfold leastSupersolution
  rw [supersolutions_congr_of_restrict h]

/-- The raw cluster `Λ_{B_r;z}(t)` depends only on the restriction of `μ` to `B_r`. -/
theorem cluster_congr_of_restrict {μ ν : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (h : μ.restrict (ball 0 r) = ν.restrict (ball 0 r)) :
    cluster μ r z t = cluster ν r z t := by
  unfold cluster
  ext x
  simp only [Set.mem_ofPred_eq, leastSupersolution_congr_of_restrict h x]

/-- The regularized cluster `int closure Λ_{B_r;z}(t)` depends only on the restriction of `μ` to `B_r`. -/
theorem regularizedCluster_congr_of_restrict {μ ν : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (h : μ.restrict (ball 0 r) = ν.restrict (ball 0 r)) :
    regularizedCluster μ r z t = regularizedCluster ν r z t := by
  unfold regularizedCluster
  rw [cluster_congr_of_restrict h]

end MatedCRT
