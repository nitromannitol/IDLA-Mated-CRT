import MatedCRT.FirstPass.S2g.HalfBallFamily

/-!
# Locality of the radius-3/4 cluster data (deterministic, q1, fp-S2g)

Route: `notes/fp-gaps/CHATGPT-q1-open-steps.md` Section 3, H3 (`A^μ_t = A^{μ⁰}_t`). The supersolution inequality on
`B_r` only sees the restriction of `μ` to `B_r`: `LaplacianLE w μ U` and `HasLaplacian w μpos μneg U` test against
functions whose support lies in `U`. Hence the least supersolution, the cluster, the regularized cluster and the
radius-3/4 data at each time depend on `μ` only through `μ.restrict (ball 0 (3/4))`. This is the deterministic part of
the transfer of the pathwise half-ball inputs from a source model to a cone measure with the same local law.

Terminology: least supersolution and cluster (Armstrong-Kuusi-Mourrat, Harmonic balls in LQG), distributional
Laplacian and test functions (Armitage-Gardiner).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- A test function with support in `U` has the same integral against `μ` and `ν` when `μ` and `ν` agree on `U`,
and is integrable against one iff against the other. -/
theorem integrable_and_integral_eq_of_restrict_eq {U : Set ℂ} {μ ν : Measure ℂ}
    (h : μ.restrict U = ν.restrict U) {φ : ℂ → ℝ} (hφ : tsupport φ ⊆ U) :
    (Integrable φ μ ↔ Integrable φ ν) ∧ ∫ x, φ x ∂μ = ∫ x, φ x ∂ν := by
  have hsupp : Function.support φ ⊆ U := (subset_tsupport φ).trans hφ
  have hzero : ∀ x, x ∉ U → φ x = 0 := fun x hx => by
    by_contra hne
    exact hx (hφ (subset_tsupport φ hne))
  constructor
  · rw [← integrableOn_iff_integrable_of_support_subset hsupp,
      ← integrableOn_iff_integrable_of_support_subset hsupp]
    unfold IntegrableOn
    rw [h]
  · have e1 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hzero
    have e2 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hzero
    rw [← e1, ← e2, h]

/-- The distributional inequality `Δw ≤ μ` in `U` depends only on `μ.restrict U`: one direction. -/
theorem laplacianLE_of_restrict_eq {U : Set ℂ} {μ ν : Measure ℂ} (h : μ.restrict U = ν.restrict U) {w : ℂ → ℝ}
    (hw : LaplacianLE w μ U) : LaplacianLE w ν U := by
  unfold LaplacianLE at hw ⊢
  obtain ⟨hloc, hle⟩ := hw
  refine ⟨hloc, fun φ hT hnn hint => ?_⟩
  have key := integrable_and_integral_eq_of_restrict_eq (φ := φ) h hT.2.2
  rw [← key.2]
  exact hle φ hT hnn (key.1.mpr hint)

/-- The distributional inequality `Δw ≤ μ` in `U` depends only on `μ.restrict U`. -/
theorem laplacianLE_congr_restrict {U : Set ℂ} {μ ν : Measure ℂ} (h : μ.restrict U = ν.restrict U) (w : ℂ → ℝ) :
    LaplacianLE w μ U ↔ LaplacianLE w ν U :=
  ⟨laplacianLE_of_restrict_eq h, laplacianLE_of_restrict_eq h.symm⟩

/-- The supersolution class `S_{B_r;z}(t)` depends only on `μ.restrict (B_r)`. -/
theorem supersolutions_congr_restrict (t r : ℝ) (z : ℂ) {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) r) = ν.restrict (ball (0 : ℂ) r)) :
    supersolutions μ r z t = supersolutions ν r z t := by
  ext w
  unfold supersolutions
  simp only [Set.mem_ofPred_eq, laplacianLE_congr_restrict h]

/-- The least supersolution `v_{B_r;z}(t)` depends only on `μ.restrict (B_r)`. -/
theorem leastSupersolution_congr_restrict (t r : ℝ) (z : ℂ) {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) r) = ν.restrict (ball (0 : ℂ) r)) :
    leastSupersolution μ r z t = leastSupersolution ν r z t := by
  funext x
  unfold leastSupersolution
  rw [supersolutions_congr_restrict t r z h]

/-- The cluster `Λ_{B_r;z}(t)` depends only on `μ.restrict (B_r)`. -/
theorem cluster_congr_restrict (t r : ℝ) (z : ℂ) {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) r) = ν.restrict (ball (0 : ℂ) r)) :
    cluster μ r z t = cluster ν r z t := by
  unfold cluster
  rw [leastSupersolution_congr_restrict t r z h]

/-- The regularized cluster `interior (closure Λ_{B_r;z}(t))` depends only on `μ.restrict (B_r)`. -/
theorem regularizedCluster_congr_restrict (t r : ℝ) (z : ℂ) {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) r) = ν.restrict (ball (0 : ℂ) r)) :
    regularizedCluster μ r z t = regularizedCluster ν r z t := by
  unfold regularizedCluster
  rw [cluster_congr_restrict t r z h]

/-- At radius `3/4` the regularized cluster lies in `B_{3/4}`, so its restricted measure depends only on
`μ.restrict (B_{3/4})`. -/
theorem restrict_regularizedCluster_eq_of_three_quarters {μ ν : Measure ℂ} (t : ℝ)
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4))) :
    μ.restrict (regularizedCluster μ (3 / 4) 0 t) = ν.restrict (regularizedCluster ν (3 / 4) 0 t) := by
  rw [regularizedCluster_congr_restrict t (3 / 4) 0 h]
  have hsub := regularizedCluster_subset_ball_three_quarters ν t
  rw [← Measure.restrict_restrict_of_subset (μ := μ) hsub, h, Measure.restrict_restrict_of_subset hsub]

/-- The regularized-cluster family at radius `3/4` is the same function of `t` for locally equal measures. -/
theorem regularizedCluster_fun_congr_three_quarters {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4))) :
    regularizedCluster μ (3 / 4) 0 = regularizedCluster ν (3 / 4) 0 := by
  funext t
  exact regularizedCluster_congr_restrict t (3 / 4) 0 h

/-- The radius-`3/4` data at a time `t` (`RadiusThreeQuartersData`) transfers between measures agreeing on `B_{3/4}`. -/
theorem radiusThreeQuartersData_of_restrict_eq {μ ν : Measure ℂ} {t : ℝ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4)))
    (hd : RadiusThreeQuartersData μ t) : RadiusThreeQuartersData ν t := by
  obtain ⟨hopen, hmem, hsph, hlap⟩ := hd
  unfold RadiusThreeQuartersData
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cluster_congr_restrict t (3 / 4) 0 h]
    exact hopen
  · rw [← leastSupersolution_congr_restrict t (3 / 4) 0 h, ← supersolutions_congr_restrict t (3 / 4) 0 h]
    exact hmem
  · rw [← leastSupersolution_congr_restrict t (3 / 4) 0 h]
    exact hsph
  · rw [← leastSupersolution_congr_restrict t (3 / 4) 0 h, ← restrict_regularizedCluster_eq_of_three_quarters t h]
    exact hlap

/-- `RadiusThreeQuartersData` depends only on `μ.restrict (B_{3/4})`. -/
theorem radiusThreeQuartersData_iff_of_restrict_eq {μ ν : Measure ℂ} {t : ℝ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4))) :
    RadiusThreeQuartersData μ t ↔ RadiusThreeQuartersData ν t :=
  ⟨radiusThreeQuartersData_of_restrict_eq h, radiusThreeQuartersData_of_restrict_eq h.symm⟩

end MatedCRT
