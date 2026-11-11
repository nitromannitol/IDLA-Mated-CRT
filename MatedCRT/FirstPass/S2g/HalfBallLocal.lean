import MatedCRT.FirstPass.S2g.HalfBallFamily

/-!
# Locality of the radius-3/4 cluster data (deterministic)

Route: H3 (`A^μ_t = A^{μ⁰}_t`). The supersolution inequality on
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

/-- Two measures agreeing on an open set `U` give the same mass to every subset of `U`. -/
theorem measure_apply_eq_of_restrict_eq {U S : Set ℂ} {μ ν : Measure ℂ} (hU : MeasurableSet U)
    (h : μ.restrict U = ν.restrict U) (hS : S ⊆ U) : μ S = ν S := by
  have key : ∀ ρ : Measure ℂ, ρ.restrict U S = ρ S := fun ρ => by
    rw [Measure.restrict_apply' hU, inter_eq_left.mpr hS]
  rw [← key μ, ← key ν, h]

/-- A set whose closure lies in `B_{1/2}` has closure in `B_{3/4}` (closed ball of radius `1/2` inside the open ball of
radius `3/4`). -/
theorem closure_subset_ball_three_quarters_of_subset_half {S : Set ℂ} (hS : S ⊆ ball (0 : ℂ) (1 / 2)) :
    closure S ⊆ ball (0 : ℂ) (3 / 4) := by
  have h1 : closure S ⊆ closedBall (0 : ℂ) (1 / 2) :=
    closure_minimal (hS.trans ball_subset_closedBall) isClosed_closedBall
  exact h1.trans (closedBall_subset_ball (by norm_num))

/-- Harmonic balls for `μ` and `ν` coincide when `μ` and `ν` agree on `B_{3/4}` and the set `Λ` has closure in `B_{3/4}`
(Armitage-Gardiner: the mean value property of `f` at the centre only sees the measure on `Λ`). -/
theorem isHarmonicBall_iff_of_restrict_eq {μ ν : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4)))
    (hΛ : closure Λ ⊆ ball (0 : ℂ) (3 / 4)) : IsHarmonicBall μ Λ z ↔ IsHarmonicBall ν Λ z := by
  have hsub : Λ ⊆ ball (0 : ℂ) (3 / 4) := subset_closure.trans hΛ
  have hμΛ : μ Λ = ν Λ := measure_apply_eq_of_restrict_eq measurableSet_ball h hsub
  have hres : μ.restrict Λ = ν.restrict Λ := by
    rw [← Measure.restrict_restrict_of_subset (μ := μ) hsub, h, Measure.restrict_restrict_of_subset hsub]
  have hreal : μ.real Λ = ν.real Λ := by
    simp only [Measure.real, hμΛ]
  have hMVP : ∀ f : ℂ → ℝ, HasMeanValueProperty μ Λ z f ↔ HasMeanValueProperty ν Λ z f := by
    intro f
    unfold HasMeanValueProperty IntegrableOn
    rw [hres, hreal]
  unfold IsHarmonicBall
  simp only [hμΛ, hMVP]

/-- The conditions of `SatisfiesHarmonicBallConditionsOn` depend on `μ` only through `μ.restrict (B_{3/4})`, when every
`Λ t`, `t ∈ (0,T)`, has closure in `B_{3/4}` (the masses of `Λ t` and of its frontier see only `B_{3/4}`). -/
theorem satisfiesHarmonicBallConditionsOn_of_restrict_eq {μ ν : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ} {T : ℝ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4)))
    (hΛ : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (3 / 4))
    (hd : SatisfiesHarmonicBallConditionsOn μ Λ z T) : SatisfiesHarmonicBallConditionsOn ν Λ z T where
  measure_eq t ht := by
    rw [← measure_apply_eq_of_restrict_eq measurableSet_ball h (subset_closure.trans (hΛ t ht))]
    exact hd.measure_eq t ht
  measure_frontier t ht := by
    rw [← measure_apply_eq_of_restrict_eq measurableSet_ball h (frontier_subset_closure.trans (hΛ t ht))]
    exact hd.measure_frontier t ht
  isRegularOpen := hd.isRegularOpen
  isBounded := hd.isBounded
  isConnected := hd.isConnected
  mem := hd.mem
  monotoneOn := hd.monotoneOn
  hausdorffContinuousOn := hd.hausdorffContinuousOn
  iInter_eq := hd.iInter_eq

/-- **Transfer of the pathwise half-ball inputs (deterministic).** `ConePathwiseHalfBallInputs` depends on the measure
only through its restriction to `B_{3/4}` and its local finiteness. If `μ` has the inputs and `ν` is locally finite and
agrees with `μ` on `B_{3/4}`, then `ν` has them, with the same canonical time. The regularized cluster family at radius
`3/4` is unchanged (`regularizedCluster_fun_congr_three_quarters`), its harmonic-ball and obstacle clauses on `(0, T)`
transfer by the two locality lemmas above, since `Λ_t` lies in `B_{1/2}` for `t < T` (`regularizedCluster_subset_half_of_lt_sSup`). -/
theorem pathwiseInputs_of_restrict_eq {μ ν : Measure ℂ}
    (h : μ.restrict (ball (0 : ℂ) (3 / 4)) = ν.restrict (ball (0 : ℂ) (3 / 4)))
    (hν : IsLocallyFiniteMeasure ν) (hμ : ConePathwiseHalfBallInputs μ) : ConePathwiseHalfBallInputs ν := by
  obtain ⟨_, hopen, hdat, hmono, hH, hne, hbdd, hHB, hSat⟩ := hμ
  have hfun := regularizedCluster_fun_congr_three_quarters h
  have hcl : ∀ t ∈ Ioo 0 (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)}),
      closure (regularizedCluster μ (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) :=
    fun t ht => closure_subset_ball_three_quarters_of_subset_half (regularizedCluster_subset_half_of_lt_sSup hmono hne ht)
  unfold ConePathwiseHalfBallInputs
  rw [← hfun]
  refine ⟨hν, fun t ht => by rw [← cluster_congr_restrict t (3 / 4) 0 h]; exact hopen t ht,
    fun t ht => radiusThreeQuartersData_of_restrict_eq h (hdat t ht), hmono, hH, hne, hbdd, ?_, ?_⟩
  · intro t ht
    exact (isHarmonicBall_iff_of_restrict_eq h (hcl t ht)).mp (hHB t ht)
  · exact satisfiesHarmonicBallConditionsOn_of_restrict_eq h hcl hSat

end MatedCRT
