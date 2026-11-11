import MatedCRT.FirstPass.S6r.GoodAnnulus

/-!
# Measurability of the scale-covariant good-annulus event (§3 item 1)

Companion of `GoodAnnulus.lean` (namespace `MatedCRT.Lemma68Window`). Notation: `𝔸 = annulus z R (2R)`,
`covN` = `N_R`, `massBumpR` = `m_R^φ`, `ScaleCovGoodAnnulusEvent c0 C R z`.

Proved here:
* `measurable_covN`: `μ ↦ N_R(z; μ)` is measurable on all measures. The potential
  `v ↦ ∫_𝔸 (log(4R/|u-v|) + 1) dμ(u)` is lower semicontinuous (the kernel is continuous into `[0, ∞]`, with value
  `∞` on the diagonal, and Fatou applies in `u`), so the supremum over `closure 𝔸` is the supremum over the countable
  set `𝔸 ∩ D`, `D` dense (the argument of `measurable_iSup_logPotential`, `MatedCRT/Proofs/Measurability/GoodScale.lean`).
* `continuousOn_bumpMass`: if `μ (ball z (3R)) ≠ ⊤`, the bump mass `w ↦ ∫ φ((u-w)/(c0 R)) dμ(u)` is continuous on
  `ball z (9R/4) ⊇ closure 𝔸` (dominated convergence with bound `1_{ball z (3R)}`). Hence `m_R^φ` is the infimum over
  `𝔸 ∩ D` (`massBumpR_eq_massBumpDense`).
* `measurableSet_scaleCovGoodAnnulusEvent_finite`: `{μ | μ (ball z (3R)) ≠ ⊤ ∧ ScaleCovGoodAnnulusEvent c0 C R z μ}`
  is a measurable set of measures.

Not proved here: measurability of the event on the measures with `μ (ball z (3R)) = ⊤`. For such `μ` the bump mass is
only lower semicontinuous in `w`, so the countable reduction used above is not available. The LQG measure is locally
finite, so this does not affect the probability use.

Terminology: Armitage-Gardiner (potential theory; Fatou), Berestycki-Powell and Armstrong-Kuusi-Mourrat (good annuli),
Duplantier-Sheffield (LQG measure).
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

lemma continuous_bumpPhi : Continuous bumpPhi := by
  unfold bumpPhi
  fun_prop

lemma bumpPhi_le_one (x : ℂ) : bumpPhi x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma isOpen_annulus_R (z : ℂ) (R : ℝ) : IsOpen (annulus z R (2 * R)) :=
  isOpen_ball.sdiff isClosed_closedBall

lemma covKernel_self (R : ℝ) (u : ℂ) : covKernel R u u = ⊤ := by
  simp [covKernel]

lemma covKernel_of_ne {R : ℝ} {u v : ℂ} (h : v ≠ u) :
    covKernel R v u = ENNReal.ofReal (Real.log (4 * R / ‖u - v‖) + 1) := by
  simp [covKernel, h.symm]

/-! ### Continuity of the kernel in its first variable (value `⊤` on the diagonal) -/

lemma tendsto_covKernel_self {R : ℝ} (hR : 0 < R) (u : ℂ) :
    Tendsto (fun v => covKernel R v u) (𝓝 u) (𝓝 ⊤) := by
  have h4R : 0 < 4 * R := by linarith
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  rw [Metric.eventually_nhds_iff]
  refine ⟨4 * R * Real.exp (1 - M), mul_pos h4R (Real.exp_pos _), fun w hw => ?_⟩
  show (M : ℝ≥0∞) < covKernel R w u
  by_cases hwu : w = u
  · rw [hwu, covKernel_self]
    exact ENNReal.coe_lt_top
  · rw [covKernel_of_ne hwu, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff']
    have hd : 0 < ‖u - w‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hwu))
    have hdw : ‖u - w‖ < 4 * R * Real.exp (1 - M) := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hw
    have hE : Real.exp ((M : ℝ) - 1) * Real.exp (1 - (M : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hlog : (M : ℝ) - 1 < Real.log (4 * R / ‖u - w‖) := by
      rw [Real.lt_log_iff_exp_lt (div_pos h4R hd), lt_div_iff₀ hd]
      have h1 : Real.exp ((M : ℝ) - 1) * ‖u - w‖ < Real.exp ((M : ℝ) - 1) * (4 * R * Real.exp (1 - (M : ℝ))) :=
        mul_lt_mul_of_pos_left hdw (Real.exp_pos _)
      have h2 : Real.exp ((M : ℝ) - 1) * (4 * R * Real.exp (1 - (M : ℝ))) = 4 * R := by
        calc _ = 4 * R * (Real.exp ((M : ℝ) - 1) * Real.exp (1 - (M : ℝ))) := by ring
          _ = 4 * R := by rw [hE, mul_one]
      linarith
    exact ⟨by linarith, by linarith [NNReal.coe_nonneg M]⟩

lemma continuousAt_covKernel_of_ne {R : ℝ} (hR : 0 < R) {u v : ℂ} (huv : v ≠ u) :
    ContinuousAt (fun w => covKernel R w u) v := by
  have hev : (fun w => ENNReal.ofReal (Real.log (4 * R / ‖u - w‖) + 1)) =ᶠ[𝓝 v]
      fun w => covKernel R w u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds huv] with w hw
    exact (covKernel_of_ne (mem_compl_singleton_iff.1 hw)).symm
  refine ContinuousAt.congr ?_ hev
  have hn : ‖u - v‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm huv))
  have hnorm : ContinuousAt (fun w : ℂ => ‖u - w‖) v :=
    ((continuous_const.sub continuous_id).norm).continuousAt
  have h4R : 4 * R ≠ 0 := by intro h; linarith
  have hdiv : ContinuousAt (fun w : ℂ => 4 * R / ‖u - w‖) v :=
    continuousAt_const.div hnorm hn
  have hlog : ContinuousAt (fun w : ℂ => Real.log (4 * R / ‖u - w‖) + 1) v :=
    (hdiv.log (div_ne_zero h4R hn)).add_const 1
  exact ENNReal.continuous_ofReal.continuousAt.comp hlog

/-- `v ↦ covKernel R v u` is continuous into `[0, ∞]` for every `u` (the diagonal value `⊤` is the limit). -/
lemma continuous_covKernel {R : ℝ} (hR : 0 < R) (u : ℂ) : Continuous fun v => covKernel R v u := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases h : v = u
  · rw [h]
    show Tendsto (fun w => covKernel R w u) (𝓝 u) (𝓝 (covKernel R u u))
    rw [covKernel_self]
    exact tendsto_covKernel_self hR u
  · exact continuousAt_covKernel_of_ne hR h

/-! ### The supremum defining `N_R` is a countable supremum -/

lemma covN_eq_iSup_inter_dense {R : ℝ} (hR : 0 < R) (z : ℂ) (μ : Measure ℂ) {D : Set ℂ} (hD : Dense D) :
    covN R z μ = ⨆ v ∈ annulus z R (2 * R) ∩ D, ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ := by
  unfold covN
  have hA := isOpen_annulus_R z R
  have hAD : annulus z R (2 * R) ⊆ closure (annulus z R (2 * R) ∩ D) := hD.open_subset_closure_inter hA
  apply le_antisymm
  · refine iSup₂_le fun v hv => ?_
    obtain ⟨x, hxS, hxv⟩ := mem_closure_iff_seq_limit.1 (closure_minimal hAD isClosed_closure hv)
    have htend : ∀ u : ℂ, Tendsto (fun n => covKernel R (x n) u) atTop (𝓝 (covKernel R v u)) :=
      fun u => ((continuous_covKernel hR u).tendsto v).comp hxv
    calc ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ
        ≤ ∫⁻ u in annulus z R (2 * R), liminf (fun n => covKernel R (x n) u) atTop ∂μ :=
          lintegral_mono fun u => le_of_eq (htend u).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ u in annulus z R (2 * R), covKernel R (x n) u ∂μ) atTop :=
          lintegral_liminf_le fun n => measurable_covKernel R (x n)
      _ ≤ limsup (fun n => ∫⁻ u in annulus z R (2 * R), covKernel R (x n) u ∂μ) atTop := liminf_le_limsup
      _ ≤ ⨆ n, ∫⁻ u in annulus z R (2 * R), covKernel R (x n) u ∂μ := limsup_le_iSup
      _ ≤ _ := iSup_le fun n => le_iSup₂_of_le (x n) (hxS n) le_rfl
  · exact iSup₂_le fun v hv => le_iSup₂_of_le v (subset_closure hv.1) le_rfl

/-- `μ ↦ N_R(z; μ)` is measurable on all measures. -/
theorem measurable_covN {R : ℝ} (hR : 0 < R) (z : ℂ) : Measurable fun μ : Measure ℂ => covN R z μ := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hrep : (fun μ : Measure ℂ => covN R z μ) = fun μ : Measure ℂ =>
      ⨆ v ∈ annulus z R (2 * R) ∩ D, ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ :=
    funext fun μ => covN_eq_iSup_inter_dense hR z μ hD
  rw [hrep]
  refine Measurable.biSup _ (hDc.mono inter_subset_right) fun v _ => ?_
  simp_rw [← lintegral_indicator (isOpen_annulus_R z R).measurableSet]
  exact Measure.measurable_lintegral
    ((measurable_covKernel R v).indicator (isOpen_annulus_R z R).measurableSet)

/-! ### The bump mass and its countable reduction -/

lemma continuous_bumpArg (c0 R : ℝ) (w : ℂ) : Continuous fun u : ℂ => (u - w) / ((c0 * R : ℝ) : ℂ) := by
  fun_prop

lemma measurable_bumpIntegrand (c0 R : ℝ) (w : ℂ) :
    Measurable fun u : ℂ => ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))) :=
  ((continuous_bumpPhi.comp (continuous_bumpArg c0 R w)).measurable).ennreal_ofReal

lemma measurable_bumpMass (c0 R : ℝ) (w : ℂ) : Measurable fun μ : Measure ℂ => bumpMass c0 R μ w :=
  Measure.measurable_lintegral (measurable_bumpIntegrand c0 R w)

/-- The integrand of the bump mass is dominated by `1_{ball z (3R)}` for `w ∈ ball z (9R/4)`, `0 < c0 ≤ 1`. -/
lemma bumpIntegrand_le_indicator {c0 R : ℝ} (hR : 0 < R) (hc0 : 0 < c0) (hc1 : c0 ≤ 1) {z w u : ℂ}
    (hw : w ∈ ball z (9 * R / 4)) :
    ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))) ≤ (ball z (3 * R)).indicator 1 u := by
  by_cases hu : u ∈ ball z (3 * R)
  · rw [indicator_of_mem hu, Pi.one_apply]
    exact ENNReal.ofReal_le_one.2 (bumpPhi_le_one _)
  · rw [indicator_of_notMem hu]
    have h1 : 3 * R ≤ dist u z := not_lt.1 (fun h => hu (mem_ball.2 h))
    have h2 : dist w z < 9 * R / 4 := mem_ball.1 hw
    have h3 : 3 * R / 4 < dist u w := by
      have := dist_triangle u w z
      linarith
    have hcR : c0 * R ≤ R := mul_le_of_le_one_left hR.le hc1
    have h4 : 3 / 4 ≤ ‖(u - w) / ((c0 * R : ℝ) : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hc0.le hR.le),
        le_div_iff₀ (mul_pos hc0 hR), ← dist_eq_norm]
      nlinarith
    rw [bumpPhi_eq_zero h4, ENNReal.ofReal_zero]

/-- `w ↦ ∫ φ((u-w)/(c0 R)) dμ(u)` is continuous on `ball z (9R/4)` when `μ (ball z (3R)) ≠ ⊤`. -/
lemma continuousOn_bumpMass {c0 R : ℝ} (hR : 0 < R) (hc0 : 0 < c0) (hc1 : c0 ≤ 1) {z : ℂ} {μ : Measure ℂ}
    (hμ : μ (ball z (3 * R)) ≠ ⊤) : ContinuousOn (bumpMass c0 R μ) (ball z (9 * R / 4)) := by
  intro w0 hw0
  refine ContinuousAt.continuousWithinAt ?_
  have hfin : ∫⁻ u, (ball z (3 * R)).indicator 1 u ∂μ ≠ ⊤ := by
    rw [lintegral_indicator_one measurableSet_ball]
    exact hμ
  have hbound : ∀ᶠ w in 𝓝 w0, ∀ᵐ u ∂μ,
      ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))) ≤ (ball z (3 * R)).indicator 1 u :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw0) fun w hw =>
      ae_of_all μ fun u => bumpIntegrand_le_indicator hR hc0 hc1 hw
  have hpt : ∀ᵐ u ∂μ, Tendsto (fun w : ℂ => ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))))
      (𝓝 w0) (𝓝 (ENNReal.ofReal (bumpPhi ((u - w0) / ((c0 * R : ℝ) : ℂ))))) :=
    ae_of_all μ fun u => (ENNReal.continuous_ofReal.comp (continuous_bumpPhi.comp
      (show Continuous fun w : ℂ => (u - w) / ((c0 * R : ℝ) : ℂ) by fun_prop))).tendsto w0
  exact tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝 w0) ((ball z (3 * R)).indicator 1)
    (Filter.Eventually.of_forall fun w => measurable_bumpIntegrand c0 R w) hbound hfin hpt

/-- Infimum over the closure of an open set equals the infimum over the countable part `A ∩ D`, for `g` continuous
on the closure. -/
lemma iInf_closure_eq_iInf_inter_dense {g : ℂ → ℝ≥0∞} {A D : Set ℂ} (hA : IsOpen A) (hD : Dense D)
    (hg : ContinuousOn g (closure A)) :
    ⨅ v ∈ closure A, g v = ⨅ v ∈ A ∩ D, g v := by
  apply le_antisymm
  · refine le_iInf₂ fun v hv => ?_
    exact iInf₂_le v (subset_closure hv.1)
  · refine le_iInf₂ fun v hv => ?_
    have hv' : v ∈ closure (A ∩ D) := closure_minimal (hD.open_subset_closure_inter hA) isClosed_closure hv
    obtain ⟨x, hxS, hxv⟩ := mem_closure_iff_seq_limit.1 hv'
    have hcont : Tendsto (fun n => g (x n)) atTop (𝓝 (g v)) :=
      (hg.continuousWithinAt hv).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxv, Eventually.of_forall fun n => subset_closure (hxS n).1⟩)
    exact ge_of_tendsto hcont (Eventually.of_forall fun n => iInf₂_le (x n) (hxS n))

/-- The countable-reduction form of the bump mass: `inf` over `𝔸 ∩ D`. -/
noncomputable def massBumpDense (c0 R : ℝ) (z : ℂ) (D : Set ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨅ w ∈ annulus z R (2 * R) ∩ D, bumpMass c0 R μ w

lemma massBumpR_eq_massBumpDense {c0 R : ℝ} (hR : 0 < R) (hc0 : 0 < c0) (hc1 : c0 ≤ 1) {z : ℂ}
    {μ : Measure ℂ} (hμ : μ (ball z (3 * R)) ≠ ⊤) {D : Set ℂ} (hD : Dense D) :
    massBumpR c0 R z μ = massBumpDense c0 R z D μ := by
  unfold massBumpR massBumpDense
  refine iInf_closure_eq_iInf_inter_dense (isOpen_annulus_R z R) hD ?_
  refine (continuousOn_bumpMass hR hc0 hc1 hμ).mono ?_
  exact closure_annulus_subset.trans (closedBall_subset_ball (by linarith))

lemma measurable_massBumpDense (c0 R : ℝ) (z : ℂ) {D : Set ℂ} (hDc : D.Countable) :
    Measurable (massBumpDense c0 R z D) := by
  unfold massBumpDense
  exact Measurable.biInf _ (hDc.mono inter_subset_right) fun w _ => measurable_bumpMass c0 R w

/-! ### Measurability of the good-annulus event on the locally finite part -/

/-- `{μ | μ (ball z (3R)) ≠ ⊤ ∧ ScaleCovGoodAnnulusEvent c0 C R z μ}` is a measurable set of measures (§3 item 1). -/
theorem measurableSet_scaleCovGoodAnnulusEvent_finite {c0 C R : ℝ} (hR : 0 < R) (hc0 : 0 < c0) (hc1 : c0 ≤ 1)
    (z : ℂ) :
    MeasurableSet {μ : Measure ℂ | μ (ball z (3 * R)) ≠ ⊤ ∧ ScaleCovGoodAnnulusEvent c0 C R z μ} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hm : Measurable (massBumpDense c0 R z D) := measurable_massBumpDense c0 R z hDc
  have hN := measurable_covN hR z
  have hfin : MeasurableSet {μ : Measure ℂ | μ (ball z (3 * R)) ≠ ⊤} :=
    (Measure.measurable_coe measurableSet_ball) (measurableSet_singleton ⊤).compl
  have heq : {μ : Measure ℂ | μ (ball z (3 * R)) ≠ ⊤ ∧ ScaleCovGoodAnnulusEvent c0 C R z μ} =
      {μ : Measure ℂ | μ (ball z (3 * R)) ≠ ⊤} ∩
        ({μ | 0 < massBumpDense c0 R z D μ} ∩
          ({μ | massBumpDense c0 R z D μ < ⊤} ∩
            {μ | covN R z μ ≤ ENNReal.ofReal C * massBumpDense c0 R z D μ})) := by
    ext μ
    simp only [mem_inter_iff, ScaleCovGoodAnnulusEvent]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      rw [massBumpR_eq_massBumpDense hR hc0 hc1 h1 hD] at h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_⟩
      rw [massBumpR_eq_massBumpDense hR hc0 hc1 h1 hD]
      exact ⟨h2, h3, h4⟩
  rw [heq]
  exact hfin.inter ((measurableSet_lt measurable_const hm).inter
    ((measurableSet_lt hm measurable_const).inter (measurableSet_le hN (hm.const_mul _))))

end Lemma68Window

end MatedCRT
