import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapPole
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift

/-! Distributional comparison for the strict obstacle gap. -/

namespace MatedCRT

open Set Metric MeasureTheory Laplacian _root_.HarmonicBalls

/-- Subtracting a function whose Laplacian is the common upper bound gives
an increment with nonpositive distributional Laplacian. -/
theorem laplacianLE_sub_of_hasLaplacian
    {U : Set ℂ} {μ : Measure ℂ} {v w : ℂ → ℝ}
    (hw : LaplacianLE w μ U) (hv : HasLaplacian v μ 0 U) :
    LaplacianLE (fun x => w x - v x) 0 U := by
  refine ⟨hw.1.sub hv.1, fun φ hφ hφ0 _ => ?_⟩
  have hwφ := hw.2 φ hφ hφ0 (hv.2 φ hφ).1
  have hvφ := (hv.2 φ hφ).2.2
  rw [integral_zero_measure, sub_zero] at hvφ
  have he : (fun x => (w x - v x) * Δ φ x) =
      (fun x => w x * Δ φ x - v x * Δ φ x) := by
    funext x
    ring
  rw [he, integral_sub (integrable_mul_laplacian_of_test hw.1 hφ)
    (integrable_mul_laplacian_of_test hv.1 hφ), integral_zero_measure]
  linarith

/-- Away from the pole the odometer has Laplacian bounded above by the
background measure. -/
theorem odometer_laplacianLE_off_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {t : ℝ} (ht : 0 < t) :
    LaplacianLE (odometer μ ρ z t) μ (ball (0 : ℂ) ρ \ {z}) := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hρ hV hz ht
  have hG := hasLaplacian_zero_of_harmonicOnNhd
    (isOpen_ball.sdiff isClosed_singleton) (harmonicOnNhd_greenFunction_ball hz)
  exact (hw.2.1.mono_set sdiff_subset).add_const_mul_of_hasLaplacian_zero hG t

/-- The obstacle increment is superharmonic when the earlier odometer has
Laplacian equal to the background measure on the punctured regularization. -/
theorem superharmonic_odometer_increment_of_hasLaplacian
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hcompact : closure (cluster μ ρ z s) ⊆ ball 0 ρ)
    (hΔ : HasLaplacian (odometer μ ρ z s) μ 0
      (interior (closure (cluster μ ρ z s)) \ {z})) :
    IsSuperharmonicOn (interior (closure (cluster μ ρ z s)) \ {z})
      (fun x => odometer μ ρ z t x - odometer μ ρ z s x) := by
  have hsub : interior (closure (cluster μ ρ z s)) \ {z} ⊆
      ball (0 : ℂ) ρ \ {z} := fun x hx => ⟨hcompact (interior_subset hx.1), hx.2⟩
  have hcont := ((odometer_continuousOn_and_subharmonic hμ hρ hV hz (hs.trans hst)).1.sub
    (odometer_continuousOn_and_subharmonic hμ hρ hV hz hs).1).mono hsub
  have hle := (odometer_laplacianLE_off_pole hμ hρ hV hz (hs.trans hst)).mono_set hsub
  exact superharmonicOfLaplacianLEStep_holds _ _ (isOpen_interior.sdiff isClosed_singleton)
    hcont (laplacianLE_sub_of_hasLaplacian hle hΔ)

/-- On the punctured regularization, a null cluster frontier removes the
boundary measure from the odometer's distributional Laplacian. -/
theorem odometer_hasLaplacian_on_regularization
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {s : ℝ} (hs : 0 < s)
    (hcompact : closure (cluster μ ρ z s) ⊆ ball 0 ρ)
    (hnull : μ (frontier (cluster μ ρ z s)) = 0) :
    HasLaplacian (odometer μ ρ z s) μ 0
      (interior (closure (cluster μ ρ z s)) \ {z}) := by
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨hopen, _, ν, _, _, hdom, _, hΔ⟩ :=
    cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
      shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hμ hρ hV hz hs
  let C := cluster μ ρ z s
  let U := interior (closure C) \ {z}
  have hfrontsub : frontier C ⊆ ball (0 : ℂ) ρ := frontier_subset_closure.trans hcompact
  have hνnull : ν (frontier C) = 0 := by
    have h := hdom (frontier C)
    rw [Measure.restrict_apply isClosed_frontier.measurableSet,
      Measure.restrict_apply isClosed_frontier.measurableSet,
      inter_eq_self_of_subset_left hfrontsub] at h
    exact le_antisymm (h.trans_eq hnull) bot_le
  have hUball : U ⊆ ball (0 : ℂ) ρ := fun x hx => hcompact (interior_subset hx.1)
  refine ⟨hΔ.1.mono_set hUball, fun φ hφ => ?_⟩
  have hφball : IsTestFunction (ball (0 : ℂ) ρ) φ :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUball⟩
  obtain ⟨hi, _, heq⟩ := hΔ.2 φ hφball
  have hiμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  refine ⟨hiμ, integrable_zero_measure, ?_⟩
  have hφzero (x : ℂ) (hx : x ∉ U) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  have hcluster : ∫ x in C, φ x ∂μ = ∫ x, φ x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [show ∀ᵐ x ∂μ, x ∉ frontier C from ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hnull)] with x hxfr hxC
    apply hφzero x
    intro hxU
    apply hxfr
    rw [← closure_sdiff_interior C, hopen.interior_eq]
    exact ⟨interior_subset hxU.1, hxC⟩
  have hfront : ν.restrict (frontier C) = 0 := Measure.restrict_eq_zero.mpr hνnull
  have hzφ : φ z = 0 := hφzero z (fun hzU => hzU.2 rfl)
  rw [hfront, add_zero, hcluster, integral_smul_measure, integral_dirac, hzφ,
    smul_zero, sub_zero] at heq
  simpa only [integral_zero_measure, sub_zero] using heq

/-- A compactly confined cluster with null frontier is contained, after
regularization, in every later cluster. -/
theorem regularized_cluster_subset_later_cluster_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hcompact : closure (cluster μ ρ z s) ⊆ ball 0 ρ)
    (hnull : μ (frontier (cluster μ ρ z s)) = 0) :
    interior (closure (cluster μ ρ z s)) ⊆ cluster μ ρ z t := by
  obtain ⟨hopen, hconn, _⟩ :=
    cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
      shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hμ hρ hV hz hs
  apply regularized_cluster_subset_later_cluster_of_superharmonicity
    hμ hρ hV hz hs hst hopen hconn.isPreconnected hcompact
  exact superharmonic_odometer_increment_of_hasLaplacian hμ hρ hV hz hs hst hcompact
    (odometer_hasLaplacian_on_regularization hμ hρ hV hz hs hcompact hnull)

/-- Compact containment at the later time suffices for comparison when every
compactly confined positive-time cluster has null frontier. -/
theorem regularized_cluster_subset_later_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    (hnull : ∀ s : ℝ, 0 < s → closure (cluster μ ρ z s) ⊆ ball 0 ρ →
      μ (frontier (cluster μ ρ z s)) = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hcompact : closure (cluster μ ρ z t) ⊆ ball 0 ρ) :
    interior (closure (cluster μ ρ z s)) ⊆ cluster μ ρ z t := by
  have hsub : cluster μ ρ z s ⊆ cluster μ ρ z t :=
    cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hμ hρ hV hz hs hst.le
  have hcompact' := (closure_mono hsub).trans hcompact
  exact regularized_cluster_subset_later_cluster_of_frontier_null
    hμ hρ hV hz hs hst hcompact' (hnull s hs hcompact')

end MatedCRT
