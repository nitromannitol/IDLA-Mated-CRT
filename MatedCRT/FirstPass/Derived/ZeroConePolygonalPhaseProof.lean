import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseSteps
import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseCoupling
import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseClock
import MatedCRT.FirstPass.Derived.ZeroConePhaseFactorProof

/-!
# The phase periods of the polygonal observables from the two-clock equality

This file derives `ZeroConePolygonalPhasePeriods D hγ H₀` from the two-clock equality `ZeroConeTiltPhaseEquality D hγ H₀`.

* `ae_period_of_two_shifts`: if `V'({θ + d₁}) = V(θ)` and `V'({θ + d₂}) = V(θ)` for almost every phase `θ`, then
  `V({θ + (d₁ - d₂)}) = V(θ)` for almost every `θ` (translate the second equality by `d₁ - d₂`).
* The bumps `phaseTilt γ j = (γ / (j + 1)) f`, `f` the smooth bump `phaseBump` at `3/8` with support in the closed disk
  of radius `1/8` about `3/8`. The written proof uses a radial bump; it is used only through the property that it is
  smooth with support in the punctured unit disk (the hypothesis of `coneAreaBumpTilt`), which `phaseBump` has.
  The periods are `D_j = ∫ (e^{phaseTilt γ j} - 1) dμ`: positive because `μ` charges the open disk where `f = 1`, and
  at most `(e^{γ/(j+1)} - 1) μ(supp f) → 0`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

/-! ### Two shifted equalities give a period -/

/-- Reducing a phase mod `1` before adding `c` does not change the reduction mod `1` of the sum. -/
theorem toIcoMod_toIcoMod_add (x c : ℝ) :
    toIcoMod (zero_lt_one' ℝ) 0 (toIcoMod (zero_lt_one' ℝ) 0 x + c) = toIcoMod (zero_lt_one' ℝ) 0 (x + c) := by
  rw [← self_sub_toIcoDiv_zsmul (zero_lt_one' ℝ) 0 x, sub_add_eq_add_sub, toIcoMod_sub_zsmul]

/-- **Two shifted equalities give a period.** If, for almost every phase `θ`, `V'({θ + d₁}) = V(θ)` and
`V'({θ + d₂}) = V(θ)`, then `V({θ + (d₁ - d₂)}) = V(θ)` for almost every `θ`. -/
theorem ae_period_of_two_shifts {V V' : ℝ → ℝ} {d₁ d₂ : ℝ}
    (h₁ : ∀ᵐ θ ∂zeroConePhase, V' (toIcoMod (zero_lt_one' ℝ) 0 (θ + d₁)) = V θ)
    (h₂ : ∀ᵐ θ ∂zeroConePhase, V' (toIcoMod (zero_lt_one' ℝ) 0 (θ + d₂)) = V θ) :
    ∀ᵐ θ ∂zeroConePhase, V (toIcoMod (zero_lt_one' ℝ) 0 (θ + (d₁ - d₂))) = V θ := by
  filter_upwards [MatedCRT.ae_zeroConePhase_toIcoMod (d₁ - d₂) h₂, h₁] with θ hθ₂ hθ₁
  rw [← hθ₂, toIcoMod_toIcoMod_add, show θ + (d₁ - d₂) + d₂ = θ + d₁ by ring, hθ₁]

/-! ### The bumps -/

/-- The smooth bump at `3/8` equal to `1` on the closed disk of radius `1/16` and supported in the closed disk of
radius `1/8` about `3/8`. -/
def phaseBumpData : ContDiffBump (3 / 8 : ℂ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- The bump function `f` of `phaseBumpData`. -/
def phaseBump (z : ℂ) : ℝ := phaseBumpData z

/-- The `j`-th tilt `(γ / (j + 1)) f`. -/
def phaseTilt (γ : ℝ) (j : ℕ) (z : ℂ) : ℝ := γ / (j + 1) * phaseBump z

theorem contDiff_phaseTilt (γ : ℝ) (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phaseTilt γ j) :=
  contDiff_const.mul phaseBumpData.contDiff

theorem closedBall_phaseBump_subset :
    Metric.closedBall (3 / 8 : ℂ) (1 / 8) ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h38 : ‖(3 / 8 : ℂ)‖ = 3 / 8 := by
    rw [show (3 / 8 : ℂ) = ((3 / 8 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have hup : ‖z‖ ≤ 1 / 2 := by
    calc ‖z‖ = ‖(z - 3 / 8) + 3 / 8‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - 3 / 8‖ + ‖(3 / 8 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 8 + 3 / 8 := by rw [h38]; linarith
      _ = 1 / 2 := by norm_num
  have hlow : 1 / 4 ≤ ‖z‖ := by
    have := norm_sub_norm_le (3 / 8 : ℂ) z
    rw [h38, norm_sub_rev] at this
    linarith
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    linarith
  · intro h0
    rw [Set.mem_singleton_iff] at h0
    rw [h0, norm_zero] at hlow
    linarith

theorem tsupport_phaseTilt_subset (γ : ℝ) (j : ℕ) :
    tsupport (phaseTilt γ j) ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
  refine (tsupport_mul_subset_right (f := fun _ : ℂ => γ / (j + 1))).trans ?_
  show tsupport (fun z => phaseBumpData z) ⊆ _
  rw [phaseBumpData.tsupport_eq]
  exact closedBall_phaseBump_subset

theorem tsupport_phaseTilt_subset_closedBall (γ : ℝ) (j : ℕ) :
    tsupport (phaseTilt γ j) ⊆ Metric.closedBall (3 / 8 : ℂ) (1 / 8) := by
  refine (tsupport_mul_subset_right (f := fun _ : ℂ => γ / (j + 1))).trans ?_
  show tsupport (fun z => phaseBumpData z) ⊆ _
  rw [phaseBumpData.tsupport_eq]

theorem hasCompactSupport_phaseTilt (γ : ℝ) (j : ℕ) : HasCompactSupport (phaseTilt γ j) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (tsupport_phaseTilt_subset_closedBall γ j)

theorem phaseTilt_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (j : ℕ) (z : ℂ) : 0 ≤ phaseTilt γ j z :=
  mul_nonneg (div_nonneg hγ (by positivity)) (phaseBumpData.nonneg)

theorem phaseTilt_le {γ : ℝ} (hγ : 0 ≤ γ) (j : ℕ) (z : ℂ) : phaseTilt γ j z ≤ γ / (j + 1) :=
  mul_le_of_le_one_right (div_nonneg hγ (by positivity)) phaseBumpData.le_one

theorem phaseTilt_eq_of_mem {γ : ℝ} (j : ℕ) {z : ℂ} (hz : z ∈ Metric.ball (3 / 8 : ℂ) (1 / 16)) :
    phaseTilt γ j z = γ / (j + 1) := by
  rw [phaseTilt, phaseBump, phaseBumpData.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), mul_one]

theorem phaseTilt_eq_zero_of_not_mem (γ : ℝ) (j : ℕ) {z : ℂ} (hz : z ∉ Metric.closedBall (3 / 8 : ℂ) (1 / 8)) :
    phaseTilt γ j z = 0 := by
  have : phaseBumpData z = 0 := by
    by_contra h
    exact hz (phaseBumpData.tsupport_eq ▸ subset_tsupport _ h)
  rw [phaseTilt, phaseBump, this, mul_zero]

/-! ### The periods -/

/-- The mass `∫ (e^{phaseTilt γ j} - 1) dμ` of the tilt. -/
def tiltMass (γ : ℝ) (j : ℕ) (μ : Measure ℂ) : ℝ := ∫ z, (Real.exp (phaseTilt γ j z) - 1) ∂μ

/-- `e^{phaseTilt γ j} - 1` vanishes off the closed disk of radius `1/8` about `3/8`. -/
theorem exp_phaseTilt_sub_one_eq_indicator (γ : ℝ) (j : ℕ) :
    (fun z => Real.exp (phaseTilt γ j z) - 1) =
      (Metric.closedBall (3 / 8 : ℂ) (1 / 8)).indicator (fun z => Real.exp (phaseTilt γ j z) - 1) := by
  funext z
  by_cases hz : z ∈ Metric.closedBall (3 / 8 : ℂ) (1 / 8)
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, phaseTilt_eq_zero_of_not_mem γ j hz, Real.exp_zero, sub_self]

theorem exp_phaseTilt_sub_one_mem_Icc {γ : ℝ} (hγ : 0 ≤ γ) (j : ℕ) (z : ℂ) :
    Real.exp (phaseTilt γ j z) - 1 ∈ Icc 0 (Real.exp (γ / (j + 1)) - 1) := by
  constructor
  · rw [sub_nonneg]
    exact Real.one_le_exp (phaseTilt_nonneg hγ j z)
  · rw [sub_le_sub_iff_right, Real.exp_le_exp]
    exact phaseTilt_le hγ j z

theorem integrable_exp_phaseTilt_sub_one {γ : ℝ} (hγ : 0 ≤ γ) (j : ℕ) {μ : Measure ℂ}
    (hμ : μ (Metric.closedBall (3 / 8 : ℂ) (1 / 8)) < ⊤) :
    Integrable (fun z => Real.exp (phaseTilt γ j z) - 1) μ := by
  have hK : MeasurableSet (Metric.closedBall (3 / 8 : ℂ) (1 / 8)) := Metric.isClosed_closedBall.measurableSet
  have hcont : Continuous (fun z => Real.exp (phaseTilt γ j z) - 1) :=
    ((contDiff_phaseTilt γ j).continuous.rexp).sub continuous_const
  rw [exp_phaseTilt_sub_one_eq_indicator, integrable_indicator_iff hK]
  refine Measure.integrableOn_of_bounded hμ.ne hcont.aestronglyMeasurable (Real.exp (γ / (j + 1)) - 1) ?_
  refine ae_of_all _ fun z => ?_
  obtain ⟨h0, h1⟩ := exp_phaseTilt_sub_one_mem_Icc hγ j z
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- **The periods are positive.** If `μ` is finite on the closed disk of radius `1/8` about `3/8` and charges the open
disk of radius `1/16`, then `tiltMass γ j μ > 0`. -/
theorem tiltMass_pos {γ : ℝ} (hγ : 0 < γ) (j : ℕ) {μ : Measure ℂ}
    (hμ : μ (Metric.closedBall (3 / 8 : ℂ) (1 / 8)) < ⊤) (hpos : 0 < μ (Metric.ball (3 / 8 : ℂ) (1 / 16))) :
    0 < tiltMass γ j μ := by
  have hint := integrable_exp_phaseTilt_sub_one hγ.le j hμ
  rw [tiltMass, integral_pos_iff_support_of_nonneg
    (fun z => (exp_phaseTilt_sub_one_mem_Icc hγ.le j z).1) hint]
  refine hpos.trans_le (measure_mono fun z hz => ?_)
  rw [Function.mem_support, phaseTilt_eq_of_mem j hz, sub_ne_zero]
  exact (Real.one_lt_exp.2 (div_pos hγ (by positivity))).ne'

/-- **The periods tend to `0`.** If `μ` is finite on the closed disk of radius `1/8` about `3/8`, then
`tiltMass γ j μ → 0` as `j → ∞`. -/
theorem tendsto_tiltMass {γ : ℝ} (hγ : 0 ≤ γ) {μ : Measure ℂ}
    (hμ : μ (Metric.closedBall (3 / 8 : ℂ) (1 / 8)) < ⊤) :
    Tendsto (fun j : ℕ => tiltMass γ j μ) atTop (𝓝 0) := by
  set K := Metric.closedBall (3 / 8 : ℂ) (1 / 8)
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hbound : ∀ j : ℕ, tiltMass γ j μ ≤ (Real.exp (γ / (j + 1)) - 1) * (μ K).toReal := by
    intro j
    rw [tiltMass, exp_phaseTilt_sub_one_eq_indicator, integral_indicator hK]
    calc ∫ z in K, (Real.exp (phaseTilt γ j z) - 1) ∂μ ≤ ∫ _z in K, (Real.exp (γ / (j + 1)) - 1) ∂μ := by
          refine setIntegral_mono_on ?_ (integrableOn_const hμ.ne) hK fun z _ =>
            (exp_phaseTilt_sub_one_mem_Icc hγ j z).2
          exact (integrable_exp_phaseTilt_sub_one hγ j hμ).integrableOn
      _ = (Real.exp (γ / (j + 1)) - 1) * (μ K).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm, Measure.real]
  have hnonneg : ∀ j : ℕ, 0 ≤ tiltMass γ j μ := fun j =>
    integral_nonneg fun z => (exp_phaseTilt_sub_one_mem_Icc hγ j z).1
  have hlim : Tendsto (fun j : ℕ => (Real.exp (γ / (j + 1)) - 1) * (μ K).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => γ / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun j : ℕ => Real.exp (γ / ((j : ℝ) + 1)) - 1) atTop (𝓝 0) := by
      have := (Real.continuous_exp.tendsto 0).comp h1
      simpa [Function.comp_def] using this.sub_const 1
    simpa using h2.mul_const (μ K).toReal
  exact squeeze_zero hnonneg hbound hlim

/-! ### The phase periods -/

section ZeroCone

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The phase periods of the polygonal observables from the two-clock equality.** If the polygonal configuration of
the data is almost surely the configuration of the shifted zero-cone curve with the multiplicities read off the curve
(`hcode`, the edge-count identity), then `ZeroConeTiltPhaseEquality D hγ H₀` gives `ZeroConePolygonalPhasePeriods D hγ H₀`
with the periods `D_j = ∫ (e^{phaseTilt γ j} - 1) dμ`: the equalities for the two time tails give the period
`d_+ - d_-` (`ae_period_of_two_shifts`), which is `D_j` (`ClockDatum.clockOffset_true_sub_false`). -/
theorem zeroConePolygonalPhasePeriods_of_tiltPhaseEquality
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) (H₀ : GMSSpace)
    (hcode : ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G → ∀ᵐ p ∂P.prod zeroConePhase,
      polygonalConfig H₀ (GMS310Transfer.phaseShiftedData η₀ G 1 p) =
        polygonalConfig H₀ (curveTimeTranslate p.2 (η₀ p.1),
          fun j k => cellSideMult 1 ⇑(curveTimeTranslate p.2 (η₀ p.1)) j k))
    (heq : ZeroConeTiltPhaseEquality D hγ H₀) : ZeroConePolygonalPhasePeriods D hγ H₀ := by
  intro G hG Φ hΦm hΦb hΦinv
  have hE : ∀ (j : ℕ) (b : Bool), ∀ᵐ ω ∂P, ∀ᵐ θ ∂zeroConePhase,
      phaseObs Φ H₀ (massReparamCurve (tiltArea (phaseTilt γ j)
          (ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω))) (ηL ω))
        (toIcoMod (zero_lt_one' ℝ) 0 (θ + clockOffset (phaseTilt γ j)
          (ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω)) (ηL ω) b)) =
      phaseObs Φ H₀ (η₀ ω) θ := fun j b =>
    Measure.ae_ae_of_ae_prod (heq Φ hΦm hΦb hΦinv (phaseTilt γ j) (contDiff_phaseTilt γ j)
      (tsupport_phaseTilt_subset γ j) (phaseTilt_nonneg hγ.1.le j) b)
  have hc : ∀ᵐ ω ∂P, ∀ᵐ θ ∂zeroConePhase,
      polygonalConfig H₀ (GMS310Transfer.phaseShiftedData η₀ G 1 (ω, θ)) =
        polygonalConfig H₀ (curveTimeTranslate θ (η₀ ω),
          fun j k => cellSideMult 1 ⇑(curveTimeTranslate θ (η₀ ω)) j k) :=
    Measure.ae_ae_of_ae_prod (hcode G hG)
  filter_upwards [ae_all_iff.2 fun j => ae_all_iff.2 fun b => hE j b, hc, ae_zeroConeAreaFacts D hγ]
    with ω hEω hcω hfacts
  obtain ⟨hfin, hpos, ⟨φ, hφ0, hφ, harea⟩, hsurj, hprop, h0, -⟩ := hfacts
  set μ := ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) with hμ
  have hK : μ (Metric.closedBall (3 / 8 : ℂ) (1 / 8)) < ⊤ := hfin _ (isCompact_closedBall _ _)
  refine ⟨fun j => tiltMass γ j μ,
    fun j => tiltMass_pos hγ.1 j hK (hpos _ Metric.isOpen_ball ⟨3 / 8, Metric.mem_ball_self (by norm_num)⟩),
    tendsto_tiltMass hγ.1.le hK, fun j => ?_⟩
  have hcurve : (fun u => ηL ω (φ u)) = ⇑(η₀ ω) := funext fun u => (hφ u).symm
  have H : ClockDatum (phaseTilt γ j) μ (ηL ω) φ :=
    { proper := hprop
      surjective := hsurj
      map_zero := h0
      finiteOnCompacts := ⟨fun K hK' => hfin K hK'⟩
      phi_zero := hφ0
      area := fun s t hst => by rw [hcurve]; exact harea s t hst
      continuous_g := (contDiff_phaseTilt γ j).continuous
      compactSupport_g := hasCompactSupport_phaseTilt γ j }
  have hper := ae_period_of_two_shifts (hEω j true) (hEω j false)
  rw [H.clockOffset_true_sub_false] at hper
  filter_upwards [hper, hcω, MatedCRT.ae_zeroConePhase_toIcoMod (tiltMass γ j μ) hcω] with θ h1 h2 h3
  rw [h3, h2]
  exact h1

end ZeroCone

end MatedCRT.ZeroConePolygonal
