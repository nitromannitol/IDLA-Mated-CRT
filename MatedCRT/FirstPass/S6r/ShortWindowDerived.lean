import MatedCRT.FirstPass.S6r.ShortWindowFrozen
import MatedCRT.FirstPass.S2VG.Literature
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence

/-!
# hprev of the short-window good-radius prevalence, with the whole-plane steps derived

Follow-up to `ShortWindowFrozen.lean` (`hprev_of_shortWindow_frozen`), following the repair plan
(patch items 2 and 4).

* Item 4 (`coneMeanZeroRestriction_of_fullB1Law`): `ConeMeanZeroRestrictionStep` from the full field law on `B_1`
  (`ConeWholePlaneFieldLawStep`, the frozen `FPConeWholePlaneFieldLaw`) by the measurable projection onto the
  mean-zero pairings. The full field law needs the LQG measure of the cone field, and `IsQuantumCone` does not
  supply one. That existence is kept as the named hypothesis `hμ` (its exact type in the signature). It is a
  missing input, not a proved step (see the report).
* Item 2 (`wholePlaneLQGCoordinateChangeStep_of_coordChange`): `WholePlaneLQGCoordinateChangeStep` from the cited
  coordinate change of the LQG measure (`LitCoordChange`, class b, Duplantier-Sheffield 2011 Prop. 2.1), the proved
  affine invariance `wholePlaneGFFAffineInvariance_proved`, and the constant-shift identity proved here
  (`sdw_isLQGLimit_shift`). The factor `c = exp(γ κ)` with `κ = h_r(z) + Q log r` is kept explicit.
* `hprev_of_shortWindow_derived`: `hprev_of_shortWindow_frozen` with `h2` discharged as above and `hR` discharged by
  item 4, so that `hμ` and `hCC` are the only new named hypotheses (`h0` and `hV` stay frozen as before).

The argument uses the notation of Armstrong-Kuusi-Mourrat (cone and field restriction) and Duplantier-Sheffield (LQG
measure, coordinate change, quantum cone).
-/

open MeasureTheory Filter Topology Metric
open HarmonicBalls
open MatedCRT

namespace MatedCRT.Lemma68Window

/-- The approximations of the LQG measure of a field shifted by a constant `κ`: `ε^{γ²/2} e^{γ(h_ε + κ)} dz`
equals `e^{γκ}` times the approximation of `h`. (Duplantier-Sheffield 2011, eq. (1.1) with a constant shift.) -/
theorem sdw_lqgApprox_add_const (γ κ : ℝ) (g : ℝ → ℂ → ℝ) (δ : ℝ) :
    HarmonicBalls.lqgApprox γ (fun ε z => g ε z + κ) δ =
      ENNReal.ofReal (Real.exp (γ * κ)) • HarmonicBalls.lqgApprox γ g δ := by
  unfold HarmonicBalls.lqgApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  have hexp : Real.exp (γ * (g δ z + κ)) = Real.exp (γ * κ) * Real.exp (γ * g δ z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos (γ * κ)).le, hexp]
  congr 1
  ring

/-- **Constant shift of the LQG limit.** If `ε^{γ²/2} e^{γ(g_ε + κ)} dz` converges vaguely to `ν`, then
`ε^{γ²/2} e^{γ g_ε} dz` converges vaguely to `e^{-γκ} ν` (the measure of `g` is the one of `g + κ` times `e^{-γκ}`). -/
theorem sdw_isLQGLimit_shift {γ κ : ℝ} {g : ℝ → ℂ → ℝ} {ν : Measure ℂ}
    (h : IsLQGLimit γ (fun ε z => g ε z + κ) ν) :
    IsLQGLimit γ g (ENNReal.ofReal (Real.exp (-(γ * κ))) • ν) := by
  have hν : IsLocallyFiniteMeasure ν := h.isLocallyFiniteMeasure
  have hloc : IsLocallyFiniteMeasure (ENNReal.ofReal (Real.exp (-(γ * κ))) • ν) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hfin⟩ := hν.finiteAtNhds x
    refine ⟨s, hs, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hloc, fun f hf hc => ?_⟩
  have key : ∀ k : ℕ, ∫ z, f z ∂(HarmonicBalls.lqgApprox γ g (dyadicScale k)) =
      Real.exp (-(γ * κ)) * ∫ z, f z ∂(HarmonicBalls.lqgApprox γ (fun ε z => g ε z + κ) (dyadicScale k)) := by
    intro k
    rw [sdw_lqgApprox_add_const, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
      ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact Tendsto.congr (fun k => (key k).symm) ((h.tendsto_integral f hf hc).const_mul _)

/-- The coordinate-change constant `κ = h_r(z) + Q log r` of the affine map `x ↦ r x + z`,
for a circle-average family `h`: the circle averages of `h(r · + z) - h_r(z)` plus `κ` are those of
`h(r · + z) + Q log r`. -/
noncomputable def sdw_coordKappa (γ r : ℝ) (z : ℂ) (h : ℝ → ℂ → ℝ) : ℝ :=
  h ‖(r : ℂ)‖ z + lqgQ γ * Real.log ‖(r : ℂ)‖

/-- **h2, derived.** The whole-plane LQG coordinate change `WholePlaneLQGCoordinateChangeStep` (Steps/Sec6/AnnulusHit.lean:65)
from the cited coordinate change of the LQG measure `LitCoordChange` (= `LQGMeasureCoordChange P γ 0`, HB
`Proposed/LQG.lean:116`), the proved affine invariance of the whole-plane GFF, and the constant-shift identity
`sdw_isLQGLimit_shift`. The new field is `h(r · + z) - h_r(z)` and its measure is `e^{-γκ}` times the pushforward of `μ`
under `x ↦ (x - z)/r`, with `c = e^{γκ}`. -/
theorem wholePlaneLQGCoordinateChangeStep_of_coordChange (hCC : MatedCRT.S2VG.LitCoordChange) :
    WholePlaneLQGCoordinateChangeStep := by
  intro γ hγ hγ2 Ω' _ P' hC' hcirc' μ' hP' hwp hμ' r hr z
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQ : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    positivity
  have hfc : ∀ ω, fieldCircleAverage 0 (hcirc' ω) = hcirc' ω := fun ω => by
    funext ε x
    simp [fieldCircleAverage]
  have hfield : IsLQGMeasureOfField P' γ 0 hcirc' μ' := by
    unfold IsLQGMeasureOfField IsLQGMeasure
    simp only [hfc]
    exact hμ'
  have hA := hCC Ω' P' γ hC' hcirc' hwp hγ hγ2 hQ μ' hfield
  have hG := HarmonicBalls.wholePlaneGFFAffineInvariance_proved P' hC' hcirc' hwp (r : ℂ) hr0 z
  refine ⟨_, _, fun ω => ENNReal.ofReal (Real.exp (-(γ * sdw_coordKappa γ r z (hcirc' ω)))) •
      (μ' ω).map (fun x => (x - z) / (r : ℂ)), fun ω => ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ r z (hcirc' ω))),
    hG, ?_, ?_⟩
  · filter_upwards [hA] with ω hω
    have h1 := hω (r : ℂ) hr0 z
    apply sdw_isLQGLimit_shift
    convert h1 using 1
    funext ε w
    simp only [fieldCircleAverage, sdw_coordKappa, zero_mul, sub_zero]
    ring
  · refine Filter.Eventually.of_forall fun ω => ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos _) |>.ne',
      ENNReal.ofReal_ne_top, ?_⟩
    rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos (γ * sdw_coordKappa γ r z (hcirc' ω))).le, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_smul]

/-- The mean-zero pairing projection: from the pairings and circle averages on `B_1` to the pairings with the
test functions `φ` supported in `B_1` with `∫ φ = 0` (the measurable projection). -/
def sdw_meanZeroProjection :
    ((TestB1 → ℝ) × (CircleB1 → ℝ)) →
      ({φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ ∧ ∫ x, φ x = 0} → ℝ) :=
  fun F φ => F.1 ⟨φ.1, φ.2.1⟩

theorem sdw_meanZeroProjection_measurable : Measurable sdw_meanZeroProjection :=
  Measurable.of_eval fun φ => (measurable_pi_apply (⟨φ.1, φ.2.1⟩ : TestB1)).comp measurable_fst

/-- **Item 4, derived from the full field law.** `ConeMeanZeroRestrictionStep` (Steps/Sec6/GoodAnnulusPrevalence.lean:59)
from the full law of the cone field on `B_1` (`ConeWholePlaneFieldLawStep`, the frozen `FPConeWholePlaneFieldLaw`) by the
measurable projection `sdw_meanZeroProjection` (`IdentDistrib` pushed forward, `AEMeasurable.map_map_of_aemeasurable`).

The named hypothesis `hμ` (the LQG measure of a quantum cone exists) is needed because `ConeWholePlaneFieldLawStep`
quantifies over an LQG measure `μ` of the cone (`IsConeField`), and `IsQuantumCone` does not provide one.
This is not in the repository; see the report. -/
theorem coneMeanZeroRestriction_of_fullB1Law (hB1 : ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ) :
    ConeMeanZeroRestrictionStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc hP hcone Ω' _ P' hC' hcirc' hwp
  obtain ⟨μ, hμP⟩ := hμ γ hγ hγ2 Ω P hC hcirc hP hcone
  have hid := hB1 γ hγ hγ2 Ω P hC hcirc μ ⟨hP, hcone, hμP⟩ Ω' P' hC' hcirc'
    hwp.isProbabilityMeasure hwp
  have e1 : P.map (sdw_meanZeroProjection ∘ coneFieldOnB1 hC hcirc) =
      P'.map (sdw_meanZeroProjection ∘ wholePlaneFieldOnB1 γ hC' hcirc') := by
    rw [← AEMeasurable.map_map_of_aemeasurable sdw_meanZeroProjection_measurable.aemeasurable hid.aemeasurable_fst,
      ← AEMeasurable.map_map_of_aemeasurable sdw_meanZeroProjection_measurable.aemeasurable hid.aemeasurable_snd,
      hid.map_eq]
  exact e1

/-- **hprev of the short-window good-radius prevalence, with the whole-plane steps derived.** The conclusion of
`shortWindowGoodRadiusPrevalence_closed` with `h2` derived from `hCC` (item 2) and `hR` derived from the full field law
`hB1` and the cone LQG measure `hμ` (item 4); `h0` and `hV` are the frozen Props `FPWholePlaneLQGExistence` and
`FPWholePlaneUpperVolumeTail`, as in `hprev_of_shortWindow_frozen`. -/
theorem hprev_of_shortWindow_derived (h0 : MatedCRT.FPWholePlaneLQGExistence)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hV : MatedCRT.FPWholePlaneUpperVolumeTail)
    (hB1 : ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ) :
    ShortWindowGoodRadiusPrevalenceStmt :=
  shortWindowGoodRadiusPrevalence_closed h0 (wholePlaneLQGCoordinateChangeStep_of_coordChange hCC) hV
    (coneMeanZeroRestriction_of_fullB1Law hB1 hμ)

#print axioms MatedCRT.Lemma68Window.sdw_lqgApprox_add_const
#print axioms MatedCRT.Lemma68Window.sdw_isLQGLimit_shift
#print axioms MatedCRT.Lemma68Window.wholePlaneLQGCoordinateChangeStep_of_coordChange
#print axioms MatedCRT.Lemma68Window.coneMeanZeroRestriction_of_fullB1Law
#print axioms MatedCRT.Lemma68Window.hprev_of_shortWindow_derived

end MatedCRT.Lemma68Window
