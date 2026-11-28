import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceLocalMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4G

/-!
# Locality of the area measure of a quantum cone on an annulus

`coneAnnulusLocality` is the first of the three steps of `ConeAnnulusAreaLawEquivalence`
(`ConeAnnulusAreaLawEquivalenceSteps.lean`): the outer data `(e, μ|_{δ < |z| < M})` of the cone `coneField X A`,
`A = coneRadial γ α B B'`, is almost surely a fixed measurable function of the curve `e`, the lateral part of `X`,
the inner path `coneInnerPath α T B` and the outer window `coneOuterWindow (Q - α) S B'`, with times `T, S` depending
only on `δ, M`, and not on `α`.

The proof is the locality of the LQG area measure (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
Invent. Math. 185 (2011); Gwynne–Miller–Sheffield, arXiv:1705.11161, §2.3.1; Harmonic balls in LQG,
arXiv:2208.11795, Fact 2.1 II): the dyadic approximations of the area measure at scales below `δ / 2` read the field
on `{δ < |z| < M}` only through its restriction to the `δ / 2`-thickening, which lies in
`{δ / 2 < |z| < M + δ / 2}`. There the radial function of the cone field (Duplantier–Miller–Sheffield,
arXiv:1409.7055, Definition 4.10) is read off the inner path and the outer window, whose dyadic regularizations
(`regPath`) make the reconstruction a measurable function of the paths for the product σ-algebra. The area measure of the
reconstructed field is decoded by `reconMeasure` (`ConeAnnulusAreaLawEquivalenceLocalMeasure.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-- On the annulus `{δ / 2 < |z| < M + δ / 2}` the radial value read from the inner path (for `t ≥ 0`) and the outer window
(for `t < 0`) is the radial process `coneRadial` of the cone, for continuous Brownian paths `b, b'`. -/
theorem reconRadial_eq_coneRadial {γ α δ M : ℝ} (hδ : 0 < δ) {b b' : ℝ≥0 → ℝ} (hb : Continuous b)
    (hb' : Continuous b') {z : ℂ} (hz : z ∈ thickAnnulus δ M) :
    reconRadial γ (coneInnerPath α (max 0 (-Real.log (δ / 2))) b,
      coneOuterWindow (lqgQ γ - α) (max 0 (Real.log (M + δ / 2))) b') (-Real.log ‖z‖) =
      coneRadial γ α b b' (-Real.log ‖z‖) := by
  obtain ⟨hz1, hz2⟩ := hz
  have hpos : 0 < ‖z‖ := lt_trans (half_pos hδ) hz1
  have hlog1 : Real.log (δ / 2) < Real.log ‖z‖ := Real.log_lt_log (half_pos hδ) hz1
  have hlog2 : Real.log ‖z‖ < Real.log (M + δ / 2) := Real.log_lt_log hpos hz2
  unfold reconRadial coneRadial
  by_cases ht : 0 ≤ -Real.log ‖z‖
  · simp only [ht, ↓reduceIte]
    have hc : Continuous (coneInnerPath α (max 0 (-Real.log (δ / 2))) b) := by
      unfold coneInnerPath
      fun_prop
    rw [regPath_eq_of_continuous hc]
    unfold coneInnerPath
    have hmin : min (((-Real.log ‖z‖).toNNReal : ℝ≥0) : ℝ) (max 0 (-Real.log (δ / 2))) = -Real.log ‖z‖ := by
      rw [Real.coe_toNNReal _ ht]
      exact min_eq_left ((by linarith : -Real.log ‖z‖ ≤ -Real.log (δ / 2)).trans (le_max_right _ _))
    rw [hmin]
  · simp only [ht, ↓reduceIte]
    have hc : Continuous (coneOuterWindow (lqgQ γ - α) (max 0 (Real.log (M + δ / 2))) b') := by
      unfold coneOuterWindow
      have hcc : Continuous fun u : ℝ => b' u.toNNReal + (lqgQ γ - α) * u :=
        (hb'.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
      fun_prop
    rw [regPath_eq_of_continuous hc]
    have hnt : 0 ≤ -(-Real.log ‖z‖) := by linarith [not_le.1 ht]
    have hmin : min (((-(-Real.log ‖z‖)).toNNReal : ℝ≥0) : ℝ) (max 0 (Real.log (M + δ / 2))) =
        -(-Real.log ‖z‖) := by
      rw [Real.coe_toNNReal _ hnt]
      exact min_eq_left ((by linarith : -(-Real.log ‖z‖) ≤ Real.log (M + δ / 2)).trans (le_max_right _ _))
    unfold coneOuterWindow
    simp only []
    rw [hmin]
    simp only [neg_neg, sub_neg_eq_add]

/-- **Locality of the area measure of the cone on an annulus** (Step 1 of `ConeAnnulusAreaLawEquivalence`).
For `0 < δ < M` the times `T = max 0 (-log (δ / 2))` and `S = max 0 (log (M + δ / 2))` and the measurable map
`(e, L, I, O) ↦ (e, reconMeasure γ δ M (L, I, O))` give, for every `α < Q` and every cone `coneField X (coneRadial γ α B B')`,
the almost sure identity `annulusOuterData e (quantumConeArea γ α X B B') δ M = G (e, lateralPart X, I, O)`. -/
theorem coneAnnulusLocality {γ δ M : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) (hδ : 0 < δ) (_hδM : δ < M) :
    ConeAnnulusLocality γ δ M := by
  refine ⟨max 0 (-Real.log (δ / 2)), max 0 (Real.log (M + δ / 2)),
    fun y => (y.1, reconMeasure γ δ M y.2), le_max_left _ _, le_max_left _ _,
    measurable_fst.prodMk ((measurable_reconMeasure γ δ M).comp measurable_snd), ?_⟩
  intro α hα Ω _ P _ X B B' e hX hB hB' hind
  have hVo : IsOpen (offsetOuterAnnulus δ M) := isOpen_ball.sdiff isClosed_closedBall
  have hVb := isBounded_offsetOuterAnnulus δ M
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := rfl
  have hA : MoTPort.IsConeProcess α (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hB hB' hind.2
  have hK : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ / 2 := by
    obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt (half_pos hδ)
    filter_upwards [eventually_ge_atTop K] with k hk
    have e : dyadicScale k = CellScaling.dyadicScale k := rfl
    rw [e, LQGCone.dyadicScale_eq_radius]
    exact hK k hk
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_coneField hγ.1 hγ.2 hα hX hB hB' hind,
    GMS4c.ae_cone_areaApprox_finite_eventually hγ.1 hγ.2 hα hX hB hB' hVb.isCompact_closure, hB.cont, hB'.cont,
    MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hv hfin hBc hB'c hLI
  obtain ⟨μ, hμ⟩ := hv
  set b : ℝ≥0 → ℝ := fun t => B t ω with hb
  set b' : ℝ≥0 → ℝ := fun t => B' t ω with hb'
  have hLI' : LocallyIntegrable (fun z : ℂ => coneRadial γ α b b' (-Real.log ‖z‖)) volume := by
    refine hLI.congr (Eventually.of_forall fun z => ?_)
    have he := LQGCone.coneRadial_eq_Q_add_motConeRadial γ α b b' (-Real.log ‖z‖)
    rw [hQ] at he
    exact he.symm
  set I := coneInnerPath α (max 0 (-Real.log (δ / 2))) b with hI
  set O := coneOuterWindow (lqgQ γ - α) (max 0 (Real.log (M + δ / 2))) b' with hO
  have hprof : reconProfile γ δ M (I, O) =
      (thickAnnulus δ M).indicator (fun z : ℂ => coneRadial γ α b b' (-Real.log ‖z‖)) := by
    funext z
    by_cases hz : z ∈ thickAnnulus δ M
    · simp only [reconProfile, Set.indicator_of_mem hz]
      exact reconRadial_eq_coneRadial hδ hBc hB'c hz
    · simp [reconProfile, Set.indicator_of_notMem hz]
  have hfLI : LocallyIntegrable (reconProfile γ δ M (I, O)) volume := by
    rw [hprof]
    exact hLI'.indicator (measurableSet_thickAnnulus δ M)
  have hloc : LQGMetric.restrictTo (GMS4c.thickOpen (annulusOpen δ M) (δ / 2))
      (coneField (X ω) (coneRadial γ α b b')) =
      LQGMetric.restrictTo (GMS4c.thickOpen (annulusOpen δ M) (δ / 2))
        (reconField γ δ M (lateralPart (X ω), I, O)) := by
    refine GMSCase.restrictTo_add_ofFunC_congr (T := lateralPart (X ω)) hLI' hfLI _ (fun z hz => ?_)
    rw [hprof, Set.indicator_of_mem (thickOpen_subset_thickAnnulus δ M hz)]
  have hcirc : ∀ᶠ k : ℕ in atTop, ∀ z ∈ offsetOuterAnnulus δ M,
      LQGMetric.circleAvg (reconField γ δ M (lateralPart (X ω), I, O)) (dyadicScale k) z =
        LQGMetric.circleAvg (coneField (X ω) (coneRadial γ α b b')) (dyadicScale k) z := by
    filter_upwards [hK] with k hk z hz
    have hpos : 0 < dyadicScale k := by
      unfold dyadicScale
      positivity
    exact (circleAvg_eq_of_restrictTo_eq (V := annulusOpen δ M) hpos hk hloc hz).symm
  have harea : quantumConeArea γ α X B B' ω = μ :=
    LQGCoord.lqgArea_eq_of_isVagueLimitC hμ
  simp only [annulusOuterData, harea]
  rw [reconMeasure_eq hμ hfin hcirc]

end MatedCRT
