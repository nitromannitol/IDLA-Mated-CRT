import LatticeProb.Analysis.VagueLimitMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.LQGMetric.Field.LQGMeasureFieldMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Measurability of the γ-LQG area measure of a random field

The γ-LQG area measure `lqgArea γ h` of a field `h` (Duplantier-Sheffield) is the vague limit of the
dyadic circle-average approximations `lqgAreaApprox γ h k`, and the zero measure when no vague
limit exists; it is the decoder `vagueLimitOrZero` of Lattice-Probability applied to these
approximations. For an almost surely measurable random field `F` whose approximations converge
vaguely almost surely, `ω ↦ lqgArea γ (F ω)` is almost surely measurable: the approximations of a
measurable version of `F` have measurable integrals against every compactly supported continuous
test function (the circle average is jointly measurable in the field, the radius and the centre).

For the circle-average embedding of the γ-quantum cone the vague limit exists almost surely
(Bonanno, `MatedCRTHarmonic.LQGCone.ae_isVagueLimitC_coneField`, copied into Lattice-Probability),
so the area measure of the cone field is almost surely measurable as soon as the cone field is.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling

/-- The γ-LQG area measure is the vague-limit decoder applied to the dyadic approximations. -/
theorem lqgArea_eq_vagueLimitOrZero (γ : ℝ) (h : LQGMetric.DistC) :
    lqgArea γ h = LatticeProb.VagueLimit.vagueLimitOrZero (lqgAreaApprox γ h) := rfl

/-- The dyadic density `(ω, z) ↦ 2^{-kγ²/2} e^{γ h_{2^{-k}}(z)}` of a measurable random field is
jointly measurable. -/
theorem measurable_lqgAreaDensity_uncurry {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ)
    {G : Ω → LQGMetric.DistC} (hG : Measurable G) (k : ℕ) :
    Measurable (Function.uncurry fun ω (z : ℂ) =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg (G ω) (dyadicScale k) z)) := by
  have h1 : Measurable fun p : Ω × ℂ => LQGMetric.circleAvg (G p.1) (dyadicScale k) p.2 :=
    LQGMetric.measurable_circleAvg.comp (f := fun p : Ω × ℂ => (G p.1, dyadicScale k, p.2))
      ((hG.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have h2 : Measurable fun p : Ω × ℂ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg (G p.1) (dyadicScale k) p.2) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul h1))
  exact h2

/-- **Measurability of the LQG area measure of a random field.** If the field `F` is almost surely
measurable and its dyadic area approximations have a vague limit almost surely, then
`ω ↦ lqgArea γ (F ω)` is almost surely measurable. -/
theorem aemeasurable_lqgArea_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (γ : ℝ) {F : Ω → LQGMetric.DistC} (hF : AEMeasurable F P)
    (hae : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC (lqgAreaApprox γ (F ω)) μ) :
    AEMeasurable (fun ω => lqgArea γ (F ω)) P := by
  have hGm : Measurable (hF.mk F) := hF.measurable_mk
  have hFG : F =ᵐ[P] hF.mk F := hF.ae_eq_mk
  have hd0 : ∀ k : ℕ, ∀ ω (z : ℂ), 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * LQGMetric.circleAvg (hF.mk F ω) (dyadicScale k) z) :=
    fun k ω z => mul_nonneg (Real.rpow_nonneg (by unfold dyadicScale; positivity) _)
      (Real.exp_pos _).le
  have hG : AEMeasurable (fun ω => lqgArea γ (hF.mk F ω)) P :=
    LatticeProb.VagueLimit.aemeasurable_vagueLimitOrZero (P := P)
      (m := fun k ω => lqgAreaApprox γ (hF.mk F ω) k)
      (fun k f hf _ => LatticeProb.measurable_integral_withDensity_ofReal_uncurry
        (measurable_lqgAreaDensity_uncurry γ hGm k) (hd0 k) hf.measurable)
      (by
        filter_upwards [hae, hFG] with ω hω hωG
        rw [← hωG]
        exact hω)
  exact hG.congr (by filter_upwards [hFG] with ω hω; rw [hω])

/-- **The LQG area measure of the quantum cone field is almost surely measurable**, given a
measurable version of the cone field and the independence of the field from the radial process
(the hypotheses of the almost sure vague convergence of the area approximations). -/
theorem aemeasurable_lqgArea_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < QuantumZipper.Qc γ)
    (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    (hXA : IndepFun X (fun ω t =>
      MatedCRTHarmonic.LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P)
    (hF : AEMeasurable (fun ω =>
      coneField (X ω) (coneRadial γ α (fun s => B s ω) (fun s => B' s ω))) P) :
    AEMeasurable (fun ω =>
      lqgArea γ (coneField (X ω) (coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))) P :=
  aemeasurable_lqgArea_of_aemeasurable γ hF
    (MatedCRTHarmonic.LQGCone.ae_isVagueLimitC_coneField hγ hγ2 hα hX hB hB' hBB' hXA)

end MatedCRT.Sec1
