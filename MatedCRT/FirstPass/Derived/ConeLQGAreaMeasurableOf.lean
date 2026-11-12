import MatedCRT.FirstPass.Derived.ConeLQGAreaMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldLaw

/-!
# The LQG area measure of the γ-quantum cone is almost surely measurable

Let `X` be a whole-plane GFF and `B, B'` two standard Brownian motions, with `X` independent of the
pair `(B, B')` and `B` independent of `B'`. For `γ ∈ (0, 2)` the circle-average embedding
`coneFieldOf γ X B B'` of the γ-quantum cone (Duplantier-Miller-Sheffield, Definition 4.10) has an
almost surely measurable γ-LQG area measure `lqgArea γ (coneFieldOf γ X B B')`.

This removes the two hypotheses of `aemeasurable_lqgArea_coneField`:
* `hXA`, the independence of `X` and the radial mating-of-trees cone process `t ↦ A_t − Q t`,
  follows from the continuous version of the radial path (`exists_radialPath`); the argument is the
  one of `indepFun_motConeRadial` in the lean-formalizations module `ConeScaling.RadialPath`;
* `hF`, the almost sure measurability of the cone field, is the first conjunct of
  `map_coneRescaleField_coneFieldOf`.
The parameter bound `γ < Q` is `lqgQ_sub_pos`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling

/-- For `γ ∈ (0, 2)`, `γ < Q = 2/γ + γ/2`. -/
theorem lt_Qc_of_lt_two {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < QuantumZipper.Qc γ := by
  have h := lqgQ_sub_pos hγ hγ2
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by dsimp [lqgQ, QuantumZipper.Qc]
  linarith

/-- If the field `X` is independent of the Brownian pair `(B, B')`, then it is independent of the
radial mating-of-trees cone process `t ↦ A_t − Q t` (`A` the radial process of the γ-quantum cone).
The process is a measurable image of the continuous radial path of `exists_radialPath`. -/
theorem indepFun_motConeRadial_of_indepFun {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {X : Ω → β} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P) :
    IndepFun X (fun ω t =>
      MatedCRTHarmonic.LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) P := by
  obtain ⟨W, -, hXW, hW⟩ := MatedCRTHarmonic.ConeScaling.exists_radialPath hγ hγ2 hB hB' hind
  let G : C(ℝ, ℝ) → (ℝ → ℝ) := fun w t => w t - lqgQ γ * t
  have hG : Measurable G :=
    measurable_pi_iff.2 fun t => (ContinuousMap.measurable_eval t).sub_const _
  refine (hXW.comp measurable_id hG).congr (ae_eq_refl _) ?_
  filter_upwards [hW] with ω hω
  funext t
  simp only [Function.comp_apply, G, hω, MatedCRTHarmonic.LQGCone.motConeRadial]

/-- **The γ-LQG area measure of the γ-quantum cone is almost surely measurable.** For a whole-plane
GFF `X` independent of the Brownian pair `(B, B')`, with `B` independent of `B'`, and `γ ∈ (0, 2)`,
the random measure `ω ↦ lqgArea γ (coneFieldOf γ (X ω) (B · ω) (B' · ω))` is almost surely
measurable. -/
theorem aemeasurable_lqgArea_coneFieldOf {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P)
    (hBB' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    AEMeasurable (fun ω =>
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) P :=
  aemeasurable_lqgArea_coneField hγ hγ2 (lt_Qc_of_lt_two hγ hγ2) hX hB hB' hBB'
    (indepFun_motConeRadial_of_indepFun hγ hγ2 hB hB' hind)
    (MatedCRTHarmonic.ConeScaling.map_coneRescaleField_coneFieldOf hγ hγ2 hX hB hB'
      ⟨hind, hBB'⟩ 1).1

end MatedCRT.Sec1
