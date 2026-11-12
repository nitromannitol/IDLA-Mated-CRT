import MatedCRT.FirstPass.Derived.ConeCurvePathwiseScale
import LatticeProb.Probability.MapRestrictSubtype
import LatticeProb.LQG.ConeRescaleVagueLimit
import LatticeProb.LQG.AreaReparamMeasurable

/-!
# Scaling law of the field and the space-filling SLE of a mating-of-trees coupling

Let `(h, η)` be the `γ`-quantum cone `h = coneFieldOf γ X B B'` of a mating-of-trees coupling and
its space-filling SLE `η`, parametrized by `γ`-LQG mass. For a level `b > 0` let
`R_b = coneScale γ γ B B' b` and `h_b = h(R_b ·) + Q log R_b - γ⁻¹ log b` (`coneRescaleField`).
Then the pair `(h_b, t ↦ R_b⁻¹ η(b t))` has the same law as `(h, η)`
(`map_coneRescaleField_curveScale`; Duplantier-Miller-Sheffield, Prop. 4.13(i) with
Thm. 1.9).

The proof transports the joint law of the field and the Lebesgue-parametrized curve
(`map_coneRescaleField_igDilate_igCurve`) through the area decoder
`(f, c) ↦ (f, massReparam (lqgArea γ f) c)`. That decoder is measurable only on the set of fields
whose dyadic area approximations converge vaguely, which need not be measurable; both `h` and
`h_b` lie in it almost surely, so `LatticeProb.map_comp_eq_of_map_eq_of_ae_mem` applies. The two
sides are identified by the pathwise identities of `ConeCurvePathwiseScale`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling MatedCRTHarmonic.ConeScaling LQGMetric

/-- **Scaling law of the quantum cone and its space-filling SLE**: for every level `b₀ > 0`,
`(h_b, t ↦ R_b⁻¹ η(b₀ t))` has the law of `(h, η)`, where `R_b = coneScale γ γ B B' b₀` and
`h_b = coneRescaleField γ R_b b₀ h`. -/
theorem map_coneRescaleField_curveScale {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b₀ : ℝ} (hb₀ : 0 < b₀) :
    P.map (fun ω =>
        (coneRescaleField γ (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀
            (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)),
          fun t : ℝ =>
            ((coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀ : ℝ) : ℂ)⁻¹ * η ω (b₀ * t))) =
      P.map (fun ω =>
        (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω), fun t : ℝ => η ω t)) := by
  have := h.isProbabilityMeasure
  let R : Ω → ℝ := fun ω => coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀
  let H : Ω → DistC := fun ω => coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω)
  let Y₁ : Ω → DistC × C(ℝ, ℂ) := fun ω => (coneRescaleField γ (R ω) b₀ (H ω), igDilate (R ω) (ηL ω))
  let Y₂ : Ω → DistC × C(ℝ, ℂ) := fun ω => (H ω, ηL ω)
  let S : Set (DistC × C(ℝ, ℂ)) :=
    {f : DistC | ∃ μ, IsVagueLimitC (lqgAreaApprox γ f) μ} ×ˢ (univ : Set C(ℝ, ℂ))
  let G : DistC × C(ℝ, ℂ) → DistC × (ℝ → ℂ) :=
    fun p => (p.1, fun t => LatticeProb.LQG.massReparam (lqgArea γ p.1) p.2 t)
  have hG : Measurable (S.domRestrict G) := LatticeProb.LQG.measurable_areaReparam_domRestrict γ
  have hlaw : P.map Y₁ = P.map Y₂ := map_coneRescaleField_igDilate_igCurve h hγ hγ2 b₀
  have hF := map_coneRescaleField_coneFieldOf hγ hγ2 h.gff h.bm_B h.bm_B'
    ⟨h.indep_cone.1, h.indep_cone.2⟩ b₀
  have hY₂ : AEMeasurable Y₂ P := hF.1.prodMk h.measurable_curves.1.aemeasurable
  obtain ⟨W, hWm, -, hW⟩ := exists_radialPath_indepFun_igCurve h hγ hγ2
  have hR : AEMeasurable R P :=
    (Real.measurable_exp.comp ((measurable_lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀)).comp hWm)).aemeasurable.congr (by
      filter_upwards [hW] with ω hω
      exact (coneScale_eq_exp_lastLevel γ b₀ hω).symm)
  have hD' := measurable_igDilate_uncurry.comp_aemeasurable
    (hR.prodMk h.measurable_curves.1.aemeasurable)
  have hY₁ : AEMeasurable Y₁ P := hF.2.1.prodMk hD'
  have hvague := MatedCRTHarmonic.LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
    (lt_Qc_of_lt_two hγ hγ2) h.gff h.bm_B h.bm_B' h.indep_cone.2
    (indepFun_motConeRadial_of_indepFun hγ hγ2 h.bm_B h.bm_B' h.indep_cone.1)
  have h₁ : ∀ᵐ ω ∂P, Y₁ ω ∈ S := by
    filter_upwards [LatticeProb.LQG.ae_exists_isVagueLimitC_lqgAreaApprox_coneRescaleField hγ hγ2
      h.gff h.bm_B h.bm_B'] with ω hω
    exact ⟨hω _ (Real.exp_pos _) b₀, trivial⟩
  have h₂ : ∀ᵐ ω ∂P, Y₂ ω ∈ S := by
    filter_upwards [hvague] with ω hω
    exact ⟨⟨_, hω⟩, trivial⟩
  have key := LatticeProb.map_comp_eq_of_map_eq_of_ae_mem hY₁ hY₂ hlaw h₁ h₂ hG
  have e₁ : (fun ω => (coneRescaleField γ (R ω) b₀ (H ω),
      fun t : ℝ => ((R ω : ℝ) : ℂ)⁻¹ * η ω (b₀ * t))) =ᵐ[P] fun ω => G (Y₁ ω) := by
    filter_upwards [ae_massReparam_lqgArea_coneRescaleField_igDilate h hγ hγ2] with ω hω
    exact Prod.ext rfl (funext fun t => (hω b₀ hb₀ t).symm)
  have e₂ : (fun ω => (H ω, fun t : ℝ => η ω t)) =ᵐ[P] fun ω => G (Y₂ ω) := by
    filter_upwards [ae_massReparam_lqgArea_coneFieldOf h hγ hγ2] with ω hω
    exact Prod.ext rfl (funext fun t => (hω t).symm)
  exact (Measure.map_congr e₁).trans (key.trans (Measure.map_congr e₂).symm)

end MatedCRT.Sec1
