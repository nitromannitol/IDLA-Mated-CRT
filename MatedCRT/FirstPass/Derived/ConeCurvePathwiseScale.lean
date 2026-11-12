import MatedCRT.FirstPass.Derived.ConeCurveJointScaleLaw
import LatticeProb.LQG.MassReparamBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-!
# The rescaled space-filling SLE is the area reparametrization of the dilated curve

Pathwise half of the joint scaling of the γ-quantum cone and the space-filling SLE in a mating-of-trees
coupling (Duplantier-Miller-Sheffield, mating of trees, Proposition 4.13(i) together with the scale invariance
of whole-plane space-filling SLE).

Let `h` be the circle-average embedding of the γ-quantum cone of the coupling, `η` the space-filling SLE
parametrized by `γ`-LQG area and `η_L` the same curve in its Lebesgue parametrization, so that `η = η_L ∘ φ` for
an increasing homeomorphism `φ` of `ℝ` fixing `0`. For a level `b > 0` let `R = R_b` be the radius at which the
cone field attains the level `b` and `h_b = h(R ·) + Q log R - γ⁻¹ log b`. Then almost surely, for every `b > 0`,
the curve `t ↦ R⁻¹ η(b t)` is the reparametrization of the dilated curve `t ↦ R⁻¹ η_L(R² t)` by the mass of the
`γ`-LQG area measure of `h_b`.

* `massReparam_dilate_eq_of_massParam`: the deterministic statement. If `η = L ∘ φ` is parametrized by
  `μ`-mass and `μ' A = b⁻¹ μ(R A)`, then `R⁻¹ η(b ·)` is the `μ'`-mass reparametrization of `R⁻¹ L(R² ·)`.
* `ae_massReparam_lqgArea_coneRescaleField_igDilate`: the almost sure statement in the coupling.
* `ae_massReparam_lqgArea_coneFieldOf`: its level-free form, `η` is the area reparametrization of `η_L`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling MatedCRTHarmonic.ConeScaling LQGMetric

/-- The time change `t ↦ (R²)⁻¹ φ(b t)` as an order isomorphism of `ℝ`. -/
noncomputable def dilateTimeChange (φ : ℝ ≃o ℝ) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) : ℝ ≃o ℝ :=
  (OrderIso.mulLeft₀ b hb).trans (φ.trans (OrderIso.mulLeft₀ (R ^ 2)⁻¹ (by positivity)))

theorem dilateTimeChange_apply (φ : ℝ ≃o ℝ) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) (t : ℝ) :
    dilateTimeChange φ hR hb t = (R ^ 2)⁻¹ * φ (b * t) := rfl

/-- **Mass reparametrization commutes with the dilation** (deterministic). If `η = L ∘ φ` for an increasing
homeomorphism `φ` fixing `0`, `η` is parametrized by `μ`-mass, and `μ' A = b⁻¹ μ(R A)` for every set `A`, then the
`μ'`-mass reparametrization of the dilated curve `R⁻¹ L(R² ·)` is `R⁻¹ η(b ·)`. -/
theorem massReparam_dilate_eq_of_massParam {μ μ' : Measure ℂ} {L η : ℝ → ℂ} (φ : ℝ ≃o ℝ)
    (hφ0 : φ 0 = 0) (hη : ∀ t, η t = L (φ t))
    (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hμ' : ∀ A : Set ℂ, μ' A = ENNReal.ofReal b⁻¹ * μ ((fun w => (R : ℂ) * w) '' A)) (t : ℝ) :
    LatticeProb.LQG.massReparam μ' (fun s => (R : ℂ)⁻¹ * L (R ^ 2 * s)) t =
      (R : ℂ)⁻¹ * η (b * t) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  refine LatticeProb.LQG.massReparam_eq_of_massParam μ' _ (fun s => (R : ℂ)⁻¹ * η (b * s))
    (dilateTimeChange φ hR hb) ?_ ?_ ?_ t
  · rw [dilateTimeChange_apply, mul_zero, hφ0, mul_zero]
  · intro s
    rw [dilateTimeChange_apply, ← mul_assoc, mul_inv_cancel₀ hR2, one_mul, hη]
  · intro s u hsu
    have himg : (fun w => (R : ℂ) * w) '' ((fun s => (R : ℂ)⁻¹ * η (b * s)) '' Icc s u) =
        η '' Icc (b * s) (b * u) := by
      rw [image_image, ← image_mul_left_Icc hb.le hsu, image_image]
      congr 1
      funext x
      rw [← mul_assoc, mul_inv_cancel₀ hRc, one_mul]
    rw [hμ', himg, harea _ _ (mul_le_mul_of_nonneg_left hsu hb.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hb.le)]
    congr 1
    field_simp

/-- **The rescaled space-filling SLE of a mating-of-trees coupling** (pathwise half of the joint scaling).
Almost surely, for every level `b₀ > 0`, with `R = coneScale γ γ B B' b₀` and
`h_b = coneRescaleField γ R b₀ h`, the curve `t ↦ R⁻¹ η(b₀ t)` is the reparametrization of the dilated curve
`R⁻¹ η_L(R² ·)` by the mass of the `γ`-LQG area measure of `h_b`. -/
theorem ae_massReparam_lqgArea_coneRescaleField_igDilate {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ b₀ : ℝ, 0 < b₀ → ∀ t : ℝ,
      LatticeProb.LQG.massReparam
          (lqgArea γ (coneRescaleField γ (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) b₀
            (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))))
          (igDilate (coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀) (ηL ω)) t =
        ((coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₀ : ℝ) : ℂ)⁻¹ * η ω (b₀ * t) := by
  have := h.isProbabilityMeasure
  have hvague := MatedCRTHarmonic.LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
    (lt_Qc_of_lt_two hγ hγ2) h.gff h.bm_B h.bm_B' h.indep_cone.2
    (indepFun_motConeRadial_of_indepFun hγ hγ2 h.bm_B h.bm_B' h.indep_cone.1)
  filter_upwards [h.areaParam, hvague,
    MatedCRTHarmonic.LQGCoord.ae_lqgArea_coneRescaleField_holds hγ hγ2 h.gff h.bm_B h.bm_B']
    with ω hap hv hsc b₀ hb₀ t
  obtain ⟨⟨φ, hφ0, hφ⟩, harea⟩ := hap
  exact massReparam_dilate_eq_of_massParam φ hφ0 hφ (harea _ hv) (Real.exp_pos _) hb₀
    (hsc _ (Real.exp_pos _) b₀ hb₀) t

/-- **The space-filling SLE of a mating-of-trees coupling is the area reparametrization of its Lebesgue
parametrization**: almost surely `η = massReparam (lqgArea γ h) η_L`. -/
theorem ae_massReparam_lqgArea_coneFieldOf {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      LatticeProb.LQG.massReparam
          (lqgArea γ (coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))) (ηL ω) t = η ω t := by
  have := h.isProbabilityMeasure
  have hvague := MatedCRTHarmonic.LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
    (lt_Qc_of_lt_two hγ hγ2) h.gff h.bm_B h.bm_B' h.indep_cone.2
    (indepFun_motConeRadial_of_indepFun hγ hγ2 h.bm_B h.bm_B' h.indep_cone.1)
  filter_upwards [h.areaParam, hvague] with ω hap hv t
  obtain ⟨⟨φ, hφ0, hφ⟩, harea⟩ := hap
  exact LatticeProb.LQG.massReparam_eq_of_massParam _ _ _ φ hφ0 hφ (harea _ hv) t

end MatedCRT.Sec1
