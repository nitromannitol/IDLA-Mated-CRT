import MatedCRT.Proofs.Field.WholePlaneLQGCoord
import MatedCRT.Proofs.Field.WholePlaneAffine

/-!
# The LQG coordinate change under the continuum definition of the LQG measure

The paper defines the γ-LQG area measure as an a.s. weak limit over all scales (corrected draft, eq:measure-lim,
line 467): `μ_h = lim_{ε → 0} ε^{γ²/2} e^{γ h_ε(z)} dz`. Harmonic-Balls `IsLQGLimit` (`Defs/LQG.lean`) uses only the
dyadic scales `ε = 2^{-k}`. This file works with the continuum predicate `IsLQGLimitCont` (the paper's eq:measure-lim).
For it, the coordinate change of the affine transform `h ↦ h(r · + z) - h_r(z)` needs no convergence input: the
approximation identity `integral_lqgApprox_affine` (`WholePlaneLQGCoord.lean`) transports the limit along `ε ↦ r ε`.

The step `WholePlaneLQGCoordinateChangeStepCont` is `WholePlaneLQGCoordinateChangeStep` (`Steps/Sec6/AnnulusHit.lean`)
with `IsLQGMeasure` replaced by `IsLQGMeasureCont`; it is proved here.
-/

namespace MatedCRT.Field

open MeasureTheory Filter Topology HarmonicBalls

/-- The γ-LQG area measure of the paper (eq:measure-lim): vague convergence of `ε^{γ²/2} e^{γ h_ε(z)} dz` as
`ε → 0⁺` over all scales, to a locally finite measure. -/
def IsLQGLimitCont (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) : Prop :=
  IsLocallyFiniteMeasure m ∧ ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun ε : ℝ => ∫ x, f x ∂(lqgApprox γ hε ε)) (𝓝[Set.Ioi 0] 0) (𝓝 (∫ x, f x ∂m))

/-- The continuum LQG measure of a random field, almost surely (eq:measure-lim). -/
def IsLQGMeasureCont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hε : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) : Prop :=
  ∀ᵐ ω ∂P, IsLQGLimitCont γ (hε ω) (μ ω)

/-- Multiplication by `r > 0` preserves `𝓝[>] 0`. -/
theorem tendsto_mul_nhdsWithin_pos {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ => r * ε) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h0 : Tendsto (fun ε : ℝ => r * ε) (𝓝 (0 : ℝ)) (𝓝 (r * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun ε hε => mul_pos hr hε

/-- **The coordinate change of the continuum LQG measure.** If `μ` is the continuum LQG measure of `h`, then
`c⁻¹ · μ((· - z)/r)` is the continuum LQG measure of the affine transform `affH r z h`. -/
theorem isLQGLimitCont_affine (γ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (h : ℝ → ℂ → ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → Continuous (h ε)) (m : Measure ℂ) (hm : IsLQGLimitCont γ h m) :
    IsLQGLimitCont γ (affH r z h)
      (ENNReal.ofReal (coordConst γ r h z)⁻¹ • m.map (fun x => (x - z) / (r : ℂ))) := by
  obtain ⟨hLF, hT⟩ := hm
  have hc0 : (0 : ℝ) < coordConst γ r h z := coordConst_pos γ hr h z
  have hLFmap : IsLocallyFiniteMeasure (m.map (fun x => (x - z) / (r : ℂ))) := by
    have := hLF
    exact isLocallyFiniteMeasure_map_homeo m (divAffHomeo z hr)
  refine ⟨isLocallyFiniteMeasure_ofReal_smul _ _, fun g hg hgc => ?_⟩
  have hmeasS : Measurable (fun x : ℂ => (x - z) / (r : ℂ)) :=
    ((continuous_id.sub continuous_const).div_const _).measurable
  have hgS : Continuous (fun x : ℂ => g ((x - z) / (r : ℂ))) :=
    hg.comp ((continuous_id.sub continuous_const).div_const _)
  have hgSc : HasCompactSupport (fun x : ℂ => g ((x - z) / (r : ℂ))) :=
    hasCompactSupport_comp_div g hgc hr z
  have e2 : ∫ x, g x ∂(ENNReal.ofReal (coordConst γ r h z)⁻¹ • m.map (fun x => (x - z) / (r : ℂ)))
      = (coordConst γ r h z)⁻¹ * ∫ x, g ((x - z) / (r : ℂ)) ∂m := by
    rw [integral_smul_measure, integral_map hmeasS.aemeasurable hg.aestronglyMeasurable,
      ENNReal.toReal_ofReal (inv_nonneg.2 hc0.le), smul_eq_mul]
  rw [e2]
  have hlim := (hT _ hgS hgSc).comp (tendsto_mul_nhdsWithin_pos hr)
  have hevent : (fun ε : ℝ => (coordConst γ r h z)⁻¹ * ∫ x, g ((x - z) / (r : ℂ)) ∂(lqgApprox γ h (r * ε)))
      =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)] (fun ε : ℝ => ∫ x, g x ∂(lqgApprox γ (affH r z h) ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_lqgApprox_affine γ hr z h hc hε g).symm
  exact Tendsto.congr' hevent (hlim.const_mul _)

/-- **The coordinate-change step for the continuum LQG measure.** This is `WholePlaneLQGCoordinateChangeStep`
(`Steps/Sec6/AnnulusHit.lean`) with `IsLQGMeasure` replaced by `IsLQGMeasureCont` (eq:measure-lim). -/
def WholePlaneLQGCoordinateChangeStepCont : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureCont P' γ hcirc' μ' →
  ∀ (r : ℝ), 0 < r → ∀ z : ℂ, ∃ (hC'' : Ω' → (ℂ → ℝ) → ℝ) (hcirc'' : Ω' → ℝ → ℂ → ℝ)
    (μ'' : Ω' → Measure ℂ) (c : Ω' → ENNReal),
    IsWholePlaneGFF P' hC'' hcirc'' ∧ IsLQGMeasureCont P' γ hcirc'' μ'' ∧
    ∀ᵐ ω ∂P', c ω ≠ 0 ∧ c ω ≠ ⊤ ∧ (μ' ω).map (fun x => (x - z) / (r : ℂ)) = c ω • μ'' ω

/-- **The coordinate-change step for the continuum LQG measure holds.** The witnesses are the affine transform of
the pairings and circle averages (`affHC`, `affHcirc`), the measure `c⁻¹ • μ'((· - z)/r)` and the constant
`c = r^{γQ} e^{γ h_r(z)}` (`coordConst`). -/
theorem wholePlaneLQGCoordinateChangeStepCont_holds : WholePlaneLQGCoordinateChangeStepCont := by
  intro γ hγ hγ2 Ω' _ P' hC' hcirc' μ' hP' hwp hμ r hr z
  have hμ' : ∀ᵐ ω ∂P', IsLQGLimitCont γ (hcirc' ω) (μ' ω) := hμ
  refine ⟨affHC r z hC' hcirc', affHcirc r z hcirc',
    fun ω => ENNReal.ofReal (coordConst γ r (hcirc' ω) z)⁻¹ •
      (μ' ω).map (fun x => (x - z) / (r : ℂ)),
    fun ω => ENNReal.ofReal (coordConst γ r (hcirc' ω) z),
    isWholePlaneGFF_affine hwp hr z, ?_, ?_⟩
  · unfold IsLQGMeasureCont
    filter_upwards [hμ', hwp.ae_continuousOn_circle] with ω hω hcω
    have hc : ∀ ε : ℝ, 0 < ε → Continuous (hcirc' ω ε) := fun ε hε => by
      have h1 : ContinuousOn (fun x : ℂ => hcirc' ω ε x) Set.univ :=
        hcω.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun x _ => ⟨hε, Set.mem_univ _⟩)
      exact continuousOn_univ.1 h1
    exact isLQGLimitCont_affine γ hr z (hcirc' ω) hc (μ' ω) hω
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hpos : (0 : ℝ) < coordConst γ r (hcirc' ω) z := coordConst_pos γ hr _ z
    have hpos' : ENNReal.ofReal (coordConst γ r (hcirc' ω) z) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hpos).ne'
    refine ⟨hpos', ENNReal.ofReal_ne_top, ?_⟩
    dsimp only
    rw [smul_smul, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_smul]

end MatedCRT.Field

