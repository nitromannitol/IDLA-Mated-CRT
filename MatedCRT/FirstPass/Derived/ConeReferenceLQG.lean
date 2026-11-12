import MatedCRT.FirstPass.Derived.ConeReferenceIsCone
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGLimitContinuousPerturbation
import LatticeProb.LQG.MassFunctional
import LatticeProb.LQG.LocalMeasureKernel2

/-!
# The γ-LQG measure of the explicit cone data

Let `h^ℂ` be a whole-plane GFF with circle averages `hcirc` and `m` the γ-LQG measure of `h^ℂ - γ log |·|`, i.e.
the vague dyadic limit of `ε^{γ²/2} e^{γ (h^ℂ_ε - γ (log |·|)_ε)} dz`. The cone field is obtained by adding to
`h^ℂ - γ log |·|` the continuous radial correction `F = coneRefField hcirc w`, whose circle averages converge to
`F` uniformly on compact sets along the dyadic scales. By the continuous-perturbation theorem the γ-LQG measure of
the cone field is `e^{γ F} m` (`isLQGLimit_coneRef`), and so, almost surely in the field and for every path, the
product-space random measure `(μ₀ ω).withDensity (e^{γ F})` is the γ-LQG measure of the cone circle averages
(`isLQGMeasure_coneRef`).
-/

open MeasureTheory Set Filter HarmonicBalls MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- The γ-LQG measure of the cone field `h^ℂ - γ log |·| + F`: the measure `m` of `h^ℂ - γ log |·|` times the
density `e^{γ F}`, `F = coneRefField hcirc w`. -/
noncomputable def coneRefMeasure (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) (m : Measure ℂ) : Measure ℂ :=
  m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * coneRefField hcirc w z))

/-- At each fixed positive radius, the circle averages of `h^ℂ - γ log |·|` are continuous in the center, when the
circle averages of `h^ℂ` are continuous on `(0, ∞) × ℂ`. -/
theorem continuous_fieldCircleAverage_center (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {r : ℝ} (hr : 0 < r) :
    Continuous (fun z => fieldCircleAverage γ hcirc r z) := by
  have h1 : Continuous fun z => hcirc r z :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ z⟩
  have h2 : Continuous fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r := by
    have hm : Continuous fun z : ℂ => Real.log (max r ‖z‖) :=
      (continuous_const.max continuous_norm).log fun z => (lt_of_lt_of_le hr (le_max_left _ _)).ne'
    refine hm.congr fun z => ?_
    exact (LatticeProb.LocalMeasureKernel.LocalDecoderCommon.circleAverage_log_norm_eq_max hr z).symm
  unfold fieldCircleAverage
  exact h1.sub (continuous_const.mul h2)

/-- The circle averages of a continuous function at the dyadic scales are continuous in the center. -/
theorem continuous_dyadic_circleAverage_center {F : ℂ → ℝ} (hF : Continuous F) (k : ℕ) :
    Continuous (fun z => Real.circleAverage F z (LatticeProb.LQG.dyadicScale k)) :=
  (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hF).comp
    (continuous_const.prodMk continuous_id)

theorem dyadicScale_pos' (k : ℕ) : 0 < LatticeProb.LQG.dyadicScale k := by
  unfold LatticeProb.LQG.dyadicScale
  positivity

/-- **The LQG measure of the cone field.**  If `m` is the dyadic vague limit of the approximations of
`h^ℂ - γ log |·|`, then `e^{γ F} m`, `F = coneRefField hcirc w`, is the dyadic vague limit of the approximations
with the cone circle averages `coneRefCircle γ hcirc w`. -/
theorem isLQGLimit_coneRef (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    {m : Measure ℂ} (hm : IsLQGLimit γ (fieldCircleAverage γ hcirc) m) :
    IsLQGLimit γ (coneRefCircle γ hcirc w) (coneRefMeasure γ hcirc w m) := by
  have hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hF : Continuous (coneRefField hcirc w) := continuous_coneRefField hc w
  have hm' : LatticeProb.LQG.IsLQGLimit γ (fieldCircleAverage γ hcirc) m :=
    (LPBridge.isLQGLimit_iff _ _ _).1 hm
  have hcont' : ∀ k : ℕ, Continuous (fieldCircleAverage γ hcirc (LatticeProb.LQG.dyadicScale k)) :=
    fun k => continuous_fieldCircleAverage_center γ hcont (dyadicScale_pos' k)
  have hlim : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
      (fun (k : ℕ) (z : ℂ) => Real.circleAverage (coneRefField hcirc w) z (LatticeProb.LQG.dyadicScale k))
      (coneRefField hcirc w) atTop K := fun K hK =>
    LatticeProb.LQG.MassFunctionalDerived.tendstoUniformlyOn_dyadic_circleAverage hF hK
  have key : LatticeProb.LQG.IsLQGLimit γ
      (fun ε z => fieldCircleAverage γ hcirc ε z + Real.circleAverage (coneRefField hcirc w) z ε)
      (m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * coneRefField hcirc w z))) :=
    LatticeProb.LQG.IsLQGLimit.add_continuous (Fε := fun ε z => Real.circleAverage (coneRefField hcirc w) z ε)
      hm' hcont' hF (fun k => continuous_dyadic_circleAverage_center hF k) hlim
  exact (LPBridge.isLQGLimit_iff _ _ _).2 key

/-- **The random LQG measure of the cone is the LQG measure of the cone circle averages.**  If `μ₀` is the γ-LQG
measure of the whole-plane field `h^ℂ - γ log |·|` (`IsLQGMeasureOfField P₁ γ γ`), then almost surely on
`(Ω₁ × C(ℝ≥0, ℝ), P₁ ⊗ ν)` the measure `e^{γ F} μ₀` is the γ-LQG measure of the cone circle averages. -/
theorem isLQGMeasure_coneRef {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {c₁ : Ω₁ → ℝ → ℂ → ℝ} (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {ν : Measure (ContinuousPath ℝ)} [IsProbabilityMeasure ν] {μ₀ : Ω₁ → Measure ℂ}
    (hμ₀ : IsLQGMeasureOfField P₁ γ γ c₁ μ₀) :
    IsLQGMeasure (P₁.prod ν) γ (fun p : Ω₁ × ContinuousPath ℝ => coneRefCircle γ (c₁ p.1) p.2)
      (fun p => coneRefMeasure γ (c₁ p.1) p.2 (μ₀ p.1)) := by
  have h : ∀ᵐ ω ∂P₁, IsLQGLimit γ (fieldCircleAverage γ (c₁ ω)) (μ₀ ω) := hμ₀
  have h' : ∀ᵐ p ∂(P₁.prod ν), IsLQGLimit γ (fieldCircleAverage γ (c₁ p.1)) (μ₀ p.1) :=
    Measure.quasiMeasurePreserving_fst.ae h
  exact h'.mono fun p hp => isLQGLimit_coneRef γ (hcont p.1) p.2 hp

end MatedCRT.FirstPass.Derived
