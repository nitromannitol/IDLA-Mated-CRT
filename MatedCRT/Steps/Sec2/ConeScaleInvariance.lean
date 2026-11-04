import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# Lemma 2.6 from named steps (scale invariance of the harmonic balls of the cone)

"By applying the proof of Lemma 2.5 to the infinite family of harmonic balls given by Theorem 2.3" (line 596). Fix
`b > 0`, `R = R_b`, `h^b = h(R ·) + Q log R - γ⁻¹ log b`, with LQG measure `μ^b = b⁻¹ μ_h(R ·)`
(`ConeLQGScalingStep`). If `{Λ_t}_{t > 0}` is the family of Theorem 2.3 for `μ_h`, then `{R⁻¹ Λ_{bt}}_{t > 0}` is the
family of Theorem 2.3 for `μ^b` (scaling of harmonic balls, deterministic: `ConeHarmonicBallFamilyOnScalingStep` on
every interval, `IsConeHarmonicBallFamily.rescaledFamily`). The family of Theorem 2.3 is unique (condition (c)), and it
is a measurable functional `Φ` of the field (`ConeHarmonicBallFunctionalStep`); since `h^b =d h`
(`QuantumConeScalingInput`), `(h, Φ(h)) =d (h^b, Φ(h^b))`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Step (the family of Theorem 2.3 is a measurable functional of the field).** For `γ ∈ (0, 2)` there is a map `Φ`
from circle average processes to family processes, measurable for the law of the circle average process of the quantum
cone, such that for every continuous circle average process `c` with LQG measure `ν` (circle average limit), the family
process of every family of Theorem 2.3 for `ν` is `Φ(c)` (such a family is unique: `IsConeHarmonicBallFamily.eqOn`).
Implicit in the paper: Lemma 2.6 speaks of the law of `{Λ_t}_{t > 0}` and its proof (line 596, via line 584) uses that
the family is the same measurable function of the field for `h` and `h^b`. Expected from HB22 (harmonic balls are
measurable functions of the field, Proposition 1.3). -/
def ConeHarmonicBallFunctionalStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ Φ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop,
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω))) ∧
    ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν → ∀ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily ν Λ → globalFamilyProcess Λ = Φ (circleProcess c)

/-- A family with the properties of Theorem 2.3 on every interval `(0, T)` has them for all `t > 0`. -/
theorem isConeHarmonicBallFamily_of_forall_isConeHarmonicBallFamilyOn {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (h : ∀ T : ℝ, 0 < T → IsConeHarmonicBallFamilyOn ν Λ T) : IsConeHarmonicBallFamily ν Λ := by
  have hm : ∀ t : ℝ, 0 < t → t ∈ Ioo 0 (t + 1) := fun t ht => ⟨ht, lt_add_one t⟩
  have hT : ∀ t : ℝ, 0 < t → 0 < t + 1 := fun t ht => by linarith
  refine ⟨fun t ht => (h (t + 1) (hT t ht)).1 t (hm t ht), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun t r ht hr hsub ρ hρ => (h (t + 1) (hT t ht)).2.2 t r (hm t ht) hr hsub ρ hρ⟩
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.measure_eq t (hm t ht)
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.measure_frontier t (hm t ht)
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.isRegularOpen t (hm t ht)
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.isBounded t (hm t ht)
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.isConnected t (hm t ht)
  · exact fun t ht => (h (t + 1) (hT t ht)).2.1.mem t (hm t ht)
  · intro s hs t ht hst
    have hs' : 0 < s := hs
    have ht' : 0 < t := ht
    exact (h (t + 1) (hT t ht')).2.1.monotoneOn ⟨hs', by linarith⟩ (hm t ht') hst
  · intro t ht ε hε
    have ht' : 0 < t := ht
    have h1 := (h (t + 1) (hT t ht')).2.1.hausdorffContinuousOn t (hm t ht') ε hε
    rw [isOpen_Ioo.nhdsWithin_eq (hm t ht')] at h1
    exact nhdsWithin_le_nhds h1
  · apply Subset.antisymm
    · intro x hx
      rw [← (h 1 one_pos).2.1.iInter_eq]
      simp only [mem_iInter] at hx ⊢
      exact fun t ht => hx t ht.1
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      simp only [mem_iInter]
      intro t ht
      have ht' : 0 < t := ht
      exact (h (t + 1) (hT t ht')).2.1.mem t (hm t ht')

/-- **Scaling of the family of Theorem 2.3** (from the deterministic scaling step on every interval): if `{Λ_t}_{t > 0}`
is a family of Theorem 2.3 for `μ`, then `{R⁻¹ Λ_{bt}}_{t > 0}` is one for `b⁻¹ μ(R ·)`. -/
theorem IsConeHarmonicBallFamily.rescaledFamily (hscaling : ConeHarmonicBallFamilyOnScalingStep)
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (h : IsConeHarmonicBallFamily μ Λ) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) :
    IsConeHarmonicBallFamily (rescaledMeasure μ R b) (rescaledFamily Λ R b) :=
  isConeHarmonicBallFamily_of_forall_isConeHarmonicBallFamilyOn fun T hT =>
    hscaling μ Λ R b T hR hb (h.isConeHarmonicBallFamilyOn (mul_pos hb hT))

/-- **Lemma 2.6, core** (for an abstract positive random radius `R`). -/
theorem coneScaleInvariance_core {γ b : ℝ} (hb : 0 < b) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (R : Ω → ℝ) {Λ : Ω → ℝ → Set ℂ}
    {Φ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω))
    (hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P)
    (hmeasb : AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) P)
    (hlaw : P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) =
      P.map (fun ω => circleProcess (hcirc ω)))
    (hscal : ∀ᵐ ω ∂P, 0 < R ω ∧
      IsLQGLimit γ (rescaledCircle γ (hcirc ω) (R ω) b) (rescaledMeasure (μ ω) (R ω) b))
    (hΦmeas : AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω)))
    (hchar : ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν → ∀ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily ν Λ → globalFamilyProcess Λ = Φ (circleProcess c))
    (hscaling : ConeHarmonicBallFamilyOnScalingStep)
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) :
    P.map (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =
      P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b),
        globalFamilyProcess (rescaledFamily (Λ ω) (R ω) b))) := by
  refine map_prod_eq_of_ae_eq hmeasc hmeasb hlaw hΦmeas ?_ ?_
  · filter_upwards [hΛ, hcont, hlim] with ω hω hc hl
    exact hchar _ hc _ hl _ hω
  · filter_upwards [hΛ, hcont, hscal] with ω hω hc hs
    exact hchar _ (continuousOn_rescaledCircle hc hs.1) _ hs.2 _ (hω.rescaledFamily hscaling hs.1 hb)

/-- **Lemma 2.6** from the steps. -/
theorem coneScaleInvariance_of_steps (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hmeasb : ConeRescaledCircleAEMeasurableStep) (hfun : ConeHarmonicBallFunctionalStep)
    (hscaling : ConeHarmonicBallFamilyOnScalingStep) : ConeScaleInvarianceStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨Φ, hΦ, hchar⟩ := hfun γ hγ0 hγ2
  exact coneScaleInvariance_core hb (fun ω => coneScaleRadius γ (hcirc ω) b)
    hcone.2.1.ae_continuousOn_circle hcone.2.2 hcone.2.1.measurable_circleProcess.aemeasurable
    (hmeasb γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb) (hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb)
    (hlqg γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb) (hΦ Ω P hC hcirc μ hcone) hchar hscaling hΛ

end MatedCRT
