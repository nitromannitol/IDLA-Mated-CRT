import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.External.QuantumCone

/-!
# Lemma 2.5 from named steps (scale invariance of the harmonic balls of the cone up to a fixed time)

The proof of Lemma 2.5 (lines 565-585). Fix `b > 0`, let `R = R_b` and `h^b = h(R ·) + Q log R - γ⁻¹ log b`.
* `h^b =d h` through the circle average processes (DMS14 Proposition 4.13(i), `QuantumConeScalingInput`), and the LQG
  measure of `h^b` is `μ^b = b⁻¹ μ_h(R ·)` (`rescaledMeasure`; Fact 2.2 III, IV: `ConeLQGScalingStep`).
* The family of Lemma 2.4 is a measurable functional of the field (`ConeHalfBallFamilyFunctionalStep`: the event that it
  exists is a measurable set `G` of circle average processes, and on it the family process is `Φ(h)`; lines 553, 562
  speak of its law). Since `h^b =d h`, a.s. a family `{Λ̃_t}_{0 < t < T^b}` of Lemma 2.4 exists for `μ^b`, and the
  joint laws of `(h, Φ(h))` and `(h^b, Φ(h^b))` agree (`map_prod_eq_of_ae_eq`).
* `Λ^b_{bt} = R Λ̃_t` is a family for `μ_h` on `(0, b T^b)` (scaling of harmonic balls, deterministic:
  `ConeHarmonicBallFamilyOnScalingStep`), and `R⁻¹ Λ^b_{b ·} = Λ̃`.
* Uniqueness: condition (c) (`IsConeHarmonicBallFamilyOn.eqOn`) and strict growth (`ConeHarmonicBallStrictGrowthStep`,
  `IsStoppedAtHalfBall.eq_of_eqOn`); this replaces the citation of HB22 Proposition 5.6 at line 584.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The measure `A ↦ b⁻¹ μ(R A)`, the push-forward of `b⁻¹ μ` by `x ↦ R⁻¹ x`: for `μ = μ_h` and `R = R_b` it is the LQG
measure of `h(R ·) + Q log R - γ⁻¹ log b` (LQG coordinate change and Weyl scaling, Fact 2.2 III, IV; line 578). -/
noncomputable def rescaledMeasure (μ : Measure ℂ) (R b : ℝ) : Measure ℂ :=
  ENNReal.ofReal b⁻¹ • μ.map fun x => (R : ℂ)⁻¹ * x

/-- A family of Lemma 2.4 for a measure `ν` (`T > 0`, the properties of Theorem 2.3 on `(0, T)`, stopped at `∂B_{1/2}`)
which grows strictly. -/
def IsStrictHalfBallFamily (ν : Measure ℂ) (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  0 < T ∧ IsConeHarmonicBallFamilyOn ν Λ T ∧ IsStoppedAtHalfBall Λ T ∧ IsStrictlyGrowingOn Λ T

/-- **Step (the LQG measure of the rescaled cone field: Fact 2.2 III, IV).** For `b > 0`, a.s. the cone scale radius
`R_b` is positive (line 451) and `b⁻¹ μ_h(R_b ·)` is the LQG measure (circle average limit) of
`h(R_b ·) + Q log R_b - γ⁻¹ log b`: LQG coordinate change (Fact 2.2 IV, `LQGMeasurePropertiesStmt`, at the random
`a = R_b`, line 578) and Weyl scaling by the constant `-γ⁻¹ log b` (Fact 2.2 III). -/
def ConeLQGScalingStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b ∧
      IsLQGLimit γ (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)

/-- **Step (the rescaled cone field is a random variable).** For `b > 0`, the circle average process of
`h(R_b ·) + Q log R_b - γ⁻¹ log b` is a random variable (`R_b` is a random variable and the circle average process is a.s.
continuous). Implicit in eq:quantum-cone-scaling (line 455), which speaks of its law. -/
def ConeRescaledCircleAEMeasurableStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
    AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) P

/-- **Step (the family of Lemma 2.4 is a measurable functional of the field).** For `γ ∈ (0, 2)` there are a set `G` of
circle average processes and a map `Φ` from circle average processes to family processes, measurable for the law of
the circle average process of the quantum cone, such that for every continuous circle average process `c` with LQG
measure `ν` (circle average limit): `c ∈ G` iff a strictly growing family of Lemma 2.4 for `ν` exists, and then its
family process is `Φ(c)`. Implicit in the paper: Lemma 2.5 speaks of the law of `{Λ_t}_{0<t<T}` (lines 553, 562), and
"as `h^b` has the same law as `h`, this shows the equality of joint laws" (line 584) uses that the family is the same
measurable function of the field for `h` and `h^b`. Expected from HB22 (harmonic balls are measurable functions of the
field, Proposition 1.3). -/
def ConeHalfBallFamilyFunctionalStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ (G : Set (Ioi (0 : ℝ) × ℂ → ℝ)) (Φ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop),
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      NullMeasurableSet G (P.map fun ω => circleProcess (hcirc ω)) ∧
        AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω))) ∧
    ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν →
      (circleProcess c ∈ G ↔ ∃ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily ν Λ T) ∧
      ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily ν Λ T → familyProcess Λ T = Φ (circleProcess c)

/-- **Deterministic step (scaling of harmonic balls).** If `{Λ_t}_{0 < t < bT}` is a family of harmonic balls for `μ`
with the properties of Theorem 2.3, then `{R⁻¹ Λ_{bt}}_{0 < t < T}` is one for `b⁻¹ μ(R ·)` (`R, b > 0`): the
mean value property, (a) and (b) are transported by `x ↦ R⁻¹ x`, and the obstacle problem (c) scales by
`w̄^{B_ρ}_t[b⁻¹ μ(R ·)](x) = b⁻¹ w̄^{B_{Rρ}}_{bt}[μ](R x)` (the Green function of a disk is scale invariant). Line 582
("for similar reasons"). -/
def ConeHarmonicBallFamilyOnScalingStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (R b T : ℝ), 0 < R → 0 < b → IsConeHarmonicBallFamilyOn μ Λ (b * T) →
    IsConeHarmonicBallFamilyOn (rescaledMeasure μ R b) (rescaledFamily Λ R b) T

/-- Rescaling by `(R⁻¹, b⁻¹)` and then by `(R, b)` is the identity. -/
theorem rescaledFamily_rescaledFamily_inv (Λ : ℝ → Set ℂ) {R b : ℝ} (hR : R ≠ 0) (hb : b ≠ 0) :
    rescaledFamily (rescaledFamily Λ R⁻¹ b⁻¹) R b = Λ := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  funext t
  ext x
  show ((R⁻¹ : ℝ) : ℂ) * ((R : ℂ) * x) ∈ Λ (b⁻¹ * (b * t)) ↔ x ∈ Λ t
  rw [inv_mul_cancel_left₀ hb, Complex.ofReal_inv, inv_mul_cancel_left₀ hRc]

/-- Rescaling a measure by `(R, b)` and then by `(R⁻¹, b⁻¹)` is the identity. -/
theorem rescaledMeasure_rescaledMeasure_inv (μ : Measure ℂ) {R b : ℝ} (hR : R ≠ 0) (hb : 0 < b) :
    rescaledMeasure (rescaledMeasure μ R b) R⁻¹ b⁻¹ = μ := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  have hf : Measurable fun x : ℂ => (R : ℂ)⁻¹ * x := measurable_id.const_mul _
  have hg : Measurable fun x : ℂ => ((R⁻¹ : ℝ) : ℂ)⁻¹ * x := measurable_id.const_mul _
  have hcomp : ((fun x : ℂ => ((R⁻¹ : ℝ) : ℂ)⁻¹ * x) ∘ fun x => (R : ℂ)⁻¹ * x) = id := by
    funext x
    simp [Complex.ofReal_inv, hRc]
  unfold rescaledMeasure
  rw [Measure.map_smul, Measure.map_map hg hf, hcomp, Measure.map_id, smul_smul, inv_inv,
    ← ENNReal.ofReal_mul hb.le, mul_inv_cancel₀ hb.ne', ENNReal.ofReal_one, one_smul]
  exact hg.aemeasurable

/-- Strict growth is preserved by rescaling. -/
theorem IsStrictlyGrowingOn.rescaledFamily {Λ : ℝ → Set ℂ} {R b T : ℝ} (h : IsStrictlyGrowingOn Λ (b * T))
    (hb : 0 < b) : IsStrictlyGrowingOn (rescaledFamily Λ R b) T := by
  intro s t hs hst htT
  have hcont : Continuous fun x : ℂ => (R : ℂ) * x := continuous_const.mul continuous_id
  exact (hcont.closure_preimage_subset _).trans (preimage_mono (h (b * s) (b * t) (mul_pos hb hs)
    (mul_lt_mul_of_pos_left hst hb) (mul_lt_mul_of_pos_left htT hb)))

/-- The circle average process of `h(R ·) + Q log R - γ⁻¹ log b` is continuous if that of `h` is (`R > 0`). -/
theorem continuousOn_rescaledCircle {γ : ℝ} {c : ℝ → ℂ → ℝ} {R b : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) (hR : 0 < R) :
    ContinuousOn (fun p : ℝ × ℂ => rescaledCircle γ c R b p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hmaps : MapsTo (fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun p hp => ⟨mul_pos hR hp.1, mem_univ _⟩
  have h1 := hc.comp (Continuous.continuousOn (by fun_prop)) hmaps
  show ContinuousOn (fun p : ℝ × ℂ => c (R * p.1) ((R : ℂ) * p.2) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b) _
  exact (h1.add continuousOn_const).sub continuousOn_const

/-- The circle average process of a cone field is a random variable. -/
theorem IsQuantumCone.measurable_circleProcess {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => circleProcess (hcirc ω) :=
  measurable_pi_iff.2 fun p : Ioi (0 : ℝ) × ℂ => h.measurable_circle p.1.1 p.2 p.1.2

/-- **Equality of joint laws through a measurable functional.** If `g =d f` and a.s. `F = Φ(f)`, `G = Φ(g)` for one
map `Φ`, measurable for the law of `f`, then `(f, F) =d (g, G)`. -/
theorem map_prod_eq_of_ae_eq {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure Ω} {f g : Ω → X} {F G : Ω → Y} {Φ : X → Y} (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hlaw : P.map g = P.map f) (hΦ : AEMeasurable Φ (P.map f)) (hF : ∀ᵐ ω ∂P, F ω = Φ (f ω))
    (hG : ∀ᵐ ω ∂P, G ω = Φ (g ω)) :
    P.map (fun ω => (f ω, F ω)) = P.map (fun ω => (g ω, G ω)) := by
  have hF' : (fun ω => (f ω, F ω)) =ᵐ[P] fun ω => (f ω, Φ (f ω)) := by
    filter_upwards [hF] with ω h
    rw [h]
  have hG' : (fun ω => (g ω, G ω)) =ᵐ[P] fun ω => (g ω, Φ (g ω)) := by
    filter_upwards [hG] with ω h
    rw [h]
  rw [Measure.map_congr hF', Measure.map_congr hG']
  have hk : AEMeasurable (fun x => (x, Φ x)) (P.map f) := aemeasurable_id.prodMk hΦ
  have hk' : AEMeasurable (fun x => (x, Φ x)) (P.map g) := by
    rw [hlaw]
    exact hk
  have e1 := AEMeasurable.map_map_of_aemeasurable hk hf
  have e2 := AEMeasurable.map_map_of_aemeasurable hk' hg
  rw [hlaw] at e2
  exact e1.symm.trans e2

/-- The almost sure events of a law: if `g =d f` (both random variables) and `f ∈ G` a.s. for a set `G` which is
null-measurable for the law of `f`, then `g ∈ G` a.s. -/
theorem ae_mem_of_map_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω} {f g : Ω → X}
    {G : Set X} (hf : AEMeasurable f P) (hg : AEMeasurable g P) (hlaw : P.map g = P.map f)
    (hG : NullMeasurableSet G (P.map f)) (hfG : ∀ᵐ ω ∂P, f ω ∈ G) : ∀ᵐ ω ∂P, g ω ∈ G := by
  rw [ae_iff] at hfG ⊢
  have e1 : P.map g Gᶜ = P {ω | ¬ g ω ∈ G} := Measure.map_apply₀ hg (by rw [hlaw]; exact hG.compl)
  have e2 : P.map f Gᶜ = P {ω | ¬ f ω ∈ G} := Measure.map_apply₀ hf hG.compl
  rw [← e1, hlaw, e2]
  exact hfG

/-- **Lemma 2.5, core** (for an abstract positive random radius `R`): the conclusion of Lemma 2.5 with `R_b` replaced by
`R`, from the law and LQG measure of `h(R ·) + Q log R - γ⁻¹ log b`, the functional `Φ` and the deterministic steps. -/
theorem coneScaleInvarianceUpToFixedTime_core {γ b : ℝ} (hb : 0 < b) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (R : Ω → ℝ) {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    {G : Set (Ioi (0 : ℝ) × ℂ → ℝ)} {Φ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω))
    (hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P)
    (hmeasb : AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) P)
    (hlaw : P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) =
      P.map (fun ω => circleProcess (hcirc ω)))
    (hscal : ∀ᵐ ω ∂P, 0 < R ω ∧
      IsLQGLimit γ (rescaledCircle γ (hcirc ω) (R ω) b) (rescaledMeasure (μ ω) (R ω) b))
    (hgrow : ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T → IsStrictlyGrowingOn Λ T)
    (hGnull : NullMeasurableSet G (P.map fun ω => circleProcess (hcirc ω)))
    (hΦmeas : AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω)))
    (hchar : ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν →
      (circleProcess c ∈ G ↔ ∃ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily ν Λ T) ∧
      ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsStrictHalfBallFamily ν Λ T → familyProcess Λ T = Φ (circleProcess c))
    (hscaling : ConeHarmonicBallFamilyOnScalingStep)
    (hTΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧ IsStoppedAtHalfBall (Λ ω) (T ω)) :
    ∃ (Tb : Ω → ℝ) (Λb : Ω → ℝ → Set ℂ),
      (∀ᵐ ω ∂P, 0 < Tb ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λb ω) (b * Tb ω) ∧
        IsStoppedAtHalfBall (rescaledFamily (Λb ω) (R ω) b) (Tb ω) ∧
        ∀ (T' : ℝ) (Λ' : ℝ → Set ℂ), 0 < T' → IsConeHarmonicBallFamilyOn (μ ω) Λ' (b * T') →
          IsStoppedAtHalfBall (rescaledFamily Λ' (R ω) b) T' →
          T' = Tb ω ∧ EqOn Λ' (Λb ω) (Ioo 0 (b * Tb ω))) ∧
      P.map (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω))) =
        P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b),
          familyProcess (rescaledFamily (Λb ω) (R ω) b) (Tb ω))) := by
  -- continuity of the rescaled circle average process
  have hcontb : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => rescaledCircle γ (hcirc ω) (R ω) b p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
    filter_upwards [hcont, hscal] with ω hω hR
    exact continuousOn_rescaledCircle hω hR.1
  -- the given family is a strictly growing family of Lemma 2.4
  have hstrict : ∀ᵐ ω ∂P, IsStrictHalfBallFamily (μ ω) (Λ ω) (T ω) := by
    filter_upwards [hTΛ, hgrow] with ω hω hg
    exact ⟨hω.1, hω.2.1, hω.2.2, hg _ _ hω.2.1⟩
  -- `h ∈ G` a.s., hence `h^b ∈ G` a.s.
  have hG : ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ G := by
    filter_upwards [hstrict, hcont, hlim] with ω hω hc hl
    exact (hchar _ hc _ hl).1.2 ⟨_, _, hω⟩
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (R ω) b) ∈ G :=
    ae_mem_of_map_eq hmeasc hmeasb hlaw hGnull hG
  -- a family of Lemma 2.4 for `μ^b`, chosen measurably in nothing (pointwise choice)
  have hex : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ), IsStrictHalfBallFamily (rescaledMeasure (μ ω) (R ω) b) y.2 y.1 := by
    filter_upwards [hGb, hcontb, hscal] with ω hω hc hs
    obtain ⟨T', Λ', h'⟩ := (hchar _ hc _ hs.2).1.1 hω
    exact ⟨(T', Λ'), h'⟩
  let x : Ω → ℝ × (ℝ → Set ℂ) := fun ω => Classical.epsilon fun y : ℝ × (ℝ → Set ℂ) =>
    IsStrictHalfBallFamily (rescaledMeasure (μ ω) (R ω) b) y.2 y.1
  have hx : ∀ᵐ ω ∂P, IsStrictHalfBallFamily (rescaledMeasure (μ ω) (R ω) b) (x ω).2 (x ω).1 := by
    filter_upwards [hex] with ω hω
    exact Classical.epsilon_spec hω
  refine ⟨fun ω => (x ω).1, fun ω => rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹, ?_, ?_⟩
  · filter_upwards [hx, hscal, hgrow] with ω hω hs hg
    have hR := hs.1
    have hresc : rescaledFamily (rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹) (R ω) b = (x ω).2 :=
      rescaledFamily_rescaledFamily_inv _ hR.ne' hb.ne'
    have hfam : IsConeHarmonicBallFamilyOn (μ ω) (rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹) (b * (x ω).1) := by
      have h1 : IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (R ω) b) (x ω).2 (b⁻¹ * (b * (x ω).1)) := by
        rw [inv_mul_cancel_left₀ hb.ne']
        exact hω.2.1
      have := hscaling _ _ (R ω)⁻¹ b⁻¹ (b * (x ω).1) (inv_pos.2 hR) (inv_pos.2 hb) h1
      rwa [rescaledMeasure_rescaledMeasure_inv _ hR.ne' hb] at this
    refine ⟨hω.1, hfam, by rw [hresc]; exact hω.2.2.1, fun T' Λ' hT' hΛ' hst' => ?_⟩
    have heq : EqOn Λ' (rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹) (Ioo 0 (min (b * (x ω).1) (b * T'))) :=
      hfam.eqOn hΛ'
    have hΛ'resc := hscaling (μ ω) Λ' (R ω) b T' hR hb hΛ'
    have hgrow' : IsStrictlyGrowingOn (rescaledFamily Λ' (R ω) b) T' := (hg _ _ hΛ').rescaledFamily hb
    have heq' : EqOn (rescaledFamily Λ' (R ω) b) (x ω).2 (Ioo 0 (min (x ω).1 T')) := by
      intro t ht
      rw [← hresc]
      have hbt : b * t ∈ Ioo 0 (min (b * (x ω).1) (b * T')) := by
        refine ⟨mul_pos hb ht.1, ?_⟩
        rw [← mul_min_of_nonneg _ _ hb.le]
        exact mul_lt_mul_of_pos_left ht.2 hb
      show {y | (R ω : ℂ) * y ∈ Λ' (b * t)} =
        {y | (R ω : ℂ) * y ∈ rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹ (b * t)}
      rw [heq hbt]
    have hTT : (x ω).1 = T' := hω.2.2.1.eq_of_eqOn hst' heq' hω.2.1.2.1.monotoneOn hΛ'resc.2.1.monotoneOn
      hω.2.2.2 hgrow'
    refine ⟨hTT.symm, ?_⟩
    rw [← hTT, min_self] at heq
    exact heq
  · refine map_prod_eq_of_ae_eq hmeasc hmeasb hlaw hΦmeas ?_ ?_
    · filter_upwards [hstrict, hcont, hlim] with ω hω hc hl
      exact (hchar _ hc _ hl).2 _ _ hω
    · filter_upwards [hx, hcontb, hscal] with ω hω hc hs
      show familyProcess (rescaledFamily (rescaledFamily (x ω).2 (R ω)⁻¹ b⁻¹) (R ω) b) (x ω).1 = _
      rw [rescaledFamily_rescaledFamily_inv _ hs.1.ne' hb.ne']
      exact (hchar _ hc _ hs.2).2 _ _ hω

/-- **Lemma 2.5** from the steps. -/
theorem coneScaleInvarianceUpToFixedTime_of_steps (hscale : QuantumConeScalingInput)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hlqg : ConeLQGScalingStep)
    (hmeasb : ConeRescaledCircleAEMeasurableStep) (hfun : ConeHalfBallFamilyFunctionalStep)
    (hscaling : ConeHarmonicBallFamilyOnScalingStep) : ConeScaleInvarianceUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone T Λ hTΛ b hb
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨G, Φ, hGΦ, hchar⟩ := hfun γ hγ0 hγ2
  obtain ⟨hGnull, hΦmeas⟩ := hGΦ Ω P hC hcirc μ hcone
  exact coneScaleInvarianceUpToFixedTime_core hb (fun ω => coneScaleRadius γ (hcirc ω) b)
    hcone.2.1.ae_continuousOn_circle hcone.2.2 hcone.2.1.measurable_circleProcess.aemeasurable
    (hmeasb γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb) (hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb)
    (hlqg γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb) (hgrow γ hγ0 hγ2 Ω P hC hcirc μ hcone) hGnull hΦmeas hchar
    hscaling hTΛ

end MatedCRT
