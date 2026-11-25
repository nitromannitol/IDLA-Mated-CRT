import MatedCRT.FirstPass.Derived.ZeroConeCurveFactorProof
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1PosProof
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ContVersion
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# Lemma A.1 for the zero-cone field jointly with the space-filling SLE

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1, `notes/refs/1705.11161.txt` lines 1186-1187)
use that a functional `V(h, η̂)` invariant under the simultaneous coordinate change of the zero-cone field and the
curve is almost surely constant. The written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(c) Joint invariance"
(lines 33-45), proves this from

* the mixing of the curve at distant centres (lines 35-39), which comes from the mixing of the imaginary-geometry
  field under the normalized similarities (lines 15-27) through the affine covariance of the curve map;
* Lemma A.4 of arXiv:1705.11161 (lines 42; `notes/refs/1705.11161.txt` lines 2026-2041): random similarities
  `T_m(w) = z_m + C_m w` with `h ∘ T_m + Q log C_m` equal in law to `h` and `|z_m| → ∞` in probability;
* an approximation of `V` by tensors, which shows that `V(h, e)` is almost surely `v(h) = ∫ V(h, e) ν(de)`
  (line 44), and Lemma A.1 for the field alone, applied to `v`.

This file proves the measure-theoretic core of that argument for a general random simultaneous action
(`ae_eq_integral_of_jointInvariance`), and from it `ZeroConeJointLemmaA1` (`zeroConeJointLemmaA1`) under Lemma A.1
for the field alone (`ZeroConeCircleAverageLemmaA1`), the scale and translation invariance of the law of the curve
(`SpaceFillingSLESimilarityLaw`), and two named inputs stated here: the mixing of the imaginary-geometry field modulo
`2πχ` under similarities with distant centres (`IGFieldDistantCentreMixing`) and Lemma A.4 of arXiv:1705.11161
(`ZeroConeLemmaA4`). The curve map of the coupling carries the mixing of the field to the curve
(`tendsto_igCurve_affineReroot_correlation`).
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

/-! ### A random simultaneous action and the factor through the first coordinate -/

section Abstract

variable {α β E 𝒯 : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
  [MeasurableSpace 𝒯]

/-- A bounded measurable real function is integrable for a finite measure. -/
theorem integrable_of_measurable_abs_le {γ' : Type*} [MeasurableSpace γ'] {μ' : Measure γ'}
    [IsFiniteMeasure μ'] {f : γ' → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ' :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC x))

/-- The indicator of a set with value `1` has absolute value at most `1`. -/
theorem abs_indicator_one_apply_le {γ' : Type*} (S : Set γ') (y : γ') :
    |S.indicator (1 : γ' → ℝ) y| ≤ 1 := by
  by_cases h : y ∈ S <;> simp [h]

/-- A bound for the absolute value of a triple product. -/
theorem abs_mul_mul_le_of_abs_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C := by
  rw [abs_mul, abs_mul]
  have hA : 0 ≤ A := (abs_nonneg a).trans ha
  have hB : 0 ≤ B := (abs_nonneg b).trans hb
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hA) hc (abs_nonneg _) (mul_nonneg hA hB)

/-- For a probability measure, `|∫ f| ≤ C` when `|f| ≤ C` everywhere. -/
theorem abs_integral_le_of_forall_abs_le_of_isProbabilityMeasure {γ' : Type*} [MeasurableSpace γ']
    {μ' : Measure γ'} [IsProbabilityMeasure μ'] {f : γ' → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂μ'| ≤ C :=
  calc |∫ x, f x ∂μ'| ≤ ∫ x, |f x| ∂μ' := abs_integral_le_integral_abs
    _ ≤ ∫ _, C ∂μ' := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
        (integrable_const C) (ae_of_all _ hC)
    _ = C := by simp

/-- The simultaneous action `((a, x), e) ↦ (σ_t a, ρ_t e)` at the random parameter `t = τ (a, x)`. -/
def randomJointAction (σ : 𝒯 → α → α) (ρ : 𝒯 → β → β) (τ : α × E → 𝒯) (x : (α × E) × β) : α × β :=
  (σ (τ x.1) x.1.1, ρ (τ x.1) x.2)

theorem measurable_randomJointAction {σ : 𝒯 → α → α} {ρ : 𝒯 → β → β} {τ : α × E → 𝒯}
    (hσ : Measurable fun q : 𝒯 × α => σ q.1 q.2) (hρ : Measurable fun q : 𝒯 × β => ρ q.1 q.2)
    (hτ : Measurable τ) : Measurable (randomJointAction σ ρ τ) := by
  have h1 : Measurable fun x : (α × E) × β => σ (τ x.1) x.1.1 :=
    hσ.comp ((hτ.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst))
  have h2 : Measurable fun x : (α × E) × β => ρ (τ x.1) x.2 :=
    hρ.comp ((hτ.comp measurable_fst).prodMk measurable_snd)
  exact h1.prodMk h2

/-- **The random simultaneous action preserves the product law** when the first coordinate of the random action has
law `μ` and each `ρ_t` at the realized parameters preserves `ν`: conditionally on `(a, x)`, `ρ_{τ(a,x)} e` has law
`ν`. -/
theorem map_randomJointAction {μ : Measure α} {ν : Measure β} {κ : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] {σ : 𝒯 → α → α} {ρ : 𝒯 → β → β}
    {τ : α × E → 𝒯} (hσ : Measurable fun q : 𝒯 × α => σ q.1 q.2)
    (hρ : Measurable fun q : 𝒯 × β => ρ q.1 q.2) (hτ : Measurable τ)
    (hσlaw : (μ.prod κ).map (fun p => σ (τ p) p.1) = μ) (hρlaw : ∀ p, ν.map (ρ (τ p)) = ν) :
    ((μ.prod κ).prod ν).map (randomJointAction σ ρ τ) = μ.prod ν := by
  have hΘ := measurable_randomJointAction hσ hρ hτ
  have hσm : Measurable fun p : α × E => σ (τ p) p.1 := hσ.comp (hτ.prodMk measurable_fst)
  have hρt : ∀ t, Measurable (ρ t) := fun t => hρ.comp (measurable_const.prodMk measurable_id)
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply hΘ (hA.prod hB), Measure.prod_apply (hΘ (hA.prod hB))]
  have hsec : ∀ p : α × E, ν (Prod.mk p ⁻¹' (randomJointAction σ ρ τ ⁻¹' (A ×ˢ B))) =
      ((fun p : α × E => σ (τ p) p.1) ⁻¹' A).indicator (fun _ => ν B) p := by
    intro p
    by_cases hp : σ (τ p) p.1 ∈ A
    · rw [indicator_of_mem (show p ∈ (fun p : α × E => σ (τ p) p.1) ⁻¹' A from hp)]
      have e : Prod.mk p ⁻¹' (randomJointAction σ ρ τ ⁻¹' (A ×ˢ B)) = ρ (τ p) ⁻¹' B := by
        ext e
        simp [randomJointAction, hp]
      rw [e, ← Measure.map_apply (hρt _) hB, hρlaw p]
    · rw [indicator_of_notMem (show p ∉ (fun p : α × E => σ (τ p) p.1) ⁻¹' A from hp)]
      have e : Prod.mk p ⁻¹' (randomJointAction σ ρ τ ⁻¹' (A ×ˢ B)) = ∅ := by
        ext e
        simp [randomJointAction, hp]
      rw [e, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const (hσm hA), ← Measure.map_apply hσm hA, hσlaw, mul_comm (ν B)]

/-- **Two integrable functions with equal integrals over all measurable rectangles are almost everywhere equal**
(the rectangles form a π-system generating the product σ-algebra). -/
theorem ae_eq_of_setIntegral_rectangle_eq {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f g : α × β → ℝ} (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hfg : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ x in A ×ˢ B, f x ∂μ.prod ν = ∫ x in A ×ˢ B, g x ∂μ.prod ν) :
    f =ᵐ[μ.prod ν] g := by
  have hall : ∀ S, MeasurableSet S → ∫ x in S, f x ∂μ.prod ν = ∫ x in S, g x ∂μ.prod ν := by
    intro S hS
    refine MeasurableSpace.induction_on_inter
      (C := fun S _ => ∫ x in S, f x ∂μ.prod ν = ∫ x in S, g x ∂μ.prod ν)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ S hS
    · simp
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hfg A B hA hB
    · intro t ht hC
      have huniv := hfg univ univ MeasurableSet.univ MeasurableSet.univ
      simp only [univ_prod_univ, setIntegral_univ] at huniv
      rw [setIntegral_compl ht hf, setIntegral_compl ht hg, huniv, hC]
    · intro t hdisj htm hC
      rw [integral_iUnion htm hdisj hf.integrableOn, integral_iUnion htm hdisj hg.integrableOn]
      exact tsum_congr hC
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hf.integrableOn)
    (fun s _ _ => hg.integrableOn) fun s hs _ => hall s hs

/-- **The correlations with indicators of the transported pair tend to zero.** Let the random simultaneous action
preserve the product law and let the curve factor mix along the random parameters (`hmix`). For a bounded weight
`ψ(a) g(e)` with `∫ g dν = 0` and every measurable `S`, `∫ ψ(a) g(e) 1_S(σ_t a, ρ_t e) → 0`: true for rectangles by
`hmix`, and the class of such `S` is closed under complements and countable disjoint unions (Tannery's theorem with
the uniform bound `|·| ≤ ‖ψ‖ ‖g‖ (μ ⊗ ν)(S)` from the preservation of the law). -/
theorem tendsto_integral_indicator_randomJointAction {μ : Measure α} {ν : Measure β} {κ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {σ : 𝒯 → α → α} {ρ : 𝒯 → β → β} (hσ : Measurable fun q : 𝒯 × α => σ q.1 q.2)
    (hρ : Measurable fun q : 𝒯 × β => ρ q.1 q.2) {τ : ℕ → α × E → 𝒯} (hτ : ∀ m, Measurable (τ m))
    (hlaw : ∀ m, ((μ.prod κ).prod ν).map (randomJointAction σ ρ (τ m)) = μ.prod ν)
    {ψ : α → ℝ} {g : β → ℝ} (hψ : Measurable ψ) (hg : Measurable g) {Mψ Mg : ℝ}
    (hψb : ∀ a, |ψ a| ≤ Mψ) (hgb : ∀ e, |g e| ≤ Mg) (hg0 : ∫ e, g e ∂ν = 0)
    (hmix : ∀ B : Set β, MeasurableSet B →
      Tendsto (fun m => ∫ p, |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν| ∂(μ.prod κ)) atTop (𝓝 0))
    {S : Set (α × β)} (hS : MeasurableSet S) :
    Tendsto (fun m => ∫ x, ψ x.1.1 * g x.2 * S.indicator 1 (randomJointAction σ ρ (τ m) x)
      ∂((μ.prod κ).prod ν)) atTop (𝓝 0) := by
  have hΘ : ∀ m, Measurable (randomJointAction σ ρ (τ m)) := fun m =>
    measurable_randomJointAction hσ hρ (hτ m)
  have hw : Measurable fun x : (α × E) × β => ψ x.1.1 * g x.2 :=
    (hψ.comp (measurable_fst.comp measurable_fst)).mul (hg.comp measurable_snd)
  have hwb : ∀ x : (α × E) × β, |ψ x.1.1 * g x.2| ≤ Mψ * Mg := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hψb x.1.1) (hgb x.2) (abs_nonneg (g x.2)) ((abs_nonneg (ψ x.1.1)).trans (hψb x.1.1))
  have hwi : Integrable (fun x : (α × E) × β => ψ x.1.1 * g x.2) ((μ.prod κ).prod ν) :=
    integrable_of_measurable_abs_le hw hwb
  have hset : ∀ m (T : Set (α × β)), MeasurableSet T →
      ∫ x, ψ x.1.1 * g x.2 * T.indicator 1 (randomJointAction σ ρ (τ m) x) ∂((μ.prod κ).prod ν) =
        ∫ x in randomJointAction σ ρ (τ m) ⁻¹' T, ψ x.1.1 * g x.2 ∂((μ.prod κ).prod ν) := by
    intro m T hT
    rw [← integral_indicator (hΘ m hT)]
    congr 1
    funext x
    by_cases hx : randomJointAction σ ρ (τ m) x ∈ T
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ randomJointAction σ ρ (τ m) ⁻¹' T from hx),
        Pi.one_apply, mul_one]
    · rw [indicator_of_notMem hx,
        indicator_of_notMem (show x ∉ randomJointAction σ ρ (τ m) ⁻¹' T from hx), mul_zero]
  have hbound : ∀ m (T : Set (α × β)), MeasurableSet T →
      |∫ x in randomJointAction σ ρ (τ m) ⁻¹' T, ψ x.1.1 * g x.2 ∂((μ.prod κ).prod ν)| ≤
        Mψ * Mg * ((μ.prod ν) T).toReal := by
    intro m T hT
    calc _ ≤ ∫ x in randomJointAction σ ρ (τ m) ⁻¹' T, |ψ x.1.1 * g x.2| ∂((μ.prod κ).prod ν) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ in randomJointAction σ ρ (τ m) ⁻¹' T, Mψ * Mg ∂((μ.prod κ).prod ν) :=
          setIntegral_mono hwi.abs.integrableOn (integrable_const _).integrableOn hwb
      _ = Mψ * Mg * ((μ.prod ν) T).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_comm _ (Mψ * Mg), measureReal_def,
            ← Measure.map_apply (hΘ m) hT, hlaw m]
  have hint : Tendsto (fun m => ∫ x in randomJointAction σ ρ (τ m) ⁻¹' S, ψ x.1.1 * g x.2
      ∂((μ.prod κ).prod ν)) atTop (𝓝 0) := by
    refine MeasurableSpace.induction_on_inter
      (C := fun S _ => Tendsto (fun m => ∫ x in randomJointAction σ ρ (τ m) ⁻¹' S, ψ x.1.1 * g x.2
        ∂((μ.prod κ).prod ν)) atTop (𝓝 0))
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ S hS
    · simp
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      have hcomp : ∀ m, ∫ x in randomJointAction σ ρ (τ m) ⁻¹' (A ×ˢ B), ψ x.1.1 * g x.2
          ∂((μ.prod κ).prod ν) = ∫ p, ψ p.1 * A.indicator 1 (σ (τ m p) p.1) *
            ∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν ∂(μ.prod κ) := by
        intro m
        rw [← integral_indicator (hΘ m (hA.prod hB))]
        have e : (randomJointAction σ ρ (τ m) ⁻¹' (A ×ˢ B)).indicator
            (fun x : (α × E) × β => ψ x.1.1 * g x.2) = fun x => ψ x.1.1 *
              A.indicator 1 (σ (τ m x.1) x.1.1) * (g x.2 * B.indicator 1 (ρ (τ m x.1) x.2)) := by
          funext x
          by_cases h1 : σ (τ m x.1) x.1.1 ∈ A <;> by_cases h2 : ρ (τ m x.1) x.2 ∈ B <;>
            simp [randomJointAction, h1, h2]
        have hAm : Measurable fun x : (α × E) × β => A.indicator (1 : α → ℝ) (σ (τ m x.1) x.1.1) :=
          (measurable_const.indicator hA).comp (hΘ m).fst
        have hBm : Measurable fun x : (α × E) × β => B.indicator (1 : β → ℝ) (ρ (τ m x.1) x.2) :=
          (measurable_const.indicator hB).comp (hΘ m).snd
        have hfi : Integrable (fun x : (α × E) × β => ψ x.1.1 *
            A.indicator 1 (σ (τ m x.1) x.1.1) * (g x.2 * B.indicator 1 (ρ (τ m x.1) x.2)))
            ((μ.prod κ).prod ν) := by
          refine integrable_of_measurable_abs_le
            (((hψ.comp (measurable_fst.comp measurable_fst)).mul hAm).mul
              ((hg.comp measurable_snd).mul hBm)) (C := Mψ * Mg) fun x => ?_
          have hia : |A.indicator (1 : α → ℝ) (σ (τ m x.1) x.1.1)| ≤ 1 := by
            by_cases h : σ (τ m x.1) x.1.1 ∈ A <;> simp [h]
          have hib : |B.indicator (1 : β → ℝ) (ρ (τ m x.1) x.2)| ≤ 1 := by
            by_cases h : ρ (τ m x.1) x.2 ∈ B <;> simp [h]
          rw [abs_mul, abs_mul, abs_mul]
          have h0ψ : 0 ≤ Mψ := (abs_nonneg _).trans (hψb x.1.1)
          have h0g : 0 ≤ Mg := (abs_nonneg _).trans (hgb x.2)
          calc |ψ x.1.1| * |A.indicator (1 : α → ℝ) (σ (τ m x.1) x.1.1)| *
                (|g x.2| * |B.indicator (1 : β → ℝ) (ρ (τ m x.1) x.2)|)
              ≤ (Mψ * 1) * (Mg * 1) := by
                gcongr
                · exact hψb _
                · exact hgb _
            _ = Mψ * Mg := by ring
        rw [e, integral_prod _ hfi]
        congr 1
        funext p
        exact integral_const_mul (ψ p.1 * A.indicator (1 : α → ℝ) (σ (τ m p) p.1))
          (fun e => g e * B.indicator (1 : β → ℝ) (ρ (τ m p) e))
      have hI : ∀ m, Measurable fun p : α × E => ∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν := by
        intro m
        have hj : Measurable fun x : (α × E) × β => g x.2 * B.indicator (1 : β → ℝ) (ρ (τ m x.1) x.2) :=
          (hg.comp measurable_snd).mul ((measurable_const.indicator hB).comp (hΘ m).snd)
        exact hj.stronglyMeasurable.integral_prod_right'.measurable
      have hIb : ∀ m p, |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν| ≤ Mg := by
        intro m p
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ e, |g e * B.indicator 1 (ρ (τ m p) e)| ∂ν ≤ ∫ _, Mg ∂ν := by
              refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
                (integrable_const _) (ae_of_all _ fun e => ?_)
              dsimp only
              rw [abs_mul]
              have hib : |B.indicator (1 : β → ℝ) (ρ (τ m p) e)| ≤ 1 := by
                by_cases h : ρ (τ m p) e ∈ B <;> simp [h]
              calc |g e| * |B.indicator (1 : β → ℝ) (ρ (τ m p) e)| ≤ Mg * 1 :=
                    mul_le_mul (hgb e) hib (abs_nonneg _) ((abs_nonneg _).trans (hgb e))
                _ = Mg := mul_one _
          _ = Mg := by simp
      refine squeeze_zero_norm (a := fun m => Mψ * ∫ p, |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν|
        ∂(μ.prod κ)) (fun m => ?_) ?_
      · rw [hcomp m, Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        rw [← integral_const_mul Mψ]
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          ((integrable_of_measurable_abs_le (hI m).abs (C := Mg) fun p => by
            rw [abs_abs]; exact hIb m p).const_mul Mψ) (ae_of_all _ fun p => ?_)
        have hia : |A.indicator (1 : α → ℝ) (σ (τ m p) p.1)| ≤ 1 := by
          by_cases h : σ (τ m p) p.1 ∈ A <;> simp [h]
        dsimp only
        rw [abs_mul, abs_mul]
        calc |ψ p.1| * |A.indicator (1 : α → ℝ) (σ (τ m p) p.1)| *
              |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν|
            ≤ Mψ * 1 * |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν| :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hψb p.1) hia (abs_nonneg _)
                ((abs_nonneg _).trans (hψb p.1))) (abs_nonneg _)
          _ = Mψ * |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν| := by ring
      · simpa using (hmix B hB).const_mul Mψ
    · intro t ht hC
      have hzero : ∫ x, ψ x.1.1 * g x.2 ∂((μ.prod κ).prod ν) = 0 := by
        rw [integral_prod_mul (fun p : α × E => ψ p.1) g, hg0, mul_zero]
      simp only [preimage_compl]
      have e : ∀ m, ∫ x in (randomJointAction σ ρ (τ m) ⁻¹' t)ᶜ, ψ x.1.1 * g x.2 ∂((μ.prod κ).prod ν) =
          0 - ∫ x in randomJointAction σ ρ (τ m) ⁻¹' t, ψ x.1.1 * g x.2 ∂((μ.prod κ).prod ν) := by
        intro m
        rw [setIntegral_compl (hΘ m ht) hwi, hzero]
      simp only [e]
      simpa using (tendsto_const_nhds (x := (0 : ℝ))).sub hC
    · intro t hdisj htm hC
      have hsum : ∀ m, ∫ x in randomJointAction σ ρ (τ m) ⁻¹' ⋃ i, t i, ψ x.1.1 * g x.2
          ∂((μ.prod κ).prod ν) = ∑' i, ∫ x in randomJointAction σ ρ (τ m) ⁻¹' t i, ψ x.1.1 * g x.2
            ∂((μ.prod κ).prod ν) := by
        intro m
        rw [preimage_iUnion]
        exact integral_iUnion (fun i => hΘ m (htm i))
          (fun i j hij => (hdisj hij).preimage _) hwi.integrableOn
      simp only [hsum]
      have hsumm : Summable fun i => Mψ * Mg * ((μ.prod ν) (t i)).toReal := by
        refine (ENNReal.summable_toReal ?_).mul_left _
        rw [← measure_iUnion hdisj htm]
        exact measure_ne_top _ _
      have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hsumm (g := fun _ => (0 : ℝ))
        (fun i => hC i) (Eventually.of_forall fun m i => by
          rw [Real.norm_eq_abs]; exact hbound m (t i) (htm i))
      simpa using h
  exact (tendsto_congr fun m => hset m S hS).2 hint

/-- **The correlations with a bounded functional of the transported pair tend to zero.** A bounded measurable `F`
is uniformly within `1/N` of the finite combination `⌊N F⌋ / N` of indicators of measurable level sets, to which
`tendsto_integral_indicator_randomJointAction` applies. -/
theorem tendsto_integral_randomJointAction_of_bounded {μ : Measure α} {ν : Measure β} {κ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {σ : 𝒯 → α → α} {ρ : 𝒯 → β → β} (hσ : Measurable fun q : 𝒯 × α => σ q.1 q.2)
    (hρ : Measurable fun q : 𝒯 × β => ρ q.1 q.2) {τ : ℕ → α × E → 𝒯} (hτ : ∀ m, Measurable (τ m))
    (hlaw : ∀ m, ((μ.prod κ).prod ν).map (randomJointAction σ ρ (τ m)) = μ.prod ν)
    {ψ : α → ℝ} {g : β → ℝ} (hψ : Measurable ψ) (hg : Measurable g) {Mψ Mg : ℝ}
    (hψb : ∀ a, |ψ a| ≤ Mψ) (hgb : ∀ e, |g e| ≤ Mg) (hg0 : ∫ e, g e ∂ν = 0)
    (hmix : ∀ B : Set β, MeasurableSet B →
      Tendsto (fun m => ∫ p, |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν| ∂(μ.prod κ)) atTop (𝓝 0))
    {F : α × β → ℝ} (hF : Measurable F) {M : ℝ} (hFb : ∀ y, |F y| ≤ M) :
    Tendsto (fun m => ∫ x, ψ x.1.1 * g x.2 * F (randomJointAction σ ρ (τ m) x)
      ∂((μ.prod κ).prod ν)) atTop (𝓝 0) := by
  have hΘ : ∀ m, Measurable (randomJointAction σ ρ (τ m)) := fun m =>
    measurable_randomJointAction hσ hρ (hτ m)
  have hψb' : ∀ a, |ψ a| ≤ |Mψ| := fun a => (hψb a).trans (le_abs_self _)
  have hgb' : ∀ e, |g e| ≤ |Mg| := fun e => (hgb e).trans (le_abs_self _)
  have hint : ∀ m (G : α × β → ℝ), Measurable G → ∀ C : ℝ, (∀ y, |G y| ≤ C) →
      Integrable (fun x => ψ x.1.1 * g x.2 * G (randomJointAction σ ρ (τ m) x))
        ((μ.prod κ).prod ν) := by
    intro m G hG C hC
    exact integrable_of_measurable_abs_le
      (((hψ.comp (measurable_fst.comp measurable_fst)).mul (hg.comp measurable_snd)).mul
        (hG.comp (hΘ m))) (C := |Mψ| * |Mg| * C) fun x =>
      abs_mul_mul_le_of_abs_le (hψb' _) (hgb' _) (hC _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim : Tendsto (fun r : ℝ => |Mψ| * |Mg| * r⁻¹) atTop (𝓝 (|Mψ| * |Mg| * 0)) :=
    tendsto_inv_atTop_zero.const_mul _
  have hε2 : |Mψ| * |Mg| * 0 < ε / 2 := by
    rw [mul_zero]
    exact half_pos hε
  obtain ⟨N, hNε, hNpos⟩ :=
    ((hlim.eventually (gt_mem_nhds hε2)).and (eventually_gt_atTop (0 : ℝ))).exists
  have hN0 : N ≠ 0 := hNpos.ne'
  have hk : Measurable fun y => ⌊N * F y⌋ := (measurable_const.mul hF).floor
  have hS : ∀ j : ℤ, MeasurableSet {y : α × β | ⌊N * F y⌋ = j} := fun j =>
    hk (measurableSet_singleton j)
  have happrox : ∀ y, |F y - (⌊N * F y⌋ : ℝ) / N| ≤ N⁻¹ := by
    intro y
    have h1 : (⌊N * F y⌋ : ℝ) ≤ N * F y := Int.floor_le _
    have h2 : N * F y < (⌊N * F y⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have e : F y - (⌊N * F y⌋ : ℝ) / N = (N * F y - ⌊N * F y⌋) * N⁻¹ := by
      rw [div_eq_mul_inv, sub_mul, mul_right_comm, mul_inv_cancel₀ hN0, one_mul]
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hNpos)]
    have h3 : |N * F y - ⌊N * F y⌋| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |N * F y - ⌊N * F y⌋| * N⁻¹ ≤ 1 * N⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 hNpos.le)
      _ = N⁻¹ := one_mul _
  have hsm : Measurable fun y => (⌊N * F y⌋ : ℝ) / N :=
    ((measurable_of_countable fun j : ℤ => (j : ℝ)).comp hk).div_const N
  have hsb : ∀ y, |(⌊N * F y⌋ : ℝ) / N| ≤ M + N⁻¹ := by
    intro y
    have h1 := happrox y
    have h2 := hFb y
    have h3 := abs_sub_abs_le_abs_sub ((⌊N * F y⌋ : ℝ) / N) (F y)
    have h4 : |(⌊N * F y⌋ : ℝ) / N - F y| = |F y - (⌊N * F y⌋ : ℝ) / N| := abs_sub_comm _ _
    linarith
  have hmem : ∀ y, ⌊N * F y⌋ ∈ Finset.Icc ⌊N * -M⌋ ⌊N * M⌋ := by
    intro y
    have h := abs_le.1 (hFb y)
    exact Finset.mem_Icc.2 ⟨Int.floor_mono (mul_le_mul_of_nonneg_left h.1 hNpos.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left h.2 hNpos.le)⟩
  have hdecomp : ∀ y, (⌊N * F y⌋ : ℝ) / N = ∑ j ∈ Finset.Icc ⌊N * -M⌋ ⌊N * M⌋,
      (j : ℝ) / N * {y' : α × β | ⌊N * F y'⌋ = j}.indicator 1 y := by
    intro y
    rw [Finset.sum_eq_single ⌊N * F y⌋]
    · rw [indicator_of_mem (show y ∈ {y' : α × β | ⌊N * F y'⌋ = ⌊N * F y⌋} from rfl), Pi.one_apply,
        mul_one]
    · intro j _ hj
      rw [indicator_of_notMem (show y ∉ {y' : α × β | ⌊N * F y'⌋ = j} from fun h => hj h.symm),
        mul_zero]
    · intro h
      exact absurd (hmem y) h
  have hsum : ∀ m, ∫ x, ψ x.1.1 * g x.2 * ((⌊N * F (randomJointAction σ ρ (τ m) x)⌋ : ℝ) / N)
      ∂((μ.prod κ).prod ν) = ∑ j ∈ Finset.Icc ⌊N * -M⌋ ⌊N * M⌋, (j : ℝ) / N *
        ∫ x, ψ x.1.1 * g x.2 * {y : α × β | ⌊N * F y⌋ = j}.indicator 1 (randomJointAction σ ρ (τ m) x)
          ∂((μ.prod κ).prod ν) := by
    intro m
    simp_rw [hdecomp, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_const_mul ((j : ℝ) / N)]
      congr 1
      funext x
      ring
    · intro j _
      exact hint m (fun y => (j : ℝ) / N * {y' : α × β | ⌊N * F y'⌋ = j}.indicator 1 y)
        (measurable_const.mul (measurable_const.indicator (hS j))) (|(j : ℝ) / N|) fun y => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (abs_indicator_one_apply_le _ _)
  have hJ : Tendsto (fun m => ∑ j ∈ Finset.Icc ⌊N * -M⌋ ⌊N * M⌋, (j : ℝ) / N *
        ∫ x, ψ x.1.1 * g x.2 * {y : α × β | ⌊N * F y⌋ = j}.indicator 1 (randomJointAction σ ρ (τ m) x)
          ∂((μ.prod κ).prod ν)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.Icc ⌊N * -M⌋ ⌊N * M⌋) fun j _ =>
      (tendsto_integral_indicator_randomJointAction hσ hρ hτ hlaw hψ hg hψb hgb hg0 hmix
        (hS j)).const_mul ((j : ℝ) / N)
    simpa using h
  have hdiff : ∀ m, |∫ x, ψ x.1.1 * g x.2 * F (randomJointAction σ ρ (τ m) x) ∂((μ.prod κ).prod ν) -
      ∫ x, ψ x.1.1 * g x.2 * ((⌊N * F (randomJointAction σ ρ (τ m) x)⌋ : ℝ) / N)
        ∂((μ.prod κ).prod ν)| ≤ |Mψ| * |Mg| * N⁻¹ := by
    intro m
    rw [← integral_sub (hint m F hF M hFb) (hint m _ hsm _ hsb)]
    refine abs_integral_le_of_forall_abs_le_of_isProbabilityMeasure fun x => ?_
    try dsimp only
    rw [← mul_sub]
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hψb' _) (hgb' _) (abs_nonneg _) (abs_nonneg _)) (happrox _)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  obtain ⟨m₀, hm₀⟩ := Metric.tendsto_atTop.1 hJ (ε / 2) (half_pos hε)
  refine ⟨m₀, fun m hm => ?_⟩
  have h1 := hm₀ m hm
  have h2 := hdiff m
  rw [hsum m] at h2
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have h3 := abs_sub_abs_le_abs_sub (∫ x, ψ x.1.1 * g x.2 * F (randomJointAction σ ρ (τ m) x)
    ∂((μ.prod κ).prod ν)) (∑ j ∈ Finset.Icc ⌊N * -M⌋ ⌊N * M⌋, (j : ℝ) / N *
      ∫ x, ψ x.1.1 * g x.2 * {y : α × β | ⌊N * F y⌋ = j}.indicator 1 (randomJointAction σ ρ (τ m) x)
        ∂((μ.prod κ).prod ν))
  linarith

/-- **A jointly invariant bounded functional factors through the first coordinate** (the tensor-approximation step
of the written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(c) Joint invariance", line 44). Let `μ`, `ν` be
probability laws, `σ_t`, `ρ_t` jointly measurable actions, and `τ_m` random parameters (in `T₀`) built from `a` and
independent auxiliary randomness of law `κ`, such that `σ_{τ_m}` preserves `μ`, every `ρ_t` (`t ∈ T₀`) preserves
`ν`, and the second factor mixes along `τ_m`: `∫ |ν(B' ∩ ρ_{τ_m}⁻¹ B) − ν(B') ν(B)| → 0`. Then a bounded measurable
`V` with `V(σ_t a, ρ_t e) = V(a, e)` for all `t ∈ T₀`, for almost every `a` and almost every `e`, is
`μ ⊗ ν`-almost everywhere equal to its partial mean `v(a) = ∫ V(a, e) ν(de)`. -/
theorem ae_eq_integral_of_jointInvariance {μ : Measure α} {ν : Measure β} {κ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {σ : 𝒯 → α → α} {ρ : 𝒯 → β → β} (hσ : Measurable fun q : 𝒯 × α => σ q.1 q.2)
    (hρ : Measurable fun q : 𝒯 × β => ρ q.1 q.2) {T₀ : Set 𝒯} {τ : ℕ → α × E → 𝒯}
    (hτ : ∀ m, Measurable (τ m)) (hτT : ∀ m p, τ m p ∈ T₀)
    (hσlaw : ∀ m, (μ.prod κ).map (fun p => σ (τ m p) p.1) = μ) (hρlaw : ∀ t ∈ T₀, ν.map (ρ t) = ν)
    (hmix : ∀ B' B : Set β, MeasurableSet B' → MeasurableSet B →
      Tendsto (fun m => ∫ p, |ν.real (B' ∩ ρ (τ m p) ⁻¹' B) - ν.real B' * ν.real B| ∂(μ.prod κ))
        atTop (𝓝 0))
    {V : α × β → ℝ} (hV : Measurable V) {M : ℝ} (hVb : ∀ y, |V y| ≤ M)
    (hinv : ∀ᵐ a ∂μ, ∀ᵐ e ∂ν, ∀ t ∈ T₀, V (σ t a, ρ t e) = V (a, e)) :
    V =ᵐ[μ.prod ν] fun y => ∫ e, V (y.1, e) ∂ν := by
  have hρt : ∀ t, Measurable (ρ t) := fun t => hρ.comp (measurable_const.prodMk measurable_id)
  have hΘ : ∀ m, Measurable (randomJointAction σ ρ (τ m)) := fun m =>
    measurable_randomJointAction hσ hρ (hτ m)
  have hlaw : ∀ m, ((μ.prod κ).prod ν).map (randomJointAction σ ρ (τ m)) = μ.prod ν := fun m =>
    map_randomJointAction hσ hρ (hτ m) (hσlaw m) fun p => hρlaw _ (hτT m p)
  -- the projection `((a, x), e) ↦ (a, e)` is the action with trivial `σ` and `ρ`
  have hπm : Measurable (randomJointAction (fun (_ : 𝒯) (a : α) => a) (fun (_ : 𝒯) (e : β) => e)
      (τ 0)) :=
    measurable_randomJointAction measurable_snd measurable_snd (hτ 0)
  have hπ : ((μ.prod κ).prod ν).map (randomJointAction (fun (_ : 𝒯) (a : α) => a)
      (fun (_ : 𝒯) (e : β) => e) (τ 0)) = μ.prod ν :=
    map_randomJointAction measurable_snd measurable_snd (hτ 0)
      (by
        show (μ.prod κ).map Prod.fst = μ
        rw [Measure.map_fst_prod, measure_univ, one_smul])
      fun _ => Measure.map_id
  have hπint : ∀ f : α × β → ℝ, Measurable f →
      ∫ x, f (x.1.1, x.2) ∂((μ.prod κ).prod ν) = ∫ y, f y ∂(μ.prod ν) := by
    intro f hf
    rw [← hπ, integral_map hπm.aemeasurable hf.aestronglyMeasurable]
    rfl
  -- correlations of `V` with `ψ(a) g(e)`, `∫ g dν = 0`, vanish
  have hclaim : ∀ (ψ : α → ℝ) (g : β → ℝ), Measurable ψ → Measurable g → (∀ a, |ψ a| ≤ 1) →
      ∀ Mg : ℝ, (∀ e, |g e| ≤ Mg) → ∫ e, g e ∂ν = 0 →
      (∀ B : Set β, MeasurableSet B → Tendsto (fun m => ∫ p, |∫ e, g e * B.indicator 1 (ρ (τ m p) e) ∂ν|
        ∂(μ.prod κ)) atTop (𝓝 0)) →
      ∫ y, ψ y.1 * g y.2 * V y ∂(μ.prod ν) = 0 := by
    intro ψ g hψ hg hψb Mg hgb hg0 hmixg
    have hf3 : Measurable fun y : α × β => ψ y.1 * g y.2 * V y :=
      ((hψ.comp measurable_fst).mul (hg.comp measurable_snd)).mul hV
    have hconst : ∀ m, ∫ x, ψ x.1.1 * g x.2 * V (randomJointAction σ ρ (τ m) x)
        ∂((μ.prod κ).prod ν) = ∫ y, ψ y.1 * g y.2 * V y ∂(μ.prod ν) := by
      intro m
      rw [← hπint _ hf3]
      have hi1 : Integrable (fun x : (α × E) × β => ψ x.1.1 * g x.2 * V (randomJointAction σ ρ (τ m) x))
          ((μ.prod κ).prod ν) :=
        integrable_of_measurable_abs_le
          (((hψ.comp (measurable_fst.comp measurable_fst)).mul (hg.comp measurable_snd)).mul
            (hV.comp (hΘ m))) fun x => abs_mul_mul_le_of_abs_le (hψb _) (hgb _) (hVb _)
      have hi2 : Integrable (fun x : (α × E) × β => ψ x.1.1 * g x.2 * V (x.1.1, x.2))
          ((μ.prod κ).prod ν) :=
        integrable_of_measurable_abs_le
          (((hψ.comp (measurable_fst.comp measurable_fst)).mul (hg.comp measurable_snd)).mul
            (hV.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
          fun x => abs_mul_mul_le_of_abs_le (hψb _) (hgb _) (hVb _)
      rw [integral_prod _ hi1, integral_prod _ hi2]
      refine integral_congr_ae ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hinv] with p hp
      refine integral_congr_ae ?_
      filter_upwards [hp] with e he
      simp only [randomJointAction, he (τ m p) (hτT m p)]
    have ht := tendsto_integral_randomJointAction_of_bounded hσ hρ hτ hlaw hψ hg hψb hgb hg0 hmixg hV
      hVb
    have ht' : Tendsto (fun _ : ℕ => ∫ y, ψ y.1 * g y.2 * V y ∂(μ.prod ν)) atTop (𝓝 0) :=
      (tendsto_congr hconst).1 ht
    exact tendsto_nhds_unique tendsto_const_nhds ht'
  -- the centred indicators `1_B − ν(B)`
  have hcorr : ∀ t ∈ T₀, ∀ B' B : Set β, MeasurableSet B' → MeasurableSet B →
      ∫ e, (B'.indicator (1 : β → ℝ) e - ν.real B') * B.indicator 1 (ρ t e) ∂ν =
        ν.real (B' ∩ ρ t ⁻¹' B) - ν.real B' * ν.real B := by
    intro t ht B' B hB' hB
    have hpre : MeasurableSet (ρ t ⁻¹' B) := hρt t hB
    have hpreν : ν.real (ρ t ⁻¹' B) = ν.real B := by
      rw [measureReal_def, measureReal_def, ← Measure.map_apply (hρt t) hB, hρlaw t ht]
    have e1 : (fun e => (B'.indicator (1 : β → ℝ) e - ν.real B') * B.indicator 1 (ρ t e)) =
        fun e => (B' ∩ ρ t ⁻¹' B).indicator 1 e - ν.real B' * (ρ t ⁻¹' B).indicator 1 e := by
      funext e
      by_cases h1 : e ∈ B' <;> by_cases h2 : ρ t e ∈ B <;> simp [h1, h2]
    have hi1 : Integrable ((B' ∩ ρ t ⁻¹' B).indicator (1 : β → ℝ)) ν :=
      (integrable_const (1 : ℝ)).indicator (hB'.inter hpre)
    have hi2 : Integrable (fun e => ν.real B' * (ρ t ⁻¹' B).indicator (1 : β → ℝ) e) ν :=
      ((integrable_const (1 : ℝ)).indicator hpre).const_mul _
    rw [e1, integral_sub hi1 hi2, integral_const_mul (ν.real B'),
      integral_indicator_one (hB'.inter hpre), integral_indicator_one hpre, hpreν]
  have hg0B : ∀ B : Set β, MeasurableSet B → ∫ e, (B.indicator (1 : β → ℝ) e - ν.real B) ∂ν = 0 := by
    intro B hB
    have hi : Integrable (B.indicator (1 : β → ℝ)) ν := (integrable_const (1 : ℝ)).indicator hB
    rw [integral_sub hi (integrable_const _), integral_indicator_one hB]
    simp
  have hmixB : ∀ B' : Set β, MeasurableSet B' → ∀ B : Set β, MeasurableSet B →
      Tendsto (fun m => ∫ p, |∫ e, (B'.indicator (1 : β → ℝ) e - ν.real B') *
        B.indicator 1 (ρ (τ m p) e) ∂ν| ∂(μ.prod κ)) atTop (𝓝 0) := by
    intro B' hB' B hB
    refine (tendsto_congr fun m => ?_).1 (hmix B' B hB' hB)
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hcorr (τ m p) (hτT m p) B' B hB' hB]
  have hgB : ∀ (B : Set β) (e : β), |B.indicator (1 : β → ℝ) e - ν.real B| ≤ 1 + |ν.real B| := by
    intro B e
    have h1 := abs_le.1 (abs_indicator_one_apply_le B e)
    have h2 := le_abs_self (ν.real B)
    have h3 := neg_abs_le (ν.real B)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  -- the partial mean
  have hv : Measurable fun a => ∫ e, V (a, e) ∂ν := hV.stronglyMeasurable.integral_prod_right'.measurable
  have hvb : ∀ a, |∫ e, V (a, e) ∂ν| ≤ M := fun a =>
    abs_integral_le_of_forall_abs_le_of_isProbabilityMeasure fun e => hVb _
  refine ae_eq_of_setIntegral_rectangle_eq (integrable_of_measurable_abs_le hV hVb)
    (integrable_of_measurable_abs_le (hv.comp measurable_fst) fun y => hvb y.1) fun A B hA hB => ?_
  have hψm : Measurable (A.indicator (1 : α → ℝ)) := measurable_const.indicator hA
  have hBm : Measurable (B.indicator (1 : β → ℝ)) := measurable_const.indicator hB
  have hrect : ∀ f : α × β → ℝ, ∫ y in A ×ˢ B, f y ∂μ.prod ν =
      ∫ y, A.indicator (1 : α → ℝ) y.1 * B.indicator (1 : β → ℝ) y.2 * f y ∂μ.prod ν := by
    intro f
    rw [← integral_indicator (hA.prod hB)]
    congr 1
    funext y
    by_cases h1 : y.1 ∈ A <;> by_cases h2 : y.2 ∈ B <;> simp [h1, h2]
  have hL : ∫ y, A.indicator (1 : α → ℝ) y.1 * B.indicator (1 : β → ℝ) y.2 * V y ∂μ.prod ν =
      ν.real B * ∫ a, A.indicator (1 : α → ℝ) a * ∫ e, V (a, e) ∂ν ∂μ := by
    have hc := hclaim (A.indicator 1) (fun e => B.indicator (1 : β → ℝ) e - ν.real B) hψm
      (hBm.sub measurable_const) (abs_indicator_one_apply_le A) (1 + |ν.real B|) (hgB B) (hg0B B hB)
      (hmixB B hB)
    have hsplit : (fun y : α × β => A.indicator (1 : α → ℝ) y.1 * B.indicator (1 : β → ℝ) y.2 * V y) =
        fun y => A.indicator 1 y.1 * (B.indicator 1 y.2 - ν.real B) * V y +
          ν.real B * (A.indicator 1 y.1 * V y) := by
      funext y
      ring
    have hia : Integrable (fun y : α × β => A.indicator (1 : α → ℝ) y.1 *
        (B.indicator (1 : β → ℝ) y.2 - ν.real B) * V y) (μ.prod ν) :=
      integrable_of_measurable_abs_le
        (((hψm.comp measurable_fst).mul ((hBm.comp measurable_snd).sub measurable_const)).mul hV)
        fun y => abs_mul_mul_le_of_abs_le (abs_indicator_one_apply_le A y.1) (hgB B y.2) (hVb y)
    have hic : Integrable (fun y : α × β => A.indicator (1 : α → ℝ) y.1 * V y) (μ.prod ν) :=
      integrable_of_measurable_abs_le ((hψm.comp measurable_fst).mul hV) (C := 1 * M) fun y => by
        rw [abs_mul]
        exact mul_le_mul (abs_indicator_one_apply_le A y.1) (hVb y) (abs_nonneg _) zero_le_one
    rw [hsplit, integral_add hia (hic.const_mul _), hc, zero_add, integral_const_mul (ν.real B),
      integral_prod _ hic]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    exact integral_const_mul (A.indicator (1 : α → ℝ) a) (fun e => V (a, e))
  have hR : ∫ y, A.indicator (1 : α → ℝ) y.1 * B.indicator (1 : β → ℝ) y.2 * (∫ e, V (y.1, e) ∂ν)
      ∂μ.prod ν = ν.real B * ∫ a, A.indicator (1 : α → ℝ) a * ∫ e, V (a, e) ∂ν ∂μ := by
    have h : ∫ z, (A.indicator (1 : α → ℝ) z.1 * ∫ e, V (z.1, e) ∂ν) * B.indicator (1 : β → ℝ) z.2
        ∂(μ.prod ν) = (∫ a, A.indicator (1 : α → ℝ) a * ∫ e, V (a, e) ∂ν ∂μ) *
          ∫ e, B.indicator (1 : β → ℝ) e ∂ν :=
      integral_prod_mul (fun a => A.indicator (1 : α → ℝ) a * ∫ e, V (a, e) ∂ν)
        (B.indicator (1 : β → ℝ))
    rw [integral_indicator_one hB, mul_comm _ (ν.real B)] at h
    rw [← h]
    congr 1
    funext y
    ring
  rw [hrect V, hrect (fun y => ∫ e, V (y.1, e) ∂ν), hL, hR]

end Abstract

/-! ### The similarity actions on fields and curves -/

section Similarity

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal

/-- The LQG coordinate change `h ↦ h(C · + z) + Q log C` at the parameter `t = (C, z)`, extended by the identity at
`C ≤ 0`. -/
def lqgSimilarityAction (γ : ℝ) (t : ℝ × ℂ) (h : Field) : Field :=
  if 0 < t.1 then lqgSimilarityField γ t.1 t.2 h else h

theorem lqgSimilarityAction_of_pos (γ : ℝ) {t : ℝ × ℂ} (ht : 0 < t.1) (h : Field) :
    lqgSimilarityAction γ t h = lqgSimilarityField γ t.1 t.2 h := by
  simp only [lqgSimilarityAction, ht, ↓reduceIte]

/-- **The LQG coordinate change is jointly measurable in the scale, the centre and the field**:
`h(C · + z) = (h(· + z))(C ·)` (`LQGMetric.GM.affineComp_comp`), the dilation is jointly measurable in `(C, h)` and
the translation in `(z, h)`. -/
theorem measurable_lqgSimilarityAction (γ : ℝ) :
    Measurable fun q : (ℝ × ℂ) × Field => lqgSimilarityAction γ q.1 q.2 := by
  have htr : Measurable fun q : (ℝ × ℂ) × Field => LQGMetric.affineComp 1 q.1.2 q.2 :=
    (MatedCRTHarmonic.GMSCase.measurable_affineComp_center 1).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hsc : Measurable fun q : (ℝ × ℂ) × Field =>
      LQGMetric.affineComp q.1.1 0 (LQGMetric.affineComp 1 q.1.2 q.2) :=
    MatedCRTHarmonic.MoTPort.ConeMeas.measurable_affineComp_joint.comp
      ((measurable_fst.comp measurable_fst).prodMk htr)
  have hpos : Measurable fun q : (ℝ × ℂ) × Field => LQGMetric.addConst
      (LQGMetric.affineComp q.1.1 0 (LQGMetric.affineComp 1 q.1.2 q.2)) (lqgQ γ * Real.log q.1.1) := by
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    simp only [LQGMetric.GFFInv.addConst_apply]
    exact ((LQGMetric.measurable_distOn_apply φ).comp hsc).add
      ((measurable_const.mul (Real.measurable_log.comp (measurable_fst.comp measurable_fst))).const_mul _)
  have e : (fun q : (ℝ × ℂ) × Field => lqgSimilarityAction γ q.1 q.2) = fun q =>
      if 0 < q.1.1 then LQGMetric.addConst
        (LQGMetric.affineComp q.1.1 0 (LQGMetric.affineComp 1 q.1.2 q.2)) (lqgQ γ * Real.log q.1.1)
      else q.2 := by
    funext q
    by_cases hq : 0 < q.1.1
    · simp only [lqgSimilarityAction, lqgSimilarityField, hq, ↓reduceIte]
      rw [LQGMetric.GM.affineComp_comp hq.ne' one_ne_zero]
      simp only [one_mul, mul_zero, zero_add]
    · simp only [lqgSimilarityAction, hq, ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst)) hpos
    measurable_snd

/-- **The rerooting of a curve at `(z, C)` is jointly measurable in `(C, z)` and the curve** (the first hitting time
is jointly measurable, `GMS4b.measurable_hitTime`; the curves are determined by their rational values). -/
theorem measurable_affineReroot_joint :
    Measurable fun q : (ℝ × ℂ) × C(ℝ, ℂ) => affineReroot q.1.2 q.1.1 0 q.2 := by
  refine (MatedCRTHarmonic.GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  refine measurable_pi_iff.mpr fun t => ?_
  have hT : Measurable fun q : (ℝ × ℂ) × C(ℝ, ℂ) => firstHit q.2 q.1.2 + q.1.1 ^ 2 * (t : ℝ) :=
    (GMS4b.measurable_hitTime.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).add
      (((measurable_fst.comp measurable_fst).pow_const 2).mul_const _)
  have hev : Measurable fun q : (ℝ × ℂ) × C(ℝ, ℂ) => q.2 (firstHit q.2 q.1.2 + q.1.1 ^ 2 * (t : ℝ)) :=
    continuous_eval.measurable.comp (measurable_snd.prodMk hT)
  have hc : Measurable fun q : (ℝ × ℂ) × C(ℝ, ℂ) =>
      (((q.1.1 : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))⁻¹) :=
    ((Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul_const _).inv
  change Measurable fun q : (ℝ × ℂ) × C(ℝ, ℂ) =>
    (((q.1.1 : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))⁻¹) *
      (q.2 (firstHit q.2 q.1.2 + q.1.1 ^ 2 * (t : ℝ)) - q.1.2)
  exact hc.mul (hev.sub (measurable_snd.comp measurable_fst))

theorem measurable_affineReroot (z : ℂ) (s : ℝ) : Measurable (affineReroot z s 0) := by
  have h := measurable_affineReroot_joint.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : C(ℝ, ℂ) => (((s, z) : ℝ × ℂ), x))
  simp only [Function.comp_def] at h
  exact h

/-- **The normalized similarity step of a circle-average array modulo `2πχ`**: the array of `h(z + s ·)` at positive
radii, `(ρ, w) ↦ f(sρ, z + sw)`, shifted by the multiple of `2πχ` which brings `f(s, z)` into `[0, 2πχ)`. On the
array of `(h, u)` it is the array of the normalized pair `(h(z + s ·) − h_s(z), (u + h_s(z)) mod 2πχ)`; at `z = 0` it
is `igDilationStep γ s`. -/
def igSimilarityStep (γ : ℝ) (z : ℂ) (s : ℝ) (f : ℝ × ℂ → ℝ) : ℝ × ℂ → ℝ :=
  fun x => if 0 < x.1 then
    f (s * x.1, z + (s : ℂ) * x.2) -
      ((⌊f (s, z) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) * (2 * Real.pi * igChi γ)
    else 0

theorem measurable_igSimilarityStep (γ : ℝ) (z : ℂ) (s : ℝ) : Measurable (igSimilarityStep γ z s) := by
  refine measurable_pi_iff.2 fun x => ?_
  by_cases hx : 0 < x.1
  · simp only [igSimilarityStep, hx, ↓reduceIte]
    exact (measurable_pi_apply (s * x.1, z + (s : ℂ) * x.2)).sub
      (((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
        (Int.measurable_floor.comp ((measurable_pi_apply ((s, z) : ℝ × ℂ)).div_const _))).mul_const _)
  · simp only [igSimilarityStep, hx, ↓reduceIte]
    exact measurable_const

/-- **Mixing of the whole-plane GFF modulo `2πχ` under similarities with distant centres** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(a) The normalized dilation", lines 15-27: tests by the characters
`exp(i X(f) + 2πi k U / d)`, the covariance of the whole-plane GFF, Duplantier–Sheffield, arXiv:0808.1560, §3.1, and
the variance `Var X_r(z) ≥ log |z|` for `|z| > 1` and every `r > 0`; "They also give convergence of correlations to
the product for any sequence `|z| → ∞` with arbitrary positive scales"). PENDING TRUTH CHECK.

Let `h` be a whole-plane GFF normalized by `h_1(0) = 0` and `u` an independent uniform variable on `[0, 2πχ)`,
`χ = 2/γ − γ/2`, and let `μ` be the law of the circle-average array of `h + u` at positive radii
(`igPosCircleProcess`). For all centres `z_n` with `|z_n| → ∞` and all scales `s_n > 0`, the normalized similarity
steps `T_n = igSimilarityStep γ z_n s_n` satisfy `μ(S₁ ∩ T_n⁻¹ S₂) → μ(S₁) μ(S₂)` for all measurable `S₁`, `S₂`. -/
def IGFieldDistantCentreMixing (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (h : Ω' → Field) (u : Ω' → ℝ),
    LQGMetric.IsNormalizedWPGFF h P' →
    P'.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] → IndepFun h u P' →
    ∀ (z : ℕ → ℂ) (s : ℕ → ℝ), (∀ n, 0 < s n) → Tendsto (fun n => ‖z n‖) atTop atTop →
    ∀ S₁ S₂ : Set (ℝ × ℂ → ℝ), MeasurableSet S₁ → MeasurableSet S₂ →
      Tendsto (fun n => (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
          (S₁ ∩ igSimilarityStep γ (z n) (s n) ⁻¹' S₂)) atTop
        (𝓝 ((P'.map fun ω => igPosCircleProcess (h ω) (u ω)) S₁ *
          (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) S₂))

/-- **Lemma A.4 of Gwynne–Miller–Sheffield at uniform points of dyadic squares of growing mass**
(arXiv:1705.11161, Lemma A.4, `notes/refs/1705.11161.txt` lines 2037-2041: for `m > 0` and `z_m` sampled uniformly
from the largest square of an independent uniform dyadic system containing `0` with `μ_h`-mass at most `m`, there is
a random constant `C_m > 0` with `h(C_m · + z_m) + Q log C_m` equal in law to `h`; the divergence `|z_m| → ∞` in
probability is the written answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, line 41: "Its area tends to infinity since every
fixed ancestor has finite mass"). PENDING TRUTH CHECK.

Let `h = coneField X₀' (coneRadial γ 0 b b')` be the circle-average embedding of the `0`-quantum cone built from a
whole-plane GFF `X₀'` and two independent standard Brownian motions independent of it (`zeroConeFieldOf`), with law
`μ`. There are an auxiliary probability space `(E, κ)` and measurable `C_m > 0`, `z_m` on `Field × E` such that, under
`μ ⊗ κ`, `h(C_m · + z_m) + Q log C_m` has law `μ` for every `m` and `P(|z_m| ≤ R) → 0` for every `R`. -/
def ZeroConeLemmaA4 (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∃ (E : Type) (_ : MeasurableSpace E) (κ : Measure E) (_ : IsProbabilityMeasure κ)
      (C : ℕ → Field × E → ℝ) (z : ℕ → Field × E → ℂ),
      (∀ m, Measurable (C m)) ∧ (∀ m, Measurable (z m)) ∧ (∀ m p, 0 < C m p) ∧
      (∀ m, ((P'.map (zeroConeFieldOf γ X₀' b b')).prod κ).map
          (fun p => lqgSimilarityField γ (C m p) (z m p) p.1) = P'.map (zeroConeFieldOf γ X₀' b b')) ∧
      ∀ R : ℝ, Tendsto (fun m => ((P'.map (zeroConeFieldOf γ X₀' b b')).prod κ) {p | ‖z m p‖ ≤ R})
        atTop (𝓝 0)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The curve map at the normalized similarity steps.** Almost surely the curve map `Φ` of the coupling sends the
array of `(hIG₀, U)` to `ηL`, and for each fixed `(z, s)`, `s > 0`, almost surely it sends the normalized similarity
step of the array to `affineReroot z s 0 ηL` (the coordinate change of imaginary geometry, `IsMatingOfTreesCoupling.igMap`,
at the full turns `φ = −2πm`, which shift the field by `m · 2πχ`). -/
theorem exists_igMap_igSimilarityStep
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ᵐ ω ∂P, Φ (Function.curry (igPosCircleProcess (hIG₀ ω) (U ω))) = ηL ω) ∧
      ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ᵐ ω ∂P,
        Φ (Function.curry (igSimilarityStep γ z s (igPosCircleProcess (hIG₀ ω) (U ω)))) =
          affineReroot z s 0 (ηL ω) := by
  obtain ⟨Φ, hΦm, hign, hrep, hcov, -⟩ := D.igMap
  refine ⟨Φ, hΦm, ?_, fun z s hs => ?_⟩
  · filter_upwards [hrep] with ω hω
    refine (hign _ _ ?_).trans hω.symm
    intro ρ hρ
    exact curry_igPosCircleProcess_of_pos (hIG₀ ω) (U ω) hρ
  · have hm : ∀ m : ℤ, ∀ᵐ ω ∂P,
        Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) (s * ρ) (z + (s : ℂ) * w) + U ω +
          (m : ℝ) * (2 * Real.pi * igChi γ)) = affineReroot z s 0 (ηL ω) := by
      intro m
      filter_upwards [hcov z s (-(2 * Real.pi * (m : ℝ))) hs] with ω hω
      have hexp : Complex.exp ((((-(2 * Real.pi * (m : ℝ))) : ℝ) : ℂ) * Complex.I) = 1 := by
        rw [show ((((-(2 * Real.pi * (m : ℝ))) : ℝ) : ℂ) * Complex.I) =
            ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I _
      have e1 : igPullback γ z s (-(2 * Real.pi * (m : ℝ)))
          (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) = fun ρ w =>
            LQGMetric.circleAvg (hIG₀ ω) (s * ρ) (z + (s : ℂ) * w) + U ω +
              (m : ℝ) * (2 * Real.pi * igChi γ) := by
        funext ρ w
        simp only [igPullback, hexp, mul_one]
        ring
      have e2 : affineReroot z s (-(2 * Real.pi * (m : ℝ))) (ηL ω) = affineReroot z s 0 (ηL ω) := by
        ext t
        simp only [affineReroot, ContinuousMap.coe_mk, hexp, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero]
      rw [e1, e2] at hω
      exact hω
    filter_upwards [ae_all_iff.2 hm] with ω hω
    refine (hign _ _ fun ρ hρ => ?_).trans
      (hω (-⌊(U ω + LQGMetric.circleAvg (hIG₀ ω) s z) / (2 * Real.pi * igChi γ)⌋))
    funext w
    simp only [Function.curry_apply, igSimilarityStep, igPosCircleProcess, hρ, mul_pos hs hρ, hs,
      ↓reduceIte]
    push_cast
    ring

/-- **Mixing of whole-plane space-filling SLE at distant centres** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(c) Joint invariance", lines 33-35: "The mixing estimate in (a) passes to the
curve: the coupling's positive-radius map reads the IG field modulo `d`, and its affine covariance gives `e^T` from
the transformed representative"). For all centres `z_n` with `|z_n| → ∞`, all scales `s_n > 0` and measurable sets
`B₁`, `B₂` of curves, `P(ηL ∈ B₁, affineReroot z_n s_n 0 ηL ∈ B₂) → P(ηL ∈ B₁) P(ηL ∈ B₂)`. -/
theorem tendsto_igCurve_affineReroot_correlation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hmix : IGFieldDistantCentreMixing γ hγ) {z : ℕ → ℂ} {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) {B₁ B₂ : Set C(ℝ, ℂ)} (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂) :
    Tendsto (fun n => (P.map ηL) (B₁ ∩ affineReroot (z n) (s n) 0 ⁻¹' B₂)) atTop
      (𝓝 ((P.map ηL) B₁ * (P.map ηL) B₂)) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hh, hUlaw, hind⟩ := D.igField
  have hUae : AEMeasurable U P := aemeasurable_of_map_eq_igUniform hUlaw
  have hKp : AEMeasurable (fun ω => igPosCircleProcess (hIG₀ ω) (U ω)) P :=
    aemeasurable_igPosCircleProcess hh.1.measurable hUae
  obtain ⟨Φ, hΦm, h1, h2⟩ := exists_igMap_igSimilarityStep (γ := γ) D
  have hcurry : Measurable (Function.curry : (ℝ × ℂ → ℝ) → ℝ → ℂ → ℝ) :=
    measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun w => measurable_pi_apply (r, w)
  have hΦ' : Measurable fun f : ℝ × ℂ → ℝ => Φ (Function.curry f) := hΦm.comp hcurry
  have hηm : Measurable ηL := D.measurable_curves.1
  have hν : P.map ηL = (P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω)).map
      fun f => Φ (Function.curry f) := by
    rw [AEMeasurable.map_map_of_aemeasurable hΦ'.aemeasurable hKp]
    refine Measure.map_congr ?_
    filter_upwards [h1] with ω hω
    exact hω.symm
  have hpair : ∀ n, (P.map ηL) (B₁ ∩ affineReroot (z n) (s n) 0 ⁻¹' B₂) =
      (P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω))
        ((fun f => Φ (Function.curry f)) ⁻¹' B₁ ∩ igSimilarityStep γ (z n) (s n) ⁻¹'
          ((fun f => Φ (Function.curry f)) ⁻¹' B₂)) := by
    intro n
    have hρ : Measurable (affineReroot (z n) (s n) 0) := measurable_affineReroot (z n) (s n)
    have hρη : Measurable fun ω => affineReroot (z n) (s n) 0 (ηL ω) := by
      have h := hρ.comp hηm
      simp only [Function.comp_def] at h
      exact h
    have hg : Measurable fun f : ℝ × ℂ → ℝ =>
        (Φ (Function.curry f), Φ (Function.curry (igSimilarityStep γ (z n) (s n) f))) :=
      hΦ'.prodMk (hΦ'.comp (measurable_igSimilarityStep γ (z n) (s n)))
    have e1 : (P.map ηL) (B₁ ∩ affineReroot (z n) (s n) 0 ⁻¹' B₂) =
        (P.map fun ω => (ηL ω, affineReroot (z n) (s n) 0 (ηL ω))) (B₁ ×ˢ B₂) := by
      rw [Measure.map_apply hηm (hB₁.inter (hρ hB₂)),
        Measure.map_apply (hηm.prodMk hρη) (hB₁.prod hB₂)]
      exact congrArg (fun S => P S) (Set.ext fun _ => Iff.rfl)
    have e2 : (P.map fun ω => (ηL ω, affineReroot (z n) (s n) 0 (ηL ω))) =
        (P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω)).map fun f =>
          (Φ (Function.curry f), Φ (Function.curry (igSimilarityStep γ (z n) (s n) f))) := by
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hKp]
      refine Measure.map_congr ?_
      filter_upwards [h1, h2 (z n) (s n) (hs n)] with ω hω1 hω2
      exact Prod.ext hω1.symm hω2.symm
    rw [e1, e2, Measure.map_apply hg (hB₁.prod hB₂)]
    exact congrArg (fun S => (P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω)) S)
      (Set.ext fun _ => Iff.rfl)
  refine (tendsto_congr hpair).2 ?_
  rw [hν, Measure.map_apply hΦ' hB₁, Measure.map_apply hΦ' hB₂]
  exact hmix P hIG₀ U hh hUlaw hind z s hs hz _ _ (hΦ' hB₁) (hΦ' hB₂)

/-- **Uniform mixing of the curve at distant centres**: the correlation of `{ηL ∈ B₁}` and
`{affineReroot z s 0 ηL ∈ B₂}` is within `ε` of the product of the probabilities for all scales `s > 0` and all
centres with `|z| ≥ R` (from the sequential form `tendsto_igCurve_affineReroot_correlation`, by contradiction). -/
theorem exists_uniform_igCurve_affineReroot_correlation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hmix : IGFieldDistantCentreMixing γ hγ) {B₁ B₂ : Set C(ℝ, ℂ)} (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, ∀ s : ℝ, 0 < s → R ≤ ‖z‖ →
      |(P.map ηL).real (B₁ ∩ affineReroot z s 0 ⁻¹' B₂) - (P.map ηL).real B₁ * (P.map ηL).real B₂| ≤ ε := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  by_contra hcon
  push Not at hcon
  choose z s hs hz hbad using hcon
  have hzn : Tendsto (fun n : ℕ => ‖z n‖) atTop atTop :=
    tendsto_atTop_mono (fun n => hz n) tendsto_natCast_atTop_atTop
  have ht := tendsto_igCurve_affineReroot_correlation D hγ hmix (z := fun n : ℕ => z n)
    (s := fun n : ℕ => s n) (fun n => hs n) hzn hB₁ hB₂
  have hne : (P.map ηL) B₁ * (P.map ηL) B₂ ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have ht' := (ENNReal.tendsto_toReal hne).comp ht
  rw [ENNReal.toReal_mul] at ht'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht' ε hε
  have h1 : |(P.map ηL).real (B₁ ∩ affineReroot (z N) (s N) 0 ⁻¹' B₂) -
      (P.map ηL).real B₁ * (P.map ηL).real B₂| < ε := by
    have h := hN N le_rfl
    rw [Real.dist_eq, Function.comp_apply] at h
    simp only [measureReal_def]
    exact h
  exact absurd h1 (not_lt.2 (hbad N).le)

/-- Integrals of `[0, 1]`-valued functions which are uniformly at most `ε` where `‖Z_m‖ ≥ R(ε)` tend to `0` when
`P(‖Z_m‖ ≤ R) → 0` for every `R`. -/
theorem tendsto_integral_of_uniform_of_tendsto_measure_norm_le {E' : Type*} [MeasurableSpace E']
    {Q : Measure E'} [IsProbabilityMeasure Q] {F : ℕ → E' → ℝ} {Z : ℕ → E' → ℂ}
    (hZ : ∀ m, Measurable (Z m)) (hF0 : ∀ m p, 0 ≤ F m p) (hF1 : ∀ m p, F m p ≤ 1)
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ m p, R ≤ ‖Z m p‖ → F m p ≤ ε)
    (hfar : ∀ R : ℝ, Tendsto (fun m => Q {p | ‖Z m p‖ ≤ R}) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ p, F m p ∂Q) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := hunif (ε / 2) (half_pos hε)
  have hreal : Tendsto (fun m => Q.real {p | ‖Z m p‖ ≤ R}) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hfar R)
    rw [ENNReal.toReal_zero, Function.comp_def] at h
    simp only [measureReal_def]
    exact h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hreal (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  have hS : MeasurableSet {p | ‖Z m p‖ ≤ R} := measurableSet_le (hZ m).norm measurable_const
  have hiS : Integrable ({p | ‖Z m p‖ ≤ R}.indicator (1 : E' → ℝ)) Q :=
    (integrable_const (1 : ℝ)).indicator hS
  have hle : ∫ p, F m p ∂Q ≤ ∫ p, (ε / 2 + {p | ‖Z m p‖ ≤ R}.indicator (1 : E' → ℝ) p) ∂Q := by
    refine integral_mono_of_nonneg (ae_of_all _ fun p => hF0 m p) ((integrable_const _).add hiS)
      (ae_of_all _ fun p => ?_)
    show F m p ≤ ε / 2 + {p | ‖Z m p‖ ≤ R}.indicator (1 : E' → ℝ) p
    by_cases hp : ‖Z m p‖ ≤ R
    · rw [Set.indicator_of_mem (show p ∈ {p | ‖Z m p‖ ≤ R} from hp), Pi.one_apply]
      linarith [hF1 m p]
    · rw [Set.indicator_of_notMem (show p ∉ {p | ‖Z m p‖ ≤ R} from hp), add_zero]
      exact hR m p (not_le.1 hp).le
  have hval : ∫ p, (ε / 2 + {p | ‖Z m p‖ ≤ R}.indicator (1 : E' → ℝ) p) ∂Q =
      ε / 2 + Q.real {p | ‖Z m p‖ ≤ R} := by
    rw [integral_add (integrable_const _) hiS, integral_const, probReal_univ, one_smul,
      integral_indicator_one hS]
  have h1 : |Q.real {p | ‖Z m p‖ ≤ R}| < ε / 2 := by
    have h := hN m hm
    rw [Real.dist_eq, sub_zero] at h
    exact h
  have h0 : 0 ≤ ∫ p, F m p ∂Q := integral_nonneg fun p => hF0 m p
  rw [abs_of_nonneg measureReal_nonneg] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- **Lemma A.1 of Gwynne–Miller–Sheffield for the zero-cone field jointly with the space-filling SLE** (written
answer `notes/fp-gaps/CODEX-MQ-sbl-25.md`, "(c) Joint invariance", lines 33-45). Let `V = G'` be bounded, measurable
and jointly invariant. With the random similarities `T_m(w) = z_m + C_m w` of Lemma A.4 (`ZeroConeLemmaA4`), which
preserve the law of the zero-cone field and have `|z_m| → ∞` in probability, the scale and translation invariance of
the law of the curve (`SpaceFillingSLESimilarityLaw`) and the mixing of the curve at distant centres (which comes
from `IGFieldDistantCentreMixing` through the curve map of the coupling), `V(h, e)` is almost surely its partial
mean `v(h) = ∫ V(h, e) ν(de)` (`ae_eq_integral_of_jointInvariance`). The partial mean is invariant under every
coordinate change of the field, hence almost surely constant by Lemma A.1 for the field alone
(`ZeroConeCircleAverageLemmaA1`); the zero-cone field is independent of the curve, so `V(h₀, ηL)` is almost surely
that constant. -/
theorem zeroConeJointLemmaA1 (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA1 : ZeroConeCircleAverageLemmaA1 γ hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hmix : IGFieldDistantCentreMixing γ hγ)
    (hA4 : ZeroConeLemmaA4 γ hγ) : ZeroConeJointLemmaA1 D hγ := by
  intro G' hG'm hbd hinv
  obtain ⟨M, hM⟩ := hbd
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H', hH'm, hH'ind, hH'eq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hηm : Measurable ηL := D.measurable_curves.1
  have hνP : IsProbabilityMeasure (P.map ηL) :=
    (Measure.isProbabilityMeasure_map_iff hηm.aemeasurable).2 inferInstance
  have hh₀ : AEMeasurable (zeroConeFieldOf γ X₀ B₀ B₀') P := hH'm.aemeasurable.congr hH'eq
  have hμP : IsProbabilityMeasure (P.map (zeroConeFieldOf γ X₀ B₀ B₀')) :=
    (Measure.isProbabilityMeasure_map_iff hh₀).2 inferInstance
  obtain ⟨E, mE, κ, hκ, C, z, hCm, hzm, hCpos, hlawA4, hfar⟩ := hA4 P X₀ B₀ B₀'
    D.isProbabilityMeasure D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.1 D.indep_cone₀.2
  -- the law of the curve is invariant under the similarities
  have hρlaw : ∀ t ∈ {t : ℝ × ℂ | 0 < t.1},
      (P.map ηL).map (affineReroot t.2 t.1 0) = P.map ηL := by
    intro t ht
    rw [Measure.map_map (measurable_affineReroot t.2 t.1) hηm, Function.comp_def]
    exact (hlaw t.1 ht t.2).map_eq
  -- the curve mixes along the random similarities
  have hmixcore : ∀ B' B : Set C(ℝ, ℂ), MeasurableSet B' → MeasurableSet B →
      Tendsto (fun m => ∫ p, |(P.map ηL).real (B' ∩ affineReroot (z m p) (C m p) 0 ⁻¹' B) -
        (P.map ηL).real B' * (P.map ηL).real B| ∂((P.map (zeroConeFieldOf γ X₀ B₀ B₀')).prod κ))
        atTop (𝓝 0) := by
    intro B' B hB' hB
    refine tendsto_integral_of_uniform_of_tendsto_measure_norm_le hzm (fun m p => abs_nonneg _)
      (fun m p => ?_) (fun ε hε => ?_) hfar
    · have ha0 : 0 ≤ (P.map ηL).real (B' ∩ affineReroot (z m p) (C m p) 0 ⁻¹' B) := measureReal_nonneg
      have ha1 : (P.map ηL).real (B' ∩ affineReroot (z m p) (C m p) 0 ⁻¹' B) ≤ 1 :=
        toReal_measure_le_one _ _
      have hb0 : 0 ≤ (P.map ηL).real B' := measureReal_nonneg
      have hb1 : (P.map ηL).real B' ≤ 1 := toReal_measure_le_one _ _
      have hc0 : 0 ≤ (P.map ηL).real B := measureReal_nonneg
      have hbc0 : 0 ≤ (P.map ηL).real B' * (P.map ηL).real B := mul_nonneg hb0 hc0
      have hbc1 : (P.map ηL).real B' * (P.map ηL).real B ≤ (P.map ηL).real B :=
        mul_le_of_le_one_left hc0 hb1
      have hc1 : (P.map ηL).real B ≤ 1 := toReal_measure_le_one _ _
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · obtain ⟨R, hR⟩ := exists_uniform_igCurve_affineReroot_correlation D hγ hmix hB' hB hε
      exact ⟨R, fun m p hp => hR (z m p) (C m p) (hCpos m p) hp⟩
  -- the random similarities preserve the law of the field
  have hσlaw : ∀ m, ((P.map (zeroConeFieldOf γ X₀ B₀ B₀')).prod κ).map
      (fun p => lqgSimilarityAction γ (C m p, z m p) p.1) = P.map (zeroConeFieldOf γ X₀ B₀ B₀') := by
    intro m
    have e : (fun p : Field × E => lqgSimilarityAction γ (C m p, z m p) p.1) =
        fun p => lqgSimilarityField γ (C m p) (z m p) p.1 :=
      funext fun p => lqgSimilarityAction_of_pos γ (t := (C m p, z m p)) (hCpos m p) p.1
    rw [e]
    exact hlawA4 m
  have hinvcore : ∀ᵐ a ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL,
      ∀ t ∈ {t : ℝ × ℂ | 0 < t.1},
        G' (lqgSimilarityAction γ t a, affineReroot t.2 t.1 0 e) = G' (a, e) := by
    filter_upwards [hinv] with a ha
    filter_upwards [ha] with e he t ht
    rw [lqgSimilarityAction_of_pos γ ht]
    exact he t.1 ht t.2
  -- `G'` is almost surely its partial mean
  have hcore := ae_eq_integral_of_jointInvariance (σ := lqgSimilarityAction γ)
    (ρ := fun t : ℝ × ℂ => affineReroot t.2 t.1 0) (T₀ := {t : ℝ × ℂ | 0 < t.1})
    (τ := fun m p => (C m p, z m p)) (measurable_lqgSimilarityAction γ) measurable_affineReroot_joint
    (fun m => (hCm m).prodMk (hzm m)) (fun m p => hCpos m p) hσlaw hρlaw hmixcore hG'm hM hinvcore
  obtain ⟨v, hv_def⟩ : ∃ v : Field → ℝ, v = fun a => ∫ e, G' (a, e) ∂(P.map ηL) := ⟨_, rfl⟩
  have hvm : Measurable v := by
    rw [hv_def]
    exact hG'm.stronglyMeasurable.integral_prod_right'.measurable
  have hvb : ∀ a, |v a| ≤ M := by
    intro a
    rw [hv_def]
    exact abs_integral_le_of_forall_abs_le_of_isProbabilityMeasure fun e => hM _
  -- the partial mean is invariant under the coordinate changes of the field
  have hvinv : ∀ᵐ a ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ C' : ℝ, 0 < C' → ∀ z' : ℂ,
      v (lqgSimilarityField γ C' z' a) = v a := by
    filter_upwards [hinv] with a ha C' hC' z'
    have hl : (P.map ηL).map (affineReroot z' C' 0) = P.map ηL := hρlaw (C', z') hC'
    rw [hv_def]
    calc ∫ e, G' (lqgSimilarityField γ C' z' a, e) ∂(P.map ηL)
        = ∫ e, G' (lqgSimilarityField γ C' z' a, e) ∂((P.map ηL).map (affineReroot z' C' 0)) := by
          rw [hl]
      _ = ∫ e, G' (lqgSimilarityField γ C' z' a, affineReroot z' C' 0 e) ∂(P.map ηL) :=
          integral_map (measurable_affineReroot z' C').aemeasurable
            (hG'm.comp measurable_prodMk_left).aestronglyMeasurable
      _ = ∫ e, G' (a, e) ∂(P.map ηL) := by
          refine integral_congr_ae ?_
          filter_upwards [ha] with e he
          exact he C' hC' z'
  -- Lemma A.1 for the field alone
  obtain ⟨F, hF_def⟩ : ∃ F : Field → ℝ, F = fun a => v a + M := ⟨_, rfl⟩
  have hFa : ∀ a, F a = v a + M := fun a => by rw [hF_def]
  have hFm : Measurable F := by
    rw [hF_def]
    exact hvm.add_const M
  have hFinv : ∀ᵐ ω ∂P, ∀ C' : ℝ, 0 < C' → ∀ z' : ℂ,
      F (lqgSimilarityField γ C' z' (zeroConeFieldOf γ X₀ B₀ B₀' ω)) = F (zeroConeFieldOf γ X₀ B₀ B₀' ω) :=
    (ae_of_ae_map hh₀ hvinv).mono fun ω hω C' hC' z' => by rw [hFa, hFa, hω C' hC' z']
  obtain ⟨c', hc'⟩ := hA1 P X₀ B₀ B₀' D.isProbabilityMeasure D.gff₀ D.bm_B₀ D.bm_B₀'
    D.indep_cone₀.1 D.indep_cone₀.2 F hFm
    ⟨M + M, fun a => by rw [hFa a]; linarith [(abs_le.1 (hvb a)).2]⟩
    (fun a => by rw [hFa a]; linarith [(abs_le.1 (hvb a)).1]) hFinv
  refine ⟨c' - M, ?_⟩
  have hvc : ∀ᵐ a ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), v a = c' - M := by
    have hFc : ∀ᵐ a ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), F a = c' :=
      (ae_map_iff hh₀ (measurableSet_eq_fun hFm measurable_const)).2 hc'
    filter_upwards [hFc] with a ha
    rw [hFa] at ha
    linarith
  -- the field is independent of the curve
  have hjoint : P.map (fun ω => (H' ω, ηL ω)) =
      (P.map (zeroConeFieldOf γ X₀ B₀ B₀')).prod (P.map ηL) := by
    rw [← Measure.map_congr hH'eq]
    exact (indepFun_iff_map_prod_eq_prod_map_map hH'm.aemeasurable hηm.aemeasurable).1 hH'ind
  have hprod : ∀ᵐ y ∂(P.map (zeroConeFieldOf γ X₀ B₀ B₀')).prod (P.map ηL), G' y = c' - M := by
    filter_upwards [hcore, Measure.quasiMeasurePreserving_fst.ae hvc] with y h1 h2
    rw [h1]
    rw [hv_def] at h2
    exact h2
  rw [← hjoint] at hprod
  have hω := ae_of_ae_map (hH'm.prodMk hηm).aemeasurable hprod
  filter_upwards [hω, hH'eq] with ω h1 h2
  rw [← h2]
  exact h1

end Similarity

end MatedCRT
