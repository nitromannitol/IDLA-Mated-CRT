import MatedCRT.FirstPass.Derived.ZeroConeCurveFactorProof
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1PosProof

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
(`ae_eq_integral_of_jointInvariance`).
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

end MatedCRT
