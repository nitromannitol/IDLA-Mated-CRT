import MatedCRT.FirstPass.SLERef.CanonicalModel

/-!
# Scale invariance at the canonical space-filling SLE model

For the canonical model `canonicalSLEModel ν` (null-robust, read through the rational-time code of a Lebesgue-area
representative), the scale-invariance field `SLEScaleInvarianceInput` follows from a property of the family `ν`
alone, `SLECodeScaleInvariant ν`: a random continuous path whose code has law `ν κ` keeps that code law after the
area-preserving rescaling `s ↦ r c (s / r ^ 2)` (`scaleCurve r c`).

The proof replaces a curve `η` with representative `ηL` by `R η` with representative `scaleCurve R ηL`. The area of
`r E` is `r ^ 2` times the area of `E`, so `scaleCurve r` preserves free Lebesgue-area representatives
(`scaleCurve_rep`). The code of `scaleCurve R ηL` is a jointly measurable function `codeScale` of `(R, code of ηL)`:
`codeEval` reads a code back at real times through rational approximations from below, `ratApprox`. Independence of
the code from `𝓕` and `𝓕`-measurability of `R` then give the law and the independence of the new code by Fubini.
-/

namespace MatedCRT.ProbeMi
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Pointwise

/-- The curve `r c` reparametrized by Lebesgue area: `s ↦ r * c (s / r ^ 2)`. -/
noncomputable def scaleCurve (r : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun s => (r : ℂ) * c (s / r ^ 2), by fun_prop⟩

@[simp] lemma scaleCurve_apply (r : ℝ) (c : C(ℝ, ℂ)) (s : ℝ) :
    scaleCurve r c s = (r : ℂ) * c (s / r ^ 2) := rfl

lemma image_scaleCurve_Icc {r : ℝ} (hr : 0 < r) (c : C(ℝ, ℂ)) (s t : ℝ) :
    scaleCurve r c '' Set.Icc s t = r • (c '' Set.Icc (s / r ^ 2) (t / r ^ 2)) := by
  have h2 : (0:ℝ) < r ^ 2 := by positivity
  have hI : (fun x : ℝ => x / r ^ 2) '' Set.Icc s t = Set.Icc (s / r ^ 2) (t / r ^ 2) := by
    simp only [div_eq_mul_inv]
    exact Set.image_mul_right_Icc' s t (inv_pos.mpr h2)
  rw [← hI, ← Set.image_smul, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp [Complex.real_smul]

/-- Scaling by `r > 0` preserves the free Lebesgue-area representative property: if `c` is a free Lebesgue-area
representative of `η`, then `scaleCurve r c` is one of `r η`. -/
theorem scaleCurve_rep {η : ℝ → ℂ} {c : C(ℝ, ℂ)} {r : ℝ} (hr : 0 < r)
    (h : IsLebesgueRepresentativeFree η c) :
    IsLebesgueRepresentativeFree (fun s => (r : ℂ) * η s) (scaleCurve r c) := by
  obtain ⟨c0, csurj, cprop, cvol, φ, hφ⟩ := h
  have h2 : (0:ℝ) < r ^ 2 := by positivity
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨by simp [c0], ?_, ?_, ?_, φ.trans (OrderIso.mulLeft₀ (r ^ 2) h2), ?_⟩
  · intro z
    obtain ⟨t, ht⟩ := csurj (z / r)
    refine ⟨t * r ^ 2, ?_⟩
    rw [scaleCurve_apply, mul_div_cancel_right₀ t h2.ne', ht]
    field_simp
  · have h1 : Tendsto (fun s : ℝ => s / r ^ 2) (cocompact ℝ) (cocompact ℝ) := by
      have := (Homeomorph.mulRight₀ ((r ^ 2)⁻¹) (inv_ne_zero h2.ne')).isClosedEmbedding.tendsto_cocompact
      simpa [div_eq_mul_inv] using this
    have h3 : Tendsto (fun z : ℂ => (r : ℂ) * z) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.mulLeft₀ (r : ℂ) hrC).isClosedEmbedding.tendsto_cocompact
    exact h3.comp (cprop.comp h1)
  · intro s t hst
    rw [image_scaleCurve_Icc hr, Measure.addHaar_smul, Complex.finrank_real_complex,
      cvol _ _ (by gcongr), ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos h2]
    congr 1
    field_simp
  · intro t
    simp only [scaleCurve_apply, OrderIso.trans_apply, OrderIso.mulLeft₀_apply, hφ]
    rw [mul_div_cancel_left₀ _ h2.ne']

/-- Rational approximation of `t` from below at mesh `1 / (n + 1)`. -/
noncomputable def ratApprox (n : ℕ) (t : ℝ) : ℚ := (⌊((n : ℝ) + 1) * t⌋ : ℚ) / ((n : ℚ) + 1)

lemma measurable_ratApprox (n : ℕ) : Measurable (ratApprox n) := by
  have : ratApprox n = (fun k : ℤ => (k : ℚ) / ((n : ℚ) + 1)) ∘ (fun t : ℝ => ⌊((n : ℝ) + 1) * t⌋) := rfl
  rw [this]
  exact (measurable_of_countable _).comp ((measurable_const.mul measurable_id).floor)

lemma tendsto_ratApprox (t : ℝ) : Tendsto (fun n => ((ratApprox n t : ℚ) : ℝ)) atTop (𝓝 t) := by
  have key : ∀ n : ℕ, ((ratApprox n t : ℚ) : ℝ) = (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1) := by
    intro n; simp [ratApprox]
  simp_rw [key]
  have hn : ∀ n : ℕ, (0:ℝ) < (n : ℝ) + 1 := fun n => by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => t - 1 / ((n : ℝ) + 1))
    (h := fun _ => t) ?_ tendsto_const_nhds ?_ ?_
  · have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := t)).sub h0
  · intro n
    have h1 := Int.lt_floor_add_one (((n : ℝ) + 1) * t)
    rw [le_div_iff₀ (hn n), sub_mul, one_div, inv_mul_cancel₀ (hn n).ne']
    linarith
  · intro n
    have h1 := Int.floor_le (((n : ℝ) + 1) * t)
    rw [div_le_iff₀ (hn n)]
    linarith

/-- Continuous extension of a rational-time code, read off by limsups (junk off continuous codes). -/
noncomputable def codeEval (x : SLEPathCode) (t : ℝ) : ℂ :=
  ((limsup (fun n => (x (ratApprox n t)).re) atTop : ℝ) : ℂ) +
    ((limsup (fun n => (x (ratApprox n t)).im) atTop : ℝ) : ℂ) * Complex.I

lemma codeEval_slePathCode (c : C(ℝ, ℂ)) (t : ℝ) : codeEval (slePathCode c) t = c t := by
  have hc : Tendsto (fun n => c ((ratApprox n t : ℚ) : ℝ)) atTop (𝓝 (c t)) :=
    (c.continuous.tendsto t).comp (tendsto_ratApprox t)
  have hre : Tendsto (fun n => (c ((ratApprox n t : ℚ) : ℝ)).re) atTop (𝓝 (c t).re) :=
    (Complex.continuous_re.tendsto _).comp hc
  have him : Tendsto (fun n => (c ((ratApprox n t : ℚ) : ℝ)).im) atTop (𝓝 (c t).im) :=
    (Complex.continuous_im.tendsto _).comp hc
  simp only [codeEval, slePathCode]
  rw [hre.limsup_eq, him.limsup_eq]
  exact Complex.re_add_im (c t)

lemma measurable_codeEval : Measurable (fun p : SLEPathCode × ℝ => codeEval p.1 p.2) := by
  have hev : Measurable (fun p : SLEPathCode × ℚ => p.1 p.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  have hn : ∀ n, Measurable (fun p : SLEPathCode × ℝ => p.1 (ratApprox n p.2)) := fun n =>
    hev.comp (measurable_fst.prodMk ((measurable_ratApprox n).comp measurable_snd))
  have hre : Measurable (fun p : SLEPathCode × ℝ => limsup (fun n => (p.1 (ratApprox n p.2)).re) atTop) :=
    Measurable.limsup fun n => Complex.measurable_re.comp (hn n)
  have him : Measurable (fun p : SLEPathCode × ℝ => limsup (fun n => (p.1 (ratApprox n p.2)).im) atTop) :=
    Measurable.limsup fun n => Complex.measurable_im.comp (hn n)
  exact (Complex.measurable_ofReal.comp hre).add ((Complex.measurable_ofReal.comp him).mul_const _)

/-- Jointly measurable rescaling of codes. -/
noncomputable def codeScale (p : ℝ × SLEPathCode) : SLEPathCode :=
  fun q => (p.1 : ℂ) * codeEval p.2 ((q : ℝ) / p.1 ^ 2)

lemma codeScale_apply (p : ℝ × SLEPathCode) (q : ℚ) :
    codeScale p q = (p.1 : ℂ) * codeEval p.2 ((q : ℝ) / p.1 ^ 2) := rfl

lemma measurable_codeScale_coord (q : ℚ) :
    Measurable fun p : ℝ × SLEPathCode => (p.1 : ℂ) * codeEval p.2 ((q : ℝ) / p.1 ^ 2) := by
  have h0 : Measurable fun p : ℝ × SLEPathCode => (q : ℝ) / p.1 ^ 2 :=
    (measurable_fst.pow_const 2).const_div (q : ℝ)
  have hpair : Measurable fun p : ℝ × SLEPathCode => (p.2, (q : ℝ) / p.1 ^ 2) :=
    measurable_snd.prodMk h0
  have h2 := measurable_codeEval.comp hpair
  simp only [Function.comp_def] at h2
  have h1 : Measurable fun p : ℝ × SLEPathCode => (p.1 : ℂ) :=
    Complex.measurable_ofReal.comp measurable_fst
  exact h1.mul h2

lemma measurable_codeScale : Measurable codeScale :=
  measurable_pi_iff.2 fun q => measurable_codeScale_coord q

lemma codeScale_slePathCode (r : ℝ) (c : C(ℝ, ℂ)) :
    codeScale (r, slePathCode c) = slePathCode (scaleCurve r c) := by
  funext q
  show (r : ℂ) * codeEval (slePathCode c) ((q : ℝ) / r ^ 2) = (r : ℂ) * c ((q : ℝ) / r ^ 2)
  rw [codeEval_slePathCode]

/-- **Scale invariance of the code law** of a family `ν` of whole-plane space-filling SLE laws, read on continuous
representatives: whenever a random continuous path `ηL` has code law `ν κ` (`4 < κ`), so has its area-preserving
rescaling `scaleCurve r ηL`, `s ↦ r ηL (s / r ^ 2)`, for every `r > 0`.

This is a hypothesis on `ν`. Its motivation is the scale invariance of whole-plane space-filling SLE modulo time
parametrization (Miller-Sheffield, *Imaginary Geometry IV*, Sections 1.2.3 and 4.3; Duplantier-Miller-Sheffield,
*Liouville quantum gravity as a mating of trees*, Section 1.4.1, and the proof of Lemma 9.7 there), together with
`Lebesgue (r E) = r ^ 2 Lebesgue (E)`, which makes `scaleCurve r ηL` the Lebesgue-area parametrization of `r ηL`
anchored at the spatial point `0`. -/
def SLECodeScaleInvariant (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (κ r : ℝ) (ηL : Ω → C(ℝ, ℂ)),
    IsProbabilityMeasure P → 4 < κ → 0 < r →
    @Measurable Ω SLEPathCode mΩ _ (fun ω => slePathCode (ηL ω)) →
    @Measure.map Ω SLEPathCode mΩ _ (fun ω => slePathCode (ηL ω)) P = ν κ →
    @Measure.map Ω SLEPathCode mΩ _ (fun ω => slePathCode (scaleCurve r (ηL ω))) P = ν κ

/-- **Scale invariance at the canonical model**: if the family `ν` is scale invariant on codes
(`SLECodeScaleInvariant ν`), then `canonicalSLEModel ν` satisfies `SLEScaleInvarianceInput`: for a positive
`𝓕`-measurable factor `R`, the curve `R η` is again a whole-plane space-filling SLE_κ independent of `𝓕`, with
representative `scaleCurve R ηL`. -/
theorem canonicalSLEModel_scale (ν : ℝ → Measure SLEPathCode) (hSC : SLECodeScaleInvariant ν) :
    SLEScaleInvarianceInput (canonicalSLEModel ν) := by
  intro Ω mΩ P 𝓕 κ η hκ h R hR hRpos
  obtain ⟨hP, h𝓕, ηL, hm, hrep, hlaw, hind⟩ := h
  have hRm : Measurable[mΩ] R := hR.mono h𝓕 le_rfl
  let _inst : MeasurableSpace Ω := mΩ
  have hX' : (fun ω => slePathCode (scaleCurve (R ω) (ηL ω))) =
      fun ω => codeScale (R ω, slePathCode (ηL ω)) := by
    funext ω; exact (codeScale_slePathCode _ _).symm
  have hX'm : Measurable[mΩ] (fun ω => slePathCode (scaleCurve (R ω) (ηL ω))) := by
    rw [hX']; exact measurable_codeScale.comp (hRm.prodMk hm)
  have hcs : ∀ r : ℝ, Measurable (fun x : SLEPathCode => codeScale (r, x)) := fun r =>
    measurable_codeScale.comp (measurable_const.prodMk measurable_id)
  have hinv : ∀ r : ℝ, 0 < r → (ν κ).map (fun x => codeScale (r, x)) = ν κ := by
    intro r hr
    have h1 := hSC Ω mΩ P κ r ηL hP hκ hr hm hlaw
    calc (ν κ).map (fun x => codeScale (r, x))
        = P.map ((fun x => codeScale (r, x)) ∘ fun ω => slePathCode (ηL ω)) := by
          rw [← hlaw, Measure.map_map (hcs r) hm]
      _ = P.map (fun ω => slePathCode (scaleCurve r (ηL ω))) := by
          congr 1; funext ω; exact codeScale_slePathCode _ _
      _ = ν κ := h1
  have : IsProbabilityMeasure (ν κ) := by
    rw [← hlaw]; exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 hP
  have key : ∀ (A : Set Ω) (B : Set SLEPathCode), MeasurableSet[𝓕] A → MeasurableSet B →
      P (A ∩ (fun ω => slePathCode (scaleCurve (R ω) (ηL ω))) ⁻¹' B) = P A * ν κ B := by
    intro A B hA hB
    have hAm : MeasurableSet[mΩ] A := h𝓕 _ hA
    let Y : Ω → ℝ × ℝ := fun ω => (R ω, A.indicator (fun _ => (1:ℝ)) ω)
    have hYF : Measurable[𝓕] Y := hR.prodMk (measurable_const.indicator hA)
    have hYm : Measurable[mΩ] Y := hYF.mono h𝓕 le_rfl
    have hindYX : IndepFun Y (fun ω => slePathCode (ηL ω)) P := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le_right hind hYF.comap_le).symm
    have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hm.aemeasurable).1 hindYX
    rw [hlaw] at hjoint
    let S : Set ((ℝ × ℝ) × SLEPathCode) := {p | p.1.2 = 1 ∧ codeScale (p.1.1, p.2) ∈ B}
    have hS : MeasurableSet S :=
      ((measurableSet_singleton (1:ℝ)).preimage (measurable_snd.comp measurable_fst)).inter
        (hB.preimage (measurable_codeScale.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    have hpre : A ∩ (fun ω => slePathCode (scaleCurve (R ω) (ηL ω))) ⁻¹' B =
        (fun ω => (Y ω, slePathCode (ηL ω))) ⁻¹' S := by
      rw [hX']
      ext ω
      by_cases hω : ω ∈ A <;> simp [Y, S, hω]
    rw [hpre, ← Measure.map_apply (hYm.prodMk hm) hS, hjoint, Measure.prod_apply hS,
      lintegral_map (measurable_measure_prodMk_left hS) hYm]
    have hpt : ∀ ω, ν κ (Prod.mk (Y ω) ⁻¹' S) = A.indicator (fun _ => ν κ B) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · have h1 : Prod.mk (Y ω) ⁻¹' S = (fun x => codeScale (R ω, x)) ⁻¹' B := by
          ext x; simp [Y, S, hω]
        rw [h1, Set.indicator_of_mem hω, ← Measure.map_apply (hcs _) hB, hinv _ (hRpos ω)]
      · have h1 : Prod.mk (Y ω) ⁻¹' S = ∅ := by
          ext x; simp [Y, S, hω]
        rw [h1]; simp [hω]
    simp_rw [hpt]
    rw [lintegral_indicator_const hAm, mul_comm]
  have hall : ∀ B : Set SLEPathCode, MeasurableSet B →
      P ((fun ω => slePathCode (scaleCurve (R ω) (ηL ω))) ⁻¹' B) = ν κ B := by
    intro B hB
    simpa using key Set.univ B MeasurableSet.univ hB
  refine ⟨hP, h𝓕, fun ω => scaleCurve (R ω) (ηL ω), hX'm, ?_, ?_, ?_⟩
  · filter_upwards [hrep] with ω hω using scaleCurve_rep (hRpos ω) hω
  · ext B hB
    rw [Measure.map_apply hX'm hB, hall B hB]
  · rw [Indep_iff]
    rintro t1 t2 ⟨B, hB, rfl⟩ ht2
    rw [Set.inter_comm, key t2 B ht2 hB, hall B hB, mul_comm]

end MatedCRT.ProbeMi
