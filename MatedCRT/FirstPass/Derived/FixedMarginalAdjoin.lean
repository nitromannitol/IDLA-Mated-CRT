import Mathlib
import LatticeProb.Prob.ContinuousMappingAECont

/-!
# Joint convergence in law with a Borel function of a coordinate of fixed law

Let `ν n` and `ν₀` be Borel probability measures on a product `X × K` whose first marginals are all the same
measure `μ`, and assume `ν n → ν₀` weakly. For a Borel map `F : X → Y` into a second countable space, the laws of
`(q, F q.1)` under `ν n` converge weakly to the law of `(q, F q.1)` under `ν₀`: the coordinate `F q.1` may be adjoined
to a joint convergence in law although `F` is not continuous, because its argument has the same law at every stage.

* `MatedCRT.exists_isClosed_measure_compl_lt_continuousOn`: **Lusin's theorem**. For a finite measure that is inner
  regular for closed sets and a Borel map `F` into a second countable space, there are closed sets of almost full
  measure on which `F` is continuous.
* `MatedCRT.tendsto_integral_comp_prodMk_of_map_fst_eq`: the adjoined joint convergence. On a closed set `fst⁻¹ C`
  of almost full measure, `q ↦ f (q, F q.1)` is continuous; a bounded continuous extension (Tietze) has integrals
  converging under `ν n → ν₀`, and its integrals differ from those of `q ↦ f (q, F q.1)` by at most
  `2 ‖f‖ μ(Cᶜ)` under every measure with first marginal `μ`.
* `MatedCRT.tendsto_integral_comp_prodMk_of_ae_continuousAt`: with the continuous mapping theorem for a bounded
  Borel function continuous almost everywhere (`LatticeProb.tendsto_integral_of_ae_continuousAt`), the integrals of
  `Γ (q, F q.1)` converge whenever `Γ` is continuous at `(q, F q.1)` for `ν₀`-almost every `q`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

section Lusin

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]

/-- **Lusin's theorem.** For a finite measure `μ` that is inner regular for closed sets (`WeaklyRegular`) and a Borel
map `F` into a second countable space, for every `ε > 0` there is a closed set `C` with `μ Cᶜ < ε` on which `F` is
continuous. For each basic open set `V` choose closed sets inside `F⁻¹ V` and inside its complement which exhaust them
up to `δ V`, with `∑ δ V < ε / 2`; on the intersection `C` of their unions, `F⁻¹ V ∩ C` is relatively open. -/
theorem exists_isClosed_measure_compl_lt_continuousOn (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {F : X → Y} (hF : Measurable F) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set X, IsClosed C ∧ μ Cᶜ < ε ∧ ContinuousOn F C := by
  classical
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis Y
  have : Countable B := hBc.to_subtype
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε).ne' B
  have hin : ∀ V : B, ∃ C ⊆ F ⁻¹' (V : Set Y), IsClosed C ∧ μ (F ⁻¹' (V : Set Y) \ C) < δ V := fun V =>
    (hF (hB.isOpen V.2).measurableSet).exists_isClosed_sdiff_lt (measure_ne_top μ _)
      (ENNReal.coe_ne_zero.2 (hδpos V).ne')
  have hout : ∀ V : B, ∃ D ⊆ (F ⁻¹' (V : Set Y))ᶜ, IsClosed D ∧
      μ ((F ⁻¹' (V : Set Y))ᶜ \ D) < δ V := fun V =>
    (hF (hB.isOpen V.2).measurableSet).compl.exists_isClosed_sdiff_lt (measure_ne_top μ _)
      (ENNReal.coe_ne_zero.2 (hδpos V).ne')
  choose Cin hCin hCinc hCinμ using hin
  choose Dout hDout hDoutc hDoutμ using hout
  refine ⟨⋂ V : B, (Cin V ∪ Dout V), isClosed_iInter fun V => (hCinc V).union (hDoutc V), ?_, ?_⟩
  · have hsub : ∀ V : B, (Cin V ∪ Dout V)ᶜ ⊆
        (F ⁻¹' (V : Set Y) \ Cin V) ∪ ((F ⁻¹' (V : Set Y))ᶜ \ Dout V) := by
      intro V x hx
      rw [compl_union] at hx
      by_cases h : x ∈ F ⁻¹' (V : Set Y)
      · exact Or.inl ⟨h, hx.1⟩
      · exact Or.inr ⟨h, hx.2⟩
    calc μ (⋂ V : B, (Cin V ∪ Dout V))ᶜ = μ (⋃ V : B, (Cin V ∪ Dout V)ᶜ) := by rw [compl_iInter]
      _ ≤ ∑' V : B, μ (Cin V ∪ Dout V)ᶜ := measure_iUnion_le _
      _ ≤ ∑' V : B, ((δ V : ℝ≥0∞) + δ V) := ENNReal.tsum_le_tsum fun V =>
          (measure_mono (hsub V)).trans ((measure_union_le _ _).trans
            (add_le_add (hCinμ V).le (hDoutμ V).le))
      _ = ∑' V : B, (δ V : ℝ≥0∞) + ∑' V : B, (δ V : ℝ≥0∞) := ENNReal.tsum_add
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hδsum hδsum
      _ = ε := ENNReal.add_halves ε
  · rw [continuousOn_iff']
    intro t ht
    refine ⟨⋃ (V : B) (_ : (V : Set Y) ⊆ t), (Dout V)ᶜ,
      isOpen_iUnion fun V => isOpen_iUnion fun _ => (hDoutc V).isOpen_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_iInter, mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨hxt, hxC⟩
      obtain ⟨V, hVB, hxV, hVt⟩ := hB.exists_subset_of_mem_open hxt ht
      exact ⟨⟨⟨V, hVB⟩, hVt, fun hD => hDout ⟨V, hVB⟩ hD hxV⟩, hxC⟩
    · rintro ⟨⟨V, hVt, hxD⟩, hxC⟩
      refine ⟨hVt ?_, hxC⟩
      rcases hxC V with h | h
      · exact hCin V h
      · exact absurd h hxD

end Lusin

section Adjoin

variable {X K Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- **Joint convergence with a Borel function of a coordinate of fixed law.** Let `ν n → ν₀` weakly on `X × K`, all
with the same first marginal `μ` (inner regular for closed sets), and let `F : X → Y` be Borel. Then for every
bounded continuous `f` on `(X × K) × Y`, `∫ f (q, F q.1) dν n → ∫ f (q, F q.1) dν₀`. -/
theorem tendsto_integral_comp_prodMk_of_map_fst_eq [NormalSpace (X × K)]
    {ν : ℕ → Measure (X × K)} [∀ n, IsProbabilityMeasure (ν n)] {ν₀ : Measure (X × K)} [IsProbabilityMeasure ν₀]
    {μ : Measure X} [μ.WeaklyRegular] (hν : ∀ n, (ν n).map Prod.fst = μ) (hν₀ : ν₀.map Prod.fst = μ)
    (hconv : ∀ f : (X × K) →ᵇ ℝ, Tendsto (fun n => ∫ q, f q ∂ν n) atTop (𝓝 (∫ q, f q ∂ν₀)))
    {F : X → Y} (hF : Measurable F) (f : ((X × K) × Y) →ᵇ ℝ) :
    Tendsto (fun n => ∫ q, f (q, F q.1) ∂ν n) atTop (𝓝 (∫ q, f (q, F q.1) ∂ν₀)) := by
  classical
  have hμ : IsProbabilityMeasure μ := by
    rw [← hν₀]
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  set g : X × K → ℝ := fun q => f (q, F q.1) with hg
  have hgm : Measurable g := f.continuous.measurable.comp (measurable_id.prodMk (hF.comp measurable_fst))
  set M : ℝ := ‖f‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg f
  have hgM : ∀ q, |g q| ≤ M := fun q => by
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hM8 : (8 : ℝ) * (M + 1) ≠ 0 := by positivity
  set η : ℝ := δ / (8 * (M + 1)) with hηdef
  have hη : 0 < η := div_pos hδ (by positivity)
  have hη8 : η * (8 * (M + 1)) = δ := div_mul_cancel₀ δ hM8
  obtain ⟨C, hCc, hCμ, hFC⟩ :=
    exists_isClosed_measure_compl_lt_continuousOn μ hF (ENNReal.ofReal_pos.2 hη).ne'
  -- `g` is continuous on the closed set `fst⁻¹ C`
  set S : Set (X × K) := Prod.fst ⁻¹' C with hSdef
  have hSc : IsClosed S := hCc.preimage continuous_fst
  have hgS : ContinuousOn g S :=
    f.continuous.comp_continuousOn (continuousOn_id.prodMk (hFC.comp continuous_fst.continuousOn fun q hq => hq))
  -- a bounded continuous extension of `g` from `S`
  obtain ⟨g₀, hg₀⟩ := ContinuousMap.exists_restrict_eq hSc (⟨S.domRestrict g, hgS.domRestrict⟩ : C(S, ℝ))
  have hg₀S : ∀ q ∈ S, g₀ q = g q := fun q hq => DFunLike.congr_fun hg₀ ⟨q, hq⟩
  set g₁ : X × K → ℝ := fun q => max (-M) (min M (g₀ q)) with hg₁
  have hg₁c : Continuous g₁ := continuous_const.max (continuous_const.min g₀.continuous)
  have hg₁M : ∀ q, ‖g₁ q‖ ≤ M := fun q => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let G : (X × K) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g₁ hg₁c M hg₁M
  have hGS : ∀ q ∈ S, G q = g q := fun q hq => by
    show max (-M) (min M (g₀ q)) = g q
    rw [hg₀S q hq, min_eq_right (abs_le.1 (hgM q)).2, max_eq_right (abs_le.1 (hgM q)).1]
  have hGM : ∀ q, |G q| ≤ M := fun q => by
    rw [← Real.norm_eq_abs]
    exact hg₁M q
  -- the error of replacing `g` by `G` under a measure with first marginal `μ`
  have hbound : ∀ p : Measure (X × K), IsProbabilityMeasure p → p.map Prod.fst = μ →
      |∫ q, g q ∂p - ∫ q, G q ∂p| ≤ 2 * M * (μ Cᶜ).toReal := by
    intro p hp hpμ
    have hSm : MeasurableSet Sᶜ := hSc.isOpen_compl.measurableSet
    have hIg : Integrable g p := Integrable.of_bound hgm.aestronglyMeasurable M
      (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hgM q)
    have hIG : Integrable (fun q => G q) p := G.integrable p
    have hpS : p Sᶜ = μ Cᶜ := by
      rw [← hpμ, Measure.map_apply measurable_fst hCc.isOpen_compl.measurableSet]
      rfl
    rw [← integral_sub hIg hIG, ← Real.norm_eq_abs]
    calc ‖∫ q, (g q - G q) ∂p‖ ≤ ∫ q, ‖g q - G q‖ ∂p := norm_integral_le_integral_norm _
      _ ≤ ∫ q, Sᶜ.indicator (fun _ => 2 * M) q ∂p := by
          refine integral_mono (hIg.sub hIG).norm ((integrable_const _).indicator hSm) fun q => ?_
          by_cases hq : q ∈ S
          · rw [indicator_of_notMem (fun h : q ∈ Sᶜ => h hq), hGS q hq, sub_self, norm_zero]
          · rw [indicator_of_mem (show q ∈ Sᶜ from hq), Real.norm_eq_abs]
            obtain ⟨h1a, h1b⟩ := abs_le.1 (hgM q)
            obtain ⟨h2a, h2b⟩ := abs_le.1 (hGM q)
            exact abs_le.2 ⟨by linarith, by linarith⟩
      _ = 2 * M * (μ Cᶜ).toReal := by
          simp only [integral_indicator_const _ hSm, smul_eq_mul, measureReal_def, hpS]
          ring
  have ha0 : 0 ≤ (μ Cᶜ).toReal := ENNReal.toReal_nonneg
  have ha : (μ Cᶜ).toReal < η := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hCμ
    rwa [ENNReal.toReal_ofReal hη.le] at h
  have hMa : 2 * M * (μ Cᶜ).toReal ≤ δ / 4 := by
    nlinarith [mul_nonneg hM0 (sub_nonneg.2 ha.le)]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv G) (δ / 2) (half_pos hδ)
  refine ⟨N, fun n hn => ?_⟩
  have e1 := abs_le.1 ((hbound (ν n) inferInstance (hν n)).trans hMa)
  have e2 := abs_le.1 ((hbound ν₀ inferInstance hν₀).trans hMa)
  have e3 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  have e3' := abs_lt.1 e3
  rw [abs_lt]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3'.1, e3'.2]

variable [PseudoMetrizableSpace X] [PseudoMetrizableSpace K] [PseudoMetrizableSpace Y]

/-- **Integrals of an almost everywhere continuous function of the adjoined coordinate converge.** In the setting of
`tendsto_integral_comp_prodMk_of_map_fst_eq`, let `Γ` be a bounded Borel function on `(X × K) × Y`, continuous at
`(q, F q.1)` for `ν₀`-almost every `q`. Then `∫ Γ (q, F q.1) dν n → ∫ Γ (q, F q.1) dν₀`. -/
theorem tendsto_integral_comp_prodMk_of_ae_continuousAt [NormalSpace (X × K)]
    {ν : ℕ → Measure (X × K)} [∀ n, IsProbabilityMeasure (ν n)] {ν₀ : Measure (X × K)} [IsProbabilityMeasure ν₀]
    {μ : Measure X} [μ.WeaklyRegular] (hν : ∀ n, (ν n).map Prod.fst = μ) (hν₀ : ν₀.map Prod.fst = μ)
    (hconv : ∀ f : (X × K) →ᵇ ℝ, Tendsto (fun n => ∫ q, f q ∂ν n) atTop (𝓝 (∫ q, f q ∂ν₀)))
    {F : X → Y} (hF : Measurable F) {Γ : (X × K) × Y → ℝ} (hΓm : Measurable Γ) (hΓb : ∃ C, ∀ p, |Γ p| ≤ C)
    (hΓc : ∀ᵐ q ∂ν₀, ContinuousAt Γ (q, F q.1)) :
    Tendsto (fun n => ∫ q, Γ (q, F q.1) ∂ν n) atTop (𝓝 (∫ q, Γ (q, F q.1) ∂ν₀)) := by
  have hG : Measurable fun q : X × K => (q, F q.1) := measurable_id.prodMk (hF.comp measurable_fst)
  let μs : ℕ → ProbabilityMeasure ((X × K) × Y) := fun n =>
    ⟨(ν n).map fun q => (q, F q.1), (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance⟩
  let μ₀ : ProbabilityMeasure ((X × K) × Y) :=
    ⟨ν₀.map fun q => (q, F q.1), (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance⟩
  have hweak : Tendsto μs atTop (𝓝 μ₀) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
    have hmap : ∀ p : Measure (X × K), ∫ x, f x ∂(p.map fun q => (q, F q.1)) = ∫ q, f (q, F q.1) ∂p :=
      fun p => integral_map hG.aemeasurable f.continuous.aestronglyMeasurable
    show Tendsto (fun n => ∫ x, f x ∂((ν n).map fun q => (q, F q.1))) atTop
      (𝓝 (∫ x, f x ∂(ν₀.map fun q => (q, F q.1))))
    simp only [hmap]
    exact tendsto_integral_comp_prodMk_of_map_fst_eq hν hν₀ hconv hF f
  have hc : ∀ᵐ p ∂(μ₀ : Measure ((X × K) × Y)), ContinuousAt Γ p := by
    show ∀ᵐ p ∂(ν₀.map fun q => (q, F q.1)), ContinuousAt Γ p
    exact (ae_map_iff hG.aemeasurable (IsGδ.setOfPred_continuousAt Γ).measurableSet).2 hΓc
  have h : Tendsto (fun n => ∫ x, Γ x ∂((ν n).map fun q => (q, F q.1))) atTop
      (𝓝 (∫ x, Γ x ∂(ν₀.map fun q => (q, F q.1)))) :=
    LatticeProb.tendsto_integral_of_ae_continuousAt hweak hΓm hΓb hc
  have hmap : ∀ p : Measure (X × K), ∫ x, Γ x ∂(p.map fun q => (q, F q.1)) = ∫ q, Γ (q, F q.1) ∂p :=
    fun p => integral_map hG.aemeasurable hΓm.aestronglyMeasurable
  simpa only [hmap] using h

end Adjoin

end MatedCRT
