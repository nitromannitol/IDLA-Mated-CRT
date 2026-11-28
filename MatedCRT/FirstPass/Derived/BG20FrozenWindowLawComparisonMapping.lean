import MatedCRT.FirstPass.Derived.ChartStopPathContinuity

/-!
# The extended continuous mapping theorem for laws pushed forward from an auxiliary space

`MatedCRT.limsup_measure_preimage_le_of_ae_tendsto` (Billingsley, *Convergence of Probability Measures*, Theorem 5.5)
compares maps defined on the space `E` carrying the converging laws. In the comparison of the frozen and stopped window
walks (Berestycki–Gwynne (2020), proof of Lemma 7.21; the written argument) the maps are functions of
an auxiliary variable: the label sequence of a walk, whose interpolated planar path `I n x ∈ E` has the converging
laws, or the environment `ω`, whose (curve, kernel) data `I n ω` have the converging joint laws. The functionals `G n x`
are not functions of `I n x`. They are only required to converge along sequences `x l` on *good* sets of small measure
complement whose images `I (k l) (x l)` converge.

* `MatedCRT.ExtendedMapping.limsup_measure_preimage_le`: the closed-set inequality
  `limsup λ_n (G_n ∈ F) ≤ μ (f ∈ F)` (outer measures; no measurability of `G_n` or `f`).
* `MatedCRT.ExtendedMapping.tendsto_integral_comp`: the weak convergence of the image laws for measurable `G_n`, `f`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

namespace ExtendedMapping

variable {X E T : Type*} [MeasurableSpace X] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E] [TopologicalSpace T]

/-- **The closed-set half of the extended continuous mapping theorem through an auxiliary space.** Let `lam n` be
probability measures on `X`, `I n : X → E` almost everywhere measurable with images `μs n → μ` weakly, and let the good
sets `good n` have complements of measure tending to `0`. If for `μ`-almost every `e`, `G (k l) (x l) → f e` along
every sequence of levels `k l → ∞` and points `x l ∈ good (k l)` with `I (k l) (x l) → e`, then
`limsup lam n (G n ⁻¹' F) ≤ μ (f ⁻¹' F)` for every closed `F`. -/
theorem limsup_measure_preimage_le {lam : ℕ → Measure X} {I : ℕ → X → E} (hI : ∀ n, AEMeasurable (I n) (lam n))
    {μs : ℕ → ProbabilityMeasure E} (hμs : ∀ n, (μs n : Measure E) = (lam n).map (I n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ)) {good : ℕ → Set X}
    (hgood : Tendsto (fun n => lam n (good n)ᶜ) atTop (𝓝 0)) {G : ℕ → X → T} {f : E → T}
    (hc : ∀ᵐ e ∂(μ : Measure E), ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ l, x l ∈ good (k l)) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e)))
    {F : Set T} (hF : IsClosed F) :
    limsup (fun n => lam n (G n ⁻¹' F)) atTop ≤ (μ : Measure E) (f ⁻¹' F) := by
  set B : ℕ → Set E := fun N => closure (⋃ n ∈ Ici N, I n '' (good n ∩ G n ⁻¹' F))
  have hBclosed : ∀ N, IsClosed (B N) := fun N => isClosed_closure
  have hBanti : Antitone B := by
    intro N M hNM
    exact closure_mono (iUnion₂_subset fun n hn => subset_iUnion₂_of_subset n (le_trans hNM hn) le_rfl)
  -- one level of the closed sets
  have hstep : ∀ N, limsup (fun n => lam n (G n ⁻¹' F)) atTop ≤ (μ : Measure E) (B N) := by
    intro N
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.div_pos (ENNReal.coe_pos.2 hε).ne' (by norm_num)
    have h1 : ∀ᶠ n in atTop, lam n (good n)ᶜ ≤ (ε : ℝ≥0∞) / 2 := (ENNReal.tendsto_nhds_zero.1 hgood) _ hε2
    have hlim : limsup (fun n => (μs n : Measure E) (B N)) atTop < (μ : Measure E) (B N) + (ε : ℝ≥0∞) / 2 :=
      lt_of_le_of_lt (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hBclosed N))
        (ENNReal.lt_add_right (measure_ne_top _ _) hε2.ne')
    have h2 := eventually_lt_of_limsup_lt hlim
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [h1, h2, eventually_ge_atTop N] with n hn1 hn2 hn3
    have hsub : G n ⁻¹' F ⊆ (good n)ᶜ ∪ I n ⁻¹' B N := by
      intro x hx
      by_cases hg : x ∈ good n
      · right
        exact subset_closure (mem_iUnion₂.2 ⟨n, hn3, ⟨x, ⟨hg, hx⟩, rfl⟩⟩)
      · exact Or.inl hg
    have hmap : lam n (I n ⁻¹' B N) = (μs n : Measure E) (B N) := by
      rw [hμs n, Measure.map_apply_of_aemeasurable (hI n) (hBclosed N).measurableSet]
    calc lam n (G n ⁻¹' F) ≤ lam n ((good n)ᶜ ∪ I n ⁻¹' B N) := measure_mono hsub
      _ ≤ lam n (good n)ᶜ + lam n (I n ⁻¹' B N) := measure_union_le _ _
      _ ≤ (ε : ℝ≥0∞) / 2 + ((μ : Measure E) (B N) + (ε : ℝ≥0∞) / 2) := by
          rw [hmap]
          exact add_le_add hn1 hn2.le
      _ = (μ : Measure E) (B N) + ε := by
          rw [add_comm, add_assoc, ENNReal.add_halves]
  -- the intersection of the closed sets
  set Z : Set E := {e | ¬ ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ l, x l ∈ good (k l)) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e))}
  have hZnull : (μ : Measure E) Z = 0 := ae_iff.1 hc
  have hinter : (⋂ N, B N) ⊆ f ⁻¹' F ∪ Z := by
    intro e he
    by_cases heZ : e ∈ Z
    · exact Or.inr heZ
    · left
      have hT : ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
          (∀ l, x l ∈ good (k l)) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
            Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e)) := by
        by_contra h
        exact heZ h
      obtain ⟨V, hV⟩ := (𝓝 e).exists_antitone_basis
      have hpick : ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ x, (x ∈ good n ∧ x ∈ G n ⁻¹' F) ∧ I n x ∈ V N := by
        intro N
        have heB : e ∈ B N := mem_iInter.1 he N
        obtain ⟨z, hzV, hzU⟩ := mem_closure_iff_nhds.1 heB (V N) (hV.mem N)
        obtain ⟨n, hn, x, hx, hxz⟩ := mem_iUnion₂.1 hzU
        refine ⟨n, hn, x, hx, ?_⟩
        rw [hxz]
        exact hzV
      choose k hk x hx hxV using hpick
      have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
      have hIe : Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) := hV.tendsto hxV
      have hGe := hT k x hkt (fun l => (hx l).1) hIe
      exact hF.mem_of_tendsto hGe (Eventually.of_forall fun l => (hx l).2)
  have hmeas : ∀ N, NullMeasurableSet (B N) (μ : Measure E) :=
    fun N => (hBclosed N).measurableSet.nullMeasurableSet
  have htend : Tendsto (fun N => (μ : Measure E) (B N)) atTop (𝓝 ((μ : Measure E) (⋂ N, B N))) :=
    tendsto_measure_iInter_atTop hmeas hBanti ⟨0, measure_ne_top _ _⟩
  have hle : (μ : Measure E) (⋂ N, B N) ≤ (μ : Measure E) (f ⁻¹' F) :=
    (measure_mono hinter).trans ((measure_union_le _ _).trans (by rw [hZnull, add_zero]))
  exact le_trans (ge_of_tendsto htend (Eventually.of_forall hstep)) hle

/-- **The closed-set inequality with a badness function.** As `limsup_measure_preimage_le`, with the good sets replaced
by the sublevel sets of functions `h n`: `lam n {c < h n} → 0` for every `c > 0`, and the convergence of `G` is only
required along sequences on which `h` becomes eventually smaller than every `c > 0`. -/
theorem limsup_measure_preimage_le_of_badness {lam : ℕ → Measure X} {I : ℕ → X → E}
    (hI : ∀ n, AEMeasurable (I n) (lam n))
    {μs : ℕ → ProbabilityMeasure E} (hμs : ∀ n, (μs n : Measure E) = (lam n).map (I n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ)) {h : ℕ → X → ℝ}
    (hh : ∀ c : ℝ, 0 < c → Tendsto (fun n => lam n {x | c < h n x}) atTop (𝓝 0)) {G : ℕ → X → T} {f : E → T}
    (hc : ∀ᵐ e ∂(μ : Measure E), ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ c : ℝ, 0 < c → ∀ᶠ l in atTop, h (k l) (x l) ≤ c) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e)))
    {F : Set T} (hF : IsClosed F) :
    limsup (fun n => lam n (G n ⁻¹' F)) atTop ≤ (μ : Measure E) (f ⁻¹' F) := by
  set c : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1) with hcdef
  have hcpos : ∀ N, 0 < c N := fun N => by
    show 0 < 1 / ((N : ℝ) + 1)
    positivity
  have hcanti : Antitone c := by
    intro N M hNM
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    show 1 / ((M : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set B : ℕ → Set E := fun N => closure (⋃ n ∈ Ici N, I n '' ({x | h n x ≤ c N} ∩ G n ⁻¹' F))
  have hBclosed : ∀ N, IsClosed (B N) := fun N => isClosed_closure
  have hBanti : Antitone B := by
    intro N M hNM
    refine closure_mono (iUnion₂_subset fun n hn => subset_iUnion₂_of_subset n (le_trans hNM hn) ?_)
    exact image_mono (inter_subset_inter_left _ fun x hx => le_trans hx (hcanti hNM))
  -- one level of the closed sets
  have hstep : ∀ N, limsup (fun n => lam n (G n ⁻¹' F)) atTop ≤ (μ : Measure E) (B N) := by
    intro N
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.div_pos (ENNReal.coe_pos.2 hε).ne' (by norm_num)
    have h1 : ∀ᶠ n in atTop, lam n {x | c N < h n x} ≤ (ε : ℝ≥0∞) / 2 :=
      (ENNReal.tendsto_nhds_zero.1 (hh (c N) (hcpos N))) _ hε2
    have hlim : limsup (fun n => (μs n : Measure E) (B N)) atTop < (μ : Measure E) (B N) + (ε : ℝ≥0∞) / 2 :=
      lt_of_le_of_lt (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hBclosed N))
        (ENNReal.lt_add_right (measure_ne_top _ _) hε2.ne')
    have h2 := eventually_lt_of_limsup_lt hlim
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [h1, h2, eventually_ge_atTop N] with n hn1 hn2 hn3
    have hsub : G n ⁻¹' F ⊆ {x | c N < h n x} ∪ I n ⁻¹' B N := by
      intro x hx
      by_cases hg : h n x ≤ c N
      · right
        exact subset_closure (mem_iUnion₂.2 ⟨n, hn3, ⟨x, ⟨hg, hx⟩, rfl⟩⟩)
      · exact Or.inl (not_le.1 hg)
    have hmap : lam n (I n ⁻¹' B N) = (μs n : Measure E) (B N) := by
      rw [hμs n, Measure.map_apply_of_aemeasurable (hI n) (hBclosed N).measurableSet]
    calc lam n (G n ⁻¹' F) ≤ lam n ({x | c N < h n x} ∪ I n ⁻¹' B N) := measure_mono hsub
      _ ≤ lam n {x | c N < h n x} + lam n (I n ⁻¹' B N) := measure_union_le _ _
      _ ≤ (ε : ℝ≥0∞) / 2 + ((μ : Measure E) (B N) + (ε : ℝ≥0∞) / 2) := by
          rw [hmap]
          exact add_le_add hn1 hn2.le
      _ = (μ : Measure E) (B N) + ε := by
          rw [add_comm, add_assoc, ENNReal.add_halves]
  -- the intersection of the closed sets
  set Z : Set E := {e | ¬ ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ c : ℝ, 0 < c → ∀ᶠ l in atTop, h (k l) (x l) ≤ c) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e))}
  have hZnull : (μ : Measure E) Z = 0 := ae_iff.1 hc
  have hinter : (⋂ N, B N) ⊆ f ⁻¹' F ∪ Z := by
    intro e he
    by_cases heZ : e ∈ Z
    · exact Or.inr heZ
    · left
      have hT : ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
          (∀ c : ℝ, 0 < c → ∀ᶠ l in atTop, h (k l) (x l) ≤ c) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
            Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e)) := by
        by_contra hn
        exact heZ hn
      obtain ⟨V, hV⟩ := (𝓝 e).exists_antitone_basis
      have hpick : ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ x, (x ∈ {x | h n x ≤ c N} ∩ G n ⁻¹' F) ∧ I n x ∈ V N := by
        intro N
        have heB : e ∈ B N := mem_iInter.1 he N
        obtain ⟨z, hzV, hzU⟩ := mem_closure_iff_nhds.1 heB (V N) (hV.mem N)
        obtain ⟨n, hn, x, hx, hxz⟩ := mem_iUnion₂.1 hzU
        refine ⟨n, hn, x, hx, ?_⟩
        rw [hxz]
        exact hzV
      choose k hk x hx hxV using hpick
      have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
      have hIe : Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) := hV.tendsto hxV
      have hsmall : ∀ c' : ℝ, 0 < c' → ∀ᶠ l in atTop, h (k l) (x l) ≤ c' := by
        intro c' hc'
        obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hc'
        filter_upwards [eventually_ge_atTop N₀] with l hl
        have h1 : h (k l) (x l) ≤ c l := (hx l).1
        have h2 : c l ≤ c N₀ := hcanti hl
        have h3 : c N₀ < c' := hN₀
        linarith
      have hGe := hT k x hkt hsmall hIe
      exact hF.mem_of_tendsto hGe (Eventually.of_forall fun l => (hx l).2)
  have hmeas : ∀ N, NullMeasurableSet (B N) (μ : Measure E) :=
    fun N => (hBclosed N).measurableSet.nullMeasurableSet
  have htend : Tendsto (fun N => (μ : Measure E) (B N)) atTop (𝓝 ((μ : Measure E) (⋂ N, B N))) :=
    tendsto_measure_iInter_atTop hmeas hBanti ⟨0, measure_ne_top _ _⟩
  have hle : (μ : Measure E) (⋂ N, B N) ≤ (μ : Measure E) (f ⁻¹' F) :=
    (measure_mono hinter).trans ((measure_union_le _ _).trans (by rw [hZnull, add_zero]))
  exact le_trans (ge_of_tendsto htend (Eventually.of_forall hstep)) hle

/-- **Convergence in probability through an auxiliary space.** Under the hypotheses of
`limsup_measure_preimage_le_of_badness` for real functionals `G n` with limit `0` along the admissible sequences,
`lam n {δ ≤ G n} → 0` for every `δ > 0`. -/
theorem tendsto_measure_le_of_badness {lam : ℕ → Measure X} {I : ℕ → X → E} (hI : ∀ n, AEMeasurable (I n) (lam n))
    {μs : ℕ → ProbabilityMeasure E} (hμs : ∀ n, (μs n : Measure E) = (lam n).map (I n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ)) {h : ℕ → X → ℝ}
    (hh : ∀ c : ℝ, 0 < c → Tendsto (fun n => lam n {x | c < h n x}) atTop (𝓝 0)) {G : ℕ → X → ℝ}
    (hc : ∀ᵐ e ∂(μ : Measure E), ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ c : ℝ, 0 < c → ∀ᶠ l in atTop, h (k l) (x l) ≤ c) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) : Tendsto (fun n => lam n {x | δ ≤ G n x}) atTop (𝓝 0) := by
  have hlim := limsup_measure_preimage_le_of_badness (T := ℝ) hI hμs hμ hh (G := G) (f := fun _ => (0 : ℝ))
    hc (F := Ici δ) isClosed_Ici
  have hempty : (fun _ : E => (0 : ℝ)) ⁻¹' Ici δ = ∅ := by
    ext e
    simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_le]
    exact hδ
  rw [hempty, measure_empty] at hlim
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  exact (eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hε)).mono fun n hn => hn.le

variable [MeasurableSpace T] [OpensMeasurableSpace T]

/-- **The extended continuous mapping theorem through an auxiliary space.** Under the hypotheses of
`limsup_measure_preimage_le`, with probability measures `lam n` and Borel maps `G n`, `f`, the image laws of `lam n`
under `G n` converge weakly to the image of `μ` under `f`. -/
theorem tendsto_integral_comp {lam : ℕ → Measure X} [∀ n, IsProbabilityMeasure (lam n)] {I : ℕ → X → E}
    (hI : ∀ n, AEMeasurable (I n) (lam n))
    {μs : ℕ → ProbabilityMeasure E} (hμs : ∀ n, (μs n : Measure E) = (lam n).map (I n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ)) {good : ℕ → Set X}
    (hgood : Tendsto (fun n => lam n (good n)ᶜ) atTop (𝓝 0)) {G : ℕ → X → T} (hG : ∀ n, Measurable (G n))
    {f : E → T} (hf : Measurable f)
    (hc : ∀ᵐ e ∂(μ : Measure E), ∀ (k : ℕ → ℕ) (x : ℕ → X), Tendsto k atTop atTop →
      (∀ l, x l ∈ good (k l)) → Tendsto (fun l => I (k l) (x l)) atTop (𝓝 e) →
        Tendsto (fun l => G (k l) (x l)) atTop (𝓝 (f e)))
    (g : T →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g (G n x) ∂(lam n)) atTop (𝓝 (∫ e, g (f e) ∂(μ : Measure E))) := by
  let ν : ProbabilityMeasure T :=
    ⟨(μ : Measure E).map f, (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance⟩
  let νs : ℕ → ProbabilityMeasure T := fun n =>
    ⟨(lam n).map (G n), (Measure.isProbabilityMeasure_map_iff (hG n).aemeasurable).2 inferInstance⟩
  have hopen : ∀ U : Set T, IsOpen U → (ν : Measure T) U ≤ liminf (fun n => (νs n : Measure T) U) atTop := by
    intro U hU
    refine le_measure_liminf_of_limsup_measure_compl_le hU.measurableSet ?_
    have hkey := limsup_measure_preimage_le hI hμs hμ hgood hc (isClosed_compl_iff.2 hU)
    have hc' : ∀ n, (νs n : Measure T) Uᶜ = lam n (G n ⁻¹' Uᶜ) :=
      fun n => Measure.map_apply (hG n) hU.measurableSet.compl
    simp only [hc']
    exact hkey.trans_eq (Measure.map_apply hf hU.measurableSet.compl).symm
  have hweak : Tendsto νs atTop (𝓝 ν) := tendsto_of_forall_isOpen_le_liminf' hopen
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak g
  have hL : ∀ n, ∫ t, g t ∂(νs n : Measure T) = ∫ x, g (G n x) ∂(lam n) := fun n =>
    integral_map (hG n).aemeasurable g.continuous.measurable.aestronglyMeasurable
  have hR : ∫ t, g t ∂(ν : Measure T) = ∫ e, g (f e) ∂(μ : Measure E) :=
    integral_map hf.aemeasurable g.continuous.measurable.aestronglyMeasurable
  simpa only [hL, hR] using hint

end ExtendedMapping

end MatedCRT
