import MatedCRT.Audit.CorrectedForms
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.External.SLE
import Mathlib.Analysis.Convex.Contractible

/-!
# Audit: Lean refutations of Draft statements which are false as drafted

`MatedCRT/Audit/CorrectedForms.lean` refutes the Draft Lemmas 4.4 and 4.5. This file was
planned (worker A) to refute the three other Drafts that were known to be false only by a written argument
(`docs/campaign/CORRECTED-FORMS.md`). Status (2026-11-05): only the refutation of **Lemma 3.1** is in this file;
the refutations of Lemmas 3.2 and 7.2 below are PLANNED (their written arguments are still to be recorded)
and not yet formalized.
Each refutation holds for every valid environment `S` (`S.IsValid 𝒮 γ`, some `γ ∈ (0, 2)`) and uses one cited input,
taken as an explicit hypothesis:

* **Lemma 3.1** (`DiscretePotentialTightnessStmt`: `D` not open) from the `m_ε` scaling
  (`MepsScalingInput`, eq:meps-scaling, BG20 eq. (1.8)): `not_discretePotentialTightnessStmt`. The set `D` is the
  closed real segment `[0, 1/4]`. It has empty interior, so `V^ε(D) \ V^ε(∂D) = ∅` and the Laplacian hypothesis is
  vacuous. The data `u^ε(a) = m_ε 1{Re η(a) > 1/8}` satisfy `|u^ε| ≤ C ε⁻¹` by the scaling of `m_ε`. Their rescalings
  `ū^ε(x) = 1{Re η(a^ε_x) > 1/8}` converge uniformly on `O = D` along no subsequence to a continuous limit,
  because the cells shrink uniformly on `D` (continuity and transience of `η`).
* **Lemma 3.2 (printed form)** (review-L32 F1): its boundary exponent cannot be chosen independently of `χ`.
  The adopted Draft statement is corrected [C6]; the counterexample concerns the earlier printed form.
* **Lemma 7.2** (`MassBoundOdometerStmt`: radii below the cell scale) from Lemma 2.8:
  `not_massBoundOdometerStmt`. Take `Θ = {0}` and the first grid time `t = jθ` at which `Λ^ε_t` has a vertex
  `x ≠ 0`. Such a time exists: `1 ∈ Λ^ε_t` for large `t`, by lower bounds over all admissible functions
  (`one_mem_matedDiscreteCluster`). The stopped odometer grows at most linearly in `t`
  (`stoppedOdometer_le_add`), so `sup_{∂Θ} u^ε_t ≤ θ ε⁻¹ max_{∂Θ} g^ε_{B_ρ}(0, ·)`. This is `< 1/C` for `θ` small.
  The point `z ∈ H_x \ H_0` and a radius `s` below the cell scale then give `|V^ε(B_{c₀ s}(z)) ∩ Λ^ε_t| ≥ 1`.

Lemma 2.8 is used only to place the cells `H_0, H_1` inside `B_ρ` (7.2), and to bound `diam H_1` above and the cell
diameters near `0` below (3.2). The almost sure facts used are the area parametrization of `η`, its transience
(`IsValid.ae_tendsto_cocompact`), the local finiteness of the map and that adjacent cells meet
(`adjacentCellsMeetAeStep`).
-/

namespace MatedCRT.Audit.Refutations

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

variable {𝒮 : SpaceFillingSLEModel}

/-! ## General tools -/

/-- `ε^p → 0` as `ε → 0⁺`, for `p > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε ^ p) (𝓝 0) (𝓝 ((0 : ℝ) ^ p)) :=
    (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Two events which both hold with polynomially high probability cannot be disjoint, off a null set, for all small
`ε`. -/
theorem false_of_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E F : ℝ → Set Ω} {G : Set Ω} (hE : PolyHighProb P E) (hF : PolyHighProb P F) (hG : ∀ᵐ ω ∂P, ω ∈ G)
    (hdis : ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ G, ω ∈ F ε → ω ∉ E ε) : False := by
  obtain ⟨p, hp, C₁, r₁, hr₁, h₁⟩ := hE
  obtain ⟨q, hq, C₂, r₂, hr₂, h₂⟩ := hF
  have hlim : Tendsto (fun ε : ℝ => |C₁| * ε ^ p + |C₂| * ε ^ q) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_rpow_nhdsGT_zero hp).const_mul |C₁|).add ((tendsto_rpow_nhdsGT_zero hq).const_mul |C₂|)
    rwa [mul_zero, mul_zero, add_zero] at this
  have hI₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 r₁ := Ioo_mem_nhdsGT hr₁
  have hI₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 r₂ := Ioo_mem_nhdsGT hr₂
  obtain ⟨ε, hdisε, hlt, ⟨hε, hε₁⟩, -, hε₂⟩ :=
    (hdis.and ((hlim.eventually (eventually_lt_nhds one_pos)).and (hI₁.and hI₂))).exists
  have hcov : (univ : Set Ω) ⊆ ((E ε)ᶜ ∪ (F ε)ᶜ) ∪ Gᶜ := by
    intro ω _
    by_cases hω : ω ∈ G
    · by_cases hωF : ω ∈ F ε
      · exact Or.inl (Or.inl (hdisε ω hω hωF))
      · exact Or.inl (Or.inr hωF)
    · exact Or.inr hω
  have hG0 : P Gᶜ = 0 := ae_iff.1 hG
  have hb₁ : P (E ε)ᶜ ≤ ENNReal.ofReal (|C₁| * ε ^ p) := (h₁ ε hε hε₁).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hε.le _)))
  have hb₂ : P (F ε)ᶜ ≤ ENNReal.ofReal (|C₂| * ε ^ q) := (h₂ ε hε hε₂).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hε.le _)))
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (|C₁| * ε ^ p) + ENNReal.ofReal (|C₂| * ε ^ q) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (((E ε)ᶜ ∪ (F ε)ᶜ) ∪ Gᶜ) := measure_mono hcov
      _ ≤ P (E ε)ᶜ + P (F ε)ᶜ + P Gᶜ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (|C₁| * ε ^ p) + ENNReal.ofReal (|C₂| * ε ^ q) + 0 := by
        rw [hG0]
        exact add_le_add (add_le_add hb₁ hb₂) le_rfl
      _ = _ := add_zero _
  rw [← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hε.le _))
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hε.le _))] at h1
  exact absurd (ENNReal.ofReal_lt_one.2 hlt) (not_lt.2 h1)

/-- A positive sequence below `ε₀` which tends to `0`. -/
theorem exists_seq_pos_lt_tendsto_zero {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ e : ℕ → ℝ, (∀ n, 0 < e n) ∧ (∀ n, e n < ε₀) ∧ Tendsto e atTop (𝓝 0) := by
  refine ⟨fun n => ε₀ / 2 * (1 / ((n : ℝ) + 1)), fun n => by positivity, fun n => ?_, ?_⟩
  · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ε₀ / 2 * (1 / ((n : ℝ) + 1)) ≤ ε₀ / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < ε₀ := by linarith
  · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε₀ / 2)
    rwa [mul_zero] at this

/-! ## Cells -/

theorem mem_cell_zero {η : ℝ → ℂ} {ε s : ℝ} (h1 : -ε ≤ s) (h2 : s ≤ 0) : η s ∈ cell ε η 0 :=
  ⟨s, ⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩

theorem mem_cell_one {η : ℝ → ℂ} {ε s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ ε) : η s ∈ cell ε η 1 :=
  ⟨s, ⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩

theorem zero_mem_cell_zero {η : ℝ → ℂ} (hη0 : η 0 = 0) {ε : ℝ} (hε : 0 < ε) : (0 : ℂ) ∈ cell ε η 0 := by
  have h := mem_cell_zero (η := η) (ε := ε) (s := 0) (by linarith) le_rfl
  rwa [hη0] at h

theorem zero_mem_cell_one {η : ℝ → ℂ} (hη0 : η 0 = 0) {ε : ℝ} (hε : 0 < ε) : (0 : ℂ) ∈ cell ε η 1 := by
  have h := mem_cell_one (η := η) (ε := ε) (s := 0) le_rfl hε.le
  rwa [hη0] at h

/-- A cell through `0` of diameter `< r` lies in `B_r`. -/
theorem cell_subset_ball_of_diam {η : ℝ → ℂ} (hc : Continuous η) {ε r : ℝ} {k : ℤ}
    (h0 : (0 : ℂ) ∈ cell ε η k) (hd : diam (cell ε η k) < r) : cell ε η k ⊆ ball 0 r := fun z hz => by
  rw [mem_ball]
  exact (dist_le_diam_of_mem (isCompact_Icc.image hc).isBounded hz h0).trans_lt hd

/-- A cell through `0` inside `B_r` is a vertex of `V^ε(B_r) \ V^ε(∂B_r)`. -/
theorem mem_ballInterior_of_subset {η : ℝ → ℂ} {ε r : ℝ} {k : ℤ} (h0 : (0 : ℂ) ∈ cell ε η k) (hr : 0 < r)
    (hsub : cell ε η k ⊆ ball 0 r) : k ∈ ballInterior ε η r := by
  refine ⟨⟨0, h0, mem_ball_self hr⟩, ?_⟩
  rintro ⟨z, hz, hzfr⟩
  have h' : z ∈ ball (0 : ℂ) r ∩ frontier (ball 0 r) := ⟨hsub hz, hzfr⟩
  rw [isOpen_ball.inter_frontier_eq] at h'
  exact h'

/-- **No cell lies inside another one** (area parametrization): for `x ≠ 0`, `H_x ⊄ H_0`. Otherwise
`η([ε(x-1), εx]) ⊆ η([-ε, 0])` and `μ` of the union of the cells between them would lose the mass `ε`. -/
theorem cell_not_subset_cell_zero {μ : Measure ℂ} {η : ℝ → ℂ} (hA : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) {x : ℤ} (hx : x ≠ 0) : ¬ cell ε η x ⊆ cell ε η 0 := by
  intro hsub
  have hmeas := hA.2.2.2
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hx1 : (x : ℝ) ≤ -1 := by
      have : x ≤ -1 := by omega
      exact_mod_cast this
    have hcell0 : cell ε η 0 ⊆ η '' Icc (ε * x) 0 :=
      image_mono (Icc_subset_Icc (by push_cast; nlinarith) (by push_cast; linarith))
    have hsplit : η '' Icc (ε * (x - 1)) 0 ⊆ η '' Icc (ε * x) 0 := by
      rw [← Icc_union_Icc_eq_Icc (b := ε * x) (by nlinarith) (by nlinarith), image_union]
      exact union_subset (hsub.trans hcell0) subset_rfl
    have h1 := measure_mono (μ := μ) hsplit
    rw [hmeas _ _ (by nlinarith), hmeas _ _ (by nlinarith),
      ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at h1
    nlinarith
  · have hx1 : (1 : ℝ) ≤ x := by
      have : 1 ≤ x := by omega
      exact_mod_cast this
    have hcell0 : cell ε η 0 ⊆ η '' Icc (-ε) (ε * (x - 1)) :=
      image_mono (Icc_subset_Icc (by push_cast; linarith) (by push_cast; nlinarith))
    have hsplit : η '' Icc (-ε) (ε * x) ⊆ η '' Icc (-ε) (ε * (x - 1)) := by
      rw [← Icc_union_Icc_eq_Icc (b := ε * (x - 1)) (by nlinarith) (by nlinarith), image_union]
      exact union_subset subset_rfl (hsub.trans hcell0)
    have h1 := measure_mono (μ := μ) hsplit
    rw [hmeas _ _ (by nlinarith), hmeas _ _ (by nlinarith),
      ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at h1
    nlinarith

/-- **Cells shrink uniformly on compact sets.** For a continuous, surjective, transient curve `η` and a compact `K`,
the marked point `η(a^ε_x)` of the cell of `x` is within `δ` of `x`, for all `x ∈ K` and all small `ε`. -/
theorem exists_vertexPoint_vertexOf_near {η : ℝ → ℂ} (hc : Continuous η) (hs : Function.Surjective η)
    (ht : Tendsto η (cocompact ℝ) (cocompact ℂ)) {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ x ∈ K,
      ‖vertexPoint ε η (vertexOf ε η x) - x‖ < δ := by
  obtain ⟨L, hL, hLK⟩ := Filter.mem_cocompact.1 (ht hK.compl_mem_cocompact)
  obtain ⟨T, hT⟩ := hL.isBounded.subset_closedBall 0
  have hpre : ∀ s : ℝ, η s ∈ K → |s| ≤ T := by
    intro s hsK
    have hsL : s ∈ L := by
      by_contra hsL
      exact hLK hsL hsK
    have := hT hsL
    rwa [mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨θ, hθ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -T - 1) (b := T + 1)).uniformContinuousOn_of_continuous hc.continuousOn) δ hδ
  refine ⟨min 1 θ, lt_min one_pos hθ, fun ε hε hε₁ x hx => ?_⟩
  have hε1 : ε < 1 := hε₁.trans_le (min_le_left _ _)
  have hεθ : ε < θ := hε₁.trans_le (min_le_right _ _)
  have hne : {k : ℤ | x ∈ cell ε η k}.Nonempty := by
    obtain ⟨s, hsx⟩ := hs x
    refine ⟨⌈s / ε⌉, s, ⟨?_, ?_⟩, hsx⟩
    · have h1 := Int.ceil_lt_add_one (s / ε)
      have h2 : ((⌈s / ε⌉ : ℤ) : ℝ) - 1 ≤ s / ε := by linarith
      calc ε * (((⌈s / ε⌉ : ℤ) : ℝ) - 1) ≤ ε * (s / ε) := mul_le_mul_of_nonneg_left h2 hε.le
        _ = s := by field_simp
    · calc s = ε * (s / ε) := by field_simp
        _ ≤ ε * ((⌈s / ε⌉ : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (Int.le_ceil _) hε.le
  have hbdd : BddBelow {k : ℤ | x ∈ cell ε η k} := by
    refine ⟨⌈-T / ε⌉, fun k hk => ?_⟩
    obtain ⟨s, hsI, hsx⟩ := hk
    have hs' := abs_le.1 (hpre s (by rw [hsx]; exact hx))
    rw [Int.ceil_le, div_le_iff₀ hε]
    nlinarith [hsI.2]
  have hmem : vertexOf ε η x ∈ {k : ℤ | x ∈ cell ε η k} := Int.csInf_mem hne hbdd
  obtain ⟨s, hsI, hsx⟩ := hmem
  have hsT := abs_le.1 (hpre s (by rw [hsx]; exact hx))
  have hdist := hunif s ⟨by linarith [hsT.1], by linarith [hsT.2]⟩ (ε * (vertexOf ε η x : ℝ))
    ⟨by nlinarith [hsI.2], by nlinarith [hsI.1]⟩ (by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> nlinarith [hsI.1, hsI.2])
  calc ‖vertexPoint ε η (vertexOf ε η x) - x‖ = dist (η (ε * (vertexOf ε η x : ℝ))) (η s) := by
        rw [Complex.dist_eq, hsx]
        rfl
    _ = dist (η s) (η (ε * (vertexOf ε η x : ℝ))) := dist_comm _ _
    _ < δ := hdist

/-! ## Lemma 3.1: false for the closed segment `[0, 1/4]` -/

/-- The closed real segment `[0, 1/4] ⊆ ℂ`: connected, compact, not open, inside `B_{1/2}`. -/
def realSegment : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc 0 (1 / 4)

theorem ofReal_mem_realSegment {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 4) : (t : ℂ) ∈ realSegment :=
  ⟨t, ⟨h0, h1⟩, rfl⟩

theorem isCompact_realSegment : IsCompact realSegment := isCompact_Icc.image Complex.continuous_ofReal

theorem isConnected_realSegment : IsConnected realSegment :=
  (isConnected_Icc (by norm_num)).image _ Complex.continuous_ofReal.continuousOn

theorem realSegment_subset_ball : realSegment ⊆ ball 0 (1 / 2) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- The segment has empty interior, so it is its own frontier. -/
theorem realSegment_subset_frontier : realSegment ⊆ frontier realSegment := by
  intro x hx
  show x ∈ closure realSegment \ interior realSegment
  refine ⟨subset_closure hx, fun hint => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hy : x + ((r / 2 : ℝ) : ℂ) * Complex.I ∈ ball x r := by
    rw [mem_ball, Complex.dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  obtain ⟨t, -, ht⟩ := hball hy
  obtain ⟨t', -, rfl⟩ := hx
  have := congrArg Complex.im ht
  simp at this
  linarith

/-- The segment has no vertex in `V^ε(D) \ V^ε(∂D)`: the Laplacian hypotheses of Lemma 3.1 are vacuous. -/
theorem not_mem_interiorCellVertices_realSegment (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) :
    k ∉ interiorCellVertices ε η realSegment := fun hk =>
  hk.2 (Sec7.cellVertices_mono realSegment_subset_frontier hk.1)

/-- The step function `1{Re z > 1/8}`. -/
noncomputable def reStep (z : ℂ) : ℝ := if 1 / 8 < z.re then 1 else 0

theorem measurable_reStep : Measurable reStep :=
  Measurable.ite (measurableSet_lt measurable_const Complex.measurable_re) measurable_const measurable_const

theorem abs_reStep_le (z : ℂ) : |reStep z| ≤ 1 := by
  unfold reStep
  split_ifs <;> norm_num

/-- A uniform limit on the segment of step functions `1{Re y_k(x) > 1/8}` with `y_k(x)` uniformly close to `x` is
not continuous. -/
theorem not_continuousOn_of_reStep {ubar : ℂ → ℝ} {F : ℕ → ℂ → ℝ} (hcont : ContinuousOn ubar realSegment)
    (hunif : TendstoUniformlyOn F ubar atTop realSegment)
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ x ∈ realSegment, ∃ y : ℂ, ‖y - x‖ < δ ∧ F k x = reStep y) :
    False := by
  have hpD : ((1 / 8 : ℝ) : ℂ) ∈ realSegment := ofReal_mem_realSegment (by norm_num) (by norm_num)
  obtain ⟨r, hr, hcr⟩ := Metric.continuousOn_iff.1 hcont _ hpD (1 / 4) (by norm_num)
  obtain ⟨r', hr'⟩ : ∃ r' : ℝ, r' = min (r / 2) (1 / 16) := ⟨_, rfl⟩
  have hr'pos : 0 < r' := by rw [hr']; exact lt_min (half_pos hr) (by norm_num)
  have hr'le : r' ≤ 1 / 16 := by rw [hr']; exact min_le_right _ _
  have hr'lt : r' < r := by rw [hr']; exact (min_le_left _ _).trans_lt (half_lt_self hr)
  obtain ⟨k, hk1, hk2⟩ := ((Metric.tendstoUniformlyOn_iff.1 hunif (1 / 4) (by norm_num)).and
    (hnear r' hr'pos)).exists
  have key : ∀ c : ℝ, |c| = r' →
      |ubar ((1 / 8 + c : ℝ) : ℂ) - (if 0 < c then 1 else 0)| < 1 / 4 ∧
        |ubar ((1 / 8 + c : ℝ) : ℂ) - ubar ((1 / 8 : ℝ) : ℂ)| < 1 / 4 := by
    intro c hc
    have hcb := abs_le.1 ((le_of_eq hc).trans hr'le)
    have hcD : ((1 / 8 + c : ℝ) : ℂ) ∈ realSegment := ofReal_mem_realSegment (by linarith) (by linarith)
    obtain ⟨y, hy, hFy⟩ := hk2 _ hcD
    have h1 := hk1 _ hcD
    rw [hFy] at h1
    have hre := (Complex.abs_re_le_norm (y - ((1 / 8 + c : ℝ) : ℂ))).trans_lt hy
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    obtain ⟨hl, hu⟩ := abs_lt.1 hre
    have hval : reStep y = if 0 < c then 1 else 0 := by
      unfold reStep
      by_cases hc0 : 0 < c
      · have : c = r' := by rw [← hc, abs_of_pos hc0]
        rw [ite_eq_left hc0, ite_eq_left (by linarith)]
      · have : c = -r' := by rw [← hc, abs_of_nonpos (not_lt.1 hc0), neg_neg]
        rw [ite_eq_right hc0, ite_eq_right (not_lt.2 (by linarith))]
    rw [hval, Real.dist_eq] at h1
    refine ⟨h1, ?_⟩
    rw [← Real.dist_eq]
    refine hcr _ hcD ?_
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, add_sub_cancel_left, hc]
    exact hr'lt
  obtain ⟨h₁, h₁'⟩ := key (-r') (by rw [abs_neg, abs_of_pos hr'pos])
  obtain ⟨h₂, h₂'⟩ := key r' (abs_of_pos hr'pos)
  rw [ite_eq_right (by linarith)] at h₁
  rw [ite_eq_left hr'pos] at h₂
  obtain ⟨-, h₁u⟩ := abs_lt.1 h₁
  obtain ⟨h₂l, -⟩ := abs_lt.1 h₂
  obtain ⟨h₁'l, -⟩ := abs_lt.1 h₁'
  obtain ⟨-, h₂'u⟩ := abs_lt.1 h₂'
  linarith

/-- **The Draft Lemma 3.1 is false**, for every valid environment, given the scaling of `m_ε`
(`MepsScalingInput`, eq:meps-scaling). The set `D` is the closed segment `[0, 1/4]` and `O = D`, with the data
`u^ε(a) = m_ε 1{Re η(a) > 1/8}` along a deterministic sequence `ε_n ↓ 0`. -/
theorem not_discretePotentialTightnessStmt (hm : MepsScalingInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ¬ DiscretePotentialTightnessStmt 𝒮 := by
  intro h
  have := hS.isProbabilityMeasure
  obtain ⟨K, hK1, hK⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hK Ω S hS
  have hKpos : 0 < K := one_pos.trans hK1
  obtain ⟨e, hepos, helt, he0⟩ := exists_seq_pos_lt_tendsto_zero hε₀
  have hmεpos : ∀ n, 0 < S.mε (e n) := fun n =>
    (mul_pos (inv_pos.2 hKpos) (inv_pos.2 (hepos n))).trans_le (hmε (e n) (hepos n) (helt n)).1
  have hηm : ∀ s : ℝ, Measurable[S.envSigma] fun ω => S.η ω s := by
    intro s
    rw [measurable_iff_comap_le]
    exact le_sup_of_le_right
      (le_iSup (fun s : ℝ => MeasurableSpace.comap (fun ω => S.η ω s) inferInstance) s)
  have hum : ∀ (n : ℕ) (a : ℤ), Measurable[S.envSigma] fun ω =>
      S.mε (e n) * reStep (vertexPoint (e n) (S.η ω) a) := fun n a =>
    measurable_const.mul (measurable_reStep.comp (hηm (e n * a)))
  have hbd : ∀ (ω : Ω) (n : ℕ), ∀ a ∈ cellVertices (e n) (S.η ω) realSegment,
      |S.mε (e n) * reStep (vertexPoint (e n) (S.η ω) a)| ≤ K / e n := by
    intro ω n a _
    rw [abs_mul, abs_of_pos (hmεpos n), div_eq_mul_inv]
    calc S.mε (e n) * |reStep (vertexPoint (e n) (S.η ω) a)| ≤ S.mε (e n) * 1 :=
          mul_le_mul_of_nonneg_left (abs_reStep_le _) (hmεpos n).le
      _ ≤ K * (e n)⁻¹ := by rw [mul_one]; exact (hmε (e n) (hepos n) (helt n)).2
  obtain ⟨Φ, -, hae⟩ := h γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num) Ω S hS realSegment
    realSegment_subset_ball isConnected_realSegment (fun _ => e)
    (fun ω n a => S.mε (e n) * reStep (vertexPoint (e n) (S.η ω) a)) (fun _ => K)
    (fun _ => measurable_const) (fun _ n => hepos n) (fun _ => he0) hum measurable_const (fun _ => hKpos)
    (fun ω n a ha => absurd ha (not_mem_interiorCellVertices_realSegment _ _ a)) hbd
  obtain ⟨ω, ⟨hmono, ubar, hcont, hO, -⟩, hA, htr⟩ :=
    (hae.and (hS.isAreaParametrized.and hS.ae_tendsto_cocompact)).exists
  refine not_continuousOn_of_reStep hcont
    (hO realSegment isCompact_realSegment isCompact_realSegment.isClosed.closure_subset) fun δ hδ => ?_
  obtain ⟨ε₁, hε₁, hnear⟩ := exists_vertexPoint_vertexOf_near hA.1 hA.2.2.1 htr isCompact_realSegment hδ
  filter_upwards [(he0.comp hmono.tendsto_atTop).eventually (eventually_lt_nhds hε₁)] with k hk x hx
  exact ⟨_, hnear _ (hepos _) hk x hx, inv_mul_cancel_left₀ (hmεpos _).ne' _⟩

end MatedCRT.Audit.Refutations
