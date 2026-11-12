import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureSandwich
import MatedCRT.FirstPass.S5c.BadEvents

/-!
# Convergence of the degree-weighted measure for Lipschitz test functions on a ball

The probabilistic step of BG20, Corollary A.6 (Lemma 2.10 of the paper) for a continuous, bounded,
Lipschitz test function `f` vanishing off a ball `B_ρ`, `ρ < 1`: if the two-sided degree-weighted counting
bound of BG20 Lemma A.5 holds on every ball `B_r`, `r < 1`, with polynomially high probability (for test
functions bounded by `ε^{-b}` and `ε^{-b}`-Lipschitz), and the cell size estimate (Lemma 2.8) holds, then
`∫ f dμ^ε_h → 6 ∫ f dμ_h` in probability.

* `tendstoInProbability_of_polyHighProb`: an error bound `g ε → 0` holding on events of polynomially high
  probability gives convergence in probability (no measurability is used);
* `IsAreaParametrized.exists_finset_cellVertices_ball`: when `B_1 ⊆ η([-M, M])` and the cells meeting `B_r` have
  diameter at most `s` with `r + s < 1`, only finitely many cells meet `B_r`;
* `tendstoInProbability_degreeWeightedMeasure_of_ball`: the convergence, from the deterministic estimate
  `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le_of_ball` on the event where the
  counting bound on `B_r` (`r = (max ρ 0 + 1)/2`), the cell size bound on `B_r` and the coverage
  `B_1 ⊆ η([-ε⁻¹, ε⁻¹])` hold;
* `tendstoInProbability_degreeWeightedMeasure_of_ball_random`: the same for a test function `f_ω` depending on `ω`
  arbitrarily, with `K, L, ρ` uniform in `ω` (the estimate is pointwise in `ω`).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- An error bound `g ε → 0` holding on events of polynomially high probability gives convergence in
probability. -/
theorem tendstoInProbability_of_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → ℝ} {Y : Ω → ℝ} {E : ℝ → Set Ω} (hE : PolyHighProb P E) {g : ℝ → ℝ}
    (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ E ε, |X ε ω - Y ω| ≤ g ε) : TendstoInProbability P X Y := by
  intro δ hδ
  have hle : ∀ᶠ ε in 𝓝[>] 0, P {ω | δ < |X ε ω - Y ω|} ≤ P (E ε)ᶜ := by
    filter_upwards [hbound, hg.eventually_lt_const hδ] with ε hb hgε
    exact measure_mono fun ω hω hωE => lt_asymm hω ((hb ω hωE).trans_lt hgε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (S5c.tendsto_compl_of_polyHighProb hE) (Eventually.of_forall fun _ => zero_le) hle

private theorem tendsto_rpow_nhdsGT_zero_of_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h0 : ContinuousAt (fun r : ℝ => r ^ a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h1 : Tendsto (fun r : ℝ => r ^ a) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ a)) :=
    h0.tendsto.mono_left nhdsWithin_le_nhds
  simpa [Real.zero_rpow ha.ne'] using h1

private theorem eventually_le_rpow_neg {b : ℝ} (hb : 0 < b) (K : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), K ≤ ε ^ (-b) := by
  have hK : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [(tendsto_rpow_nhdsGT_zero_of_pos hb).eventually_lt_const (inv_pos.2 hK),
    self_mem_nhdsWithin] with ε hε hε0
  have hε0' : 0 < ε := hε0
  rw [Real.rpow_neg hε0'.le]
  exact (le_max_left K 1).trans ((lt_inv_comm₀ (Real.rpow_pos_of_pos hε0' b) hK).1 hε).le

/-- **Finitely many cells meet a ball.** If `B_1 ⊆ η([-M, M])` and every cell meeting `B_r` has diameter
at most `s`, with `r + s < 1`, then the set `V^ε(B_r)` of cells meeting `B_r` is finite. -/
theorem IsAreaParametrized.exists_finset_cellVertices_ball {μ : Measure ℂ} {η : ℝ → ℂ}
    (hpar : IsAreaParametrized μ η) {ε M r s : ℝ} (hε : 0 < ε) (hM : 0 < M) (hrs : r + s < 1)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball 0 r).Nonempty → diam (cell ε η k) ≤ s) :
    ∃ t : Finset ℤ, ∀ k, k ∈ t ↔ k ∈ cellVertices ε η (ball 0 r) := by
  classical
  set N : ℕ := ⌈M / ε⌉₊ + 1 with hN
  refine ⟨(Finset.Icc (-(N : ℤ)) N).filter (· ∈ cellVertices ε η (ball 0 r)), fun k => ?_⟩
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun hk => ⟨?_, hk⟩⟩
  have hsub : cell ε η k ⊆ ball 0 1 := by
    intro x hx
    obtain ⟨y, hyc, hyr⟩ := hk
    have hxy : dist x y ≤ s := (dist_le_diam_of_mem (isCompact_cell hpar.1 ε k).isBounded hx hyc).trans
      (hdiam k ⟨y, hyc, hyr⟩)
    rw [mem_ball_zero_iff] at hyr ⊢
    have h1 := norm_sub_norm_le x y
    rw [dist_eq_norm] at hxy
    linarith
  have hb := hpar.cell_index_bounds hε hM (hsub.trans hcov)
  have hc := Nat.le_ceil (M / ε)
  have h1 : -(M / ε) < k := by
    rw [neg_div', div_lt_iff₀ hε]
    linarith
  have h2 : (k : ℝ) - 1 < M / ε := by
    rw [lt_div_iff₀ hε]
    linarith
  have h3 : -((N : ℤ) : ℝ) < k := by push_cast [hN]; linarith
  have h4 : (k : ℝ) < (N : ℤ) + 1 := by push_cast [hN]; linarith
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast h3.le
  · have : k < (N : ℤ) + 1 := by exact_mod_cast h4
    omega

/-- **Corollary A.6 on a ball, uniformly in the test function** (BG20). Under the hypotheses of
`tendstoInProbability_degreeWeightedMeasure_of_ball`, the convergence `∫ f_ω dμ^ε_h → 6 ∫ f_ω dμ_h` in probability
holds for a test function `f_ω` depending on `ω` in an arbitrary way, provided every `f_ω` is continuous, bounded by
`K`, `L`-Lipschitz and vanishes off `B_ρ`, `ρ < 1`, with `K, L, ρ` not depending on `ω` (the Lemma A.5 bound is
uniform in the test function). This is the form used in the scaling step, where `f_ω = f(R_b(ω) ·)`. -/
theorem tendstoInProbability_degreeWeightedMeasure_of_ball_random {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {α b : ℝ} (hα : 0 < α) (hb : 0 < b)
    (hA5 : ∀ r : ℝ, 0 < r → r < 1 → PolyHighProb S.P fun ε => {ω | ∀ g : ℂ → ℝ,
      (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) → (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
      ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε (S.η ω) (ball 0 r), w k ∈ cell ε (S.η ω) k ∩ closure (ball 0 r)) →
      6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂S.μ ω - ε ^ (-1 + α) ≤
          ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ∧
        ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂S.μ ω + ε ^ (-1 + α)})
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) {K L ρ : ℝ} (hρ : ρ < 1) (hfK : ∀ ω x, |f ω x| ≤ K)
    (hfL : ∀ ω x y, |f ω x - f ω y| ≤ L * ‖x - y‖) (hfρ : ∀ ω, ∀ x ∉ ball (0 : ℂ) ρ, f ω x = 0) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f ω x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, f ω x ∂S.μ ω) := by
  set ρ₀ : ℝ := max ρ 0 with hρ₀
  have hρ₀1 : ρ₀ < 1 := max_lt hρ one_pos
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  have hfρ₀ : ∀ ω, ∀ x ∉ ball (0 : ℂ) ρ₀, f ω x = 0 := fun ω x hx =>
    hfρ ω x fun h => hx (ball_subset_ball (le_max_left _ _) h)
  set r : ℝ := (ρ₀ + 1) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hρr : ρ₀ < r := by rw [hr]; linarith
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq_def
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨c, hc, C, hcov⟩ := hMoT.coverage
  have hcovP : PolyHighProb S.P fun ε =>
      {ω | ball (0 : ℂ) 1 ⊆ η' ω '' Icc (-(ε ^ (-(1 : ℝ)))) (ε ^ (-(1 : ℝ)))} := by
    refine ⟨c * 1, by positivity, C, 1, one_pos, fun ε hε hε1 => ?_⟩
    have hM : 1 < ε ^ (-(1 : ℝ)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by norm_num)
    have h := hcov _ hM
    rw [← Real.rpow_mul hε.le, show -(1 : ℝ) * -c = c * 1 by ring] at h
    exact h
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  have hdiam := hcell γ hγ hγ2 q r hq hq1 hr0 hr1 Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω} :=
    hS.isAreaParametrized.and (hae.mono fun ω h => h.1)
  refine tendstoInProbability_of_polyHighProb
    (((hdiam.inter hcovP).inter (hA5 r hr0 hr1)).inter_ae hW) (g := fun ε => 2 * ε ^ α) ?_ ?_
  · simpa using (tendsto_rpow_nhdsGT_zero_of_pos hα).const_mul 2
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_rpow_nhdsGT_zero_of_pos hq).eventually_lt_const (show (0 : ℝ) < 1 - r by linarith),
      (tendsto_rpow_nhdsGT_zero_of_pos hα).eventually_lt_const (show (0 : ℝ) < r - ρ₀ by linarith),
      eventually_le_rpow_neg hb K, eventually_le_rpow_neg hb L] with ε hε0 hεq hεα hKb hLb
    rintro ω ⟨⟨⟨hdω, hcω⟩, hAω⟩, hpar, hηω⟩
    have hε : (0 : ℝ) < ε := hε0
    simp only [mem_ofPred_eq] at hdω hcω hAω
    rw [hηω] at hcω
    have hM : 0 < ε ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hε _
    have hdiam' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 r).Nonempty →
        diam (cell ε (S.η ω) k) ≤ ε ^ q := fun k hk => by
      have h := (hdω k hk).2
      rwa [hexp] at h
    obtain ⟨t, ht⟩ :=
      hpar.exists_finset_cellVertices_ball hε hM (show r + ε ^ q < 1 by linarith) hcω hdiam'
    refine hpar.abs_integral_degreeWeightedMeasure_sub_six_le_of_ball hε hr0 (by linarith) t ht (hf ω) (hfK ω)
      (hfL ω) (hfρ₀ ω) ?_
    intro g hg hgL w hw
    exact hAω g (fun x => ⟨(hg x).1, (hg x).2.trans hKb⟩)
      (fun x y => (hgL x y).trans (mul_le_mul_of_nonneg_right hLb (norm_nonneg _))) w hw

/-- **Corollary A.6 for Lipschitz test functions on a ball, from Lemma A.5** (BG20). Let the cell size
estimate hold for the model, and let the two-sided degree-weighted counting bound of BG20 Lemma A.5 hold on
every ball `B_r`, `0 < r < 1`, with polynomially high probability, for all nonnegative test functions bounded
by `ε^{-b}` and `ε^{-b}`-Lipschitz and all choices of points `w_k ∈ H^ε_k ∩ cl(B_r)`. Then for every continuous
`f` with `|f| ≤ K`, `L`-Lipschitz and vanishing off `B_ρ`, `ρ < 1`, `∫ f dμ^ε_h → 6 ∫ f dμ_h` in
probability. -/
theorem tendstoInProbability_degreeWeightedMeasure_of_ball {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {α b : ℝ} (hα : 0 < α) (hb : 0 < b)
    (hA5 : ∀ r : ℝ, 0 < r → r < 1 → PolyHighProb S.P fun ε => {ω | ∀ g : ℂ → ℝ,
      (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) → (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
      ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε (S.η ω) (ball 0 r), w k ∈ cell ε (S.η ω) k ∩ closure (ball 0 r)) →
      6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂S.μ ω - ε ^ (-1 + α) ≤
          ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ∧
        ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂S.μ ω + ε ^ (-1 + α)})
    {f : ℂ → ℝ} (hf : Continuous f) {K L ρ : ℝ} (hρ : ρ < 1) (hfK : ∀ x, |f x| ≤ K)
    (hfL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hfρ : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, f x ∂S.μ ω) :=
  tendstoInProbability_degreeWeightedMeasure_of_ball_random hcell hγ hγ2 hS hα hb hA5 (f := fun _ => f)
    (fun _ => hf) hρ (fun _ => hfK) (fun _ => hfL) (fun _ => hfρ)

end MatedCRT
