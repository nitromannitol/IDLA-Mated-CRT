import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureLipschitz
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Convergence of the degree-weighted measure for continuous test functions on a ball

BG20, Corollary A.6 (Lemma 2.10 of the paper) for a continuous test function `f` vanishing off a ball
`B_ρ`, `ρ < 1`, from the Lipschitz case `tendstoInProbability_degreeWeightedMeasure_of_ball`:

* `exists_lipschitz_approx_of_continuous`: a continuous function vanishing off `B_ρ` is uniformly within
  `θ` of a continuous, bounded, Lipschitz function vanishing off `B_{max ρ 0 + s}` (a smooth uniform
  approximation, `UniformContinuous.exists_contDiff_dist_le`, times a smooth bump function);
* `tendstoInProbability_of_approx`: convergence in probability (outer measure) is stable under uniform
  approximation, when the error is controlled by a family converging in probability to an a.e.
  measurable limit (which is then tight);
* `tendstoInProbability_degreeWeightedMeasure_of_continuous_ball`: the convergence for continuous `f`.
  The error `|∫ (f - f') dμ^ε_h| ≤ θ ∫ g dμ^ε_h` is controlled by a bump `g` equal to `1` where
  `f - f'` lives; `∫ g dμ^ε_h → 6 ∫ g dμ_h` by the Lipschitz case, and `ω ↦ ∫ g dμ_h` is a.e. measurable
  (`frozenLQGTestIntegralMeasurable_holds`).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- A smooth bump function on `ℂ` is Lipschitz. -/
theorem exists_abs_sub_le_of_contDiffBump (φ : ContDiffBump (0 : ℂ)) :
    ∃ L : ℝ, ∀ x y, |φ x - φ y| ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport
    (φ.contDiff (n := 1)) one_ne_zero
  exact ⟨C, fun x y => by simpa [Real.dist_eq, dist_eq_norm] using hC.dist_le_mul x y⟩

/-- **Lipschitz approximation with support control.** A continuous function vanishing off `B_ρ` is
uniformly within `θ` of a continuous, bounded, Lipschitz function vanishing off `B_{max ρ 0 + s}`. -/
theorem exists_lipschitz_approx_of_continuous {f : ℂ → ℝ} (hf : Continuous f) {ρ s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hfρ : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0) :
    ∃ f' : ℂ → ℝ, Continuous f' ∧ (∃ K, ∀ x, |f' x| ≤ K) ∧
      (∃ L, ∀ x y, |f' x - f' y| ≤ L * ‖x - y‖) ∧
      (∀ x ∉ ball (0 : ℂ) (max ρ 0 + s), f' x = 0) ∧ ∀ x, |f x - f' x| ≤ θ := by
  set ρ₀ : ℝ := max ρ 0 with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  have hfρ₀ : ∀ x : ℂ, ρ₀ < ‖x‖ → f x = 0 := fun x hx =>
    hfρ x fun h => by rw [mem_ball_zero_iff] at h; linarith [le_max_left ρ 0]
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ₀)
    fun x hx => hfρ₀ x (by simpa [mem_closedBall_zero_iff, not_le] using hx)
  obtain ⟨Kf, hKf⟩ := (isCompact_closedBall (0 : ℂ) ρ₀).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨g, hg, hgf⟩ := (hfc.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hθ
  let φ : ContDiffBump (0 : ℂ) := ⟨ρ₀ + s / 2, ρ₀ + s, by linarith, by linarith⟩
  have hrIn : φ.rIn = ρ₀ + s / 2 := rfl
  have hrOut : φ.rOut = ρ₀ + s := rfl
  have hφc : ContDiff ℝ 1 (fun x => φ x * g x) := (φ.contDiff (n := 1)).mul (hg.of_le (WithTop.coe_le_coe.2 le_top))
  have hφs : HasCompactSupport (fun x => φ x * g x) := φ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφs hφc one_ne_zero
  have hgx : ∀ x, |g x - f x| < θ := fun x => by simpa [Real.dist_eq] using hgf x
  have hfx : ∀ x, |f x| ≤ max Kf 0 := fun x => by
    by_cases hx : ‖x‖ ≤ ρ₀
    · exact (by simpa [Real.norm_eq_abs] using hKf x (by simpa [mem_closedBall_zero_iff] using hx)
        : |f x| ≤ Kf).trans (le_max_left _ _)
    · rw [hfρ₀ x (not_le.1 hx), abs_zero]; exact le_max_right _ _
  have hφg : ∀ x, |φ x * g x| ≤ |g x| := fun x => by
    rw [abs_mul, abs_of_nonneg φ.nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) φ.le_one
  refine ⟨fun x => φ x * g x, hφc.continuous, ⟨max Kf 0 + θ, fun x => ?_⟩,
    ⟨C, fun x y => by simpa [Real.dist_eq, dist_eq_norm] using hC.dist_le_mul x y⟩, ?_, ?_⟩
  · show |φ x * g x| ≤ max Kf 0 + θ
    have h1 := abs_sub_abs_le_abs_sub (g x) (f x)
    linarith [hφg x, hgx x, hfx x]
  · intro x hx
    have h0 : φ x = 0 := φ.zero_of_le_dist (by
      rw [hrOut, dist_zero_right]; simpa [mem_ball_zero_iff, not_lt] using hx)
    simp [h0]
  · intro x
    show |f x - φ x * g x| ≤ θ
    by_cases hx : ‖x‖ ≤ ρ₀ + s / 2
    · have h1 : φ x = 1 := φ.one_of_mem_closedBall (by rw [hrIn, mem_closedBall_zero_iff]; exact hx)
      rw [h1, one_mul, abs_sub_comm]
      exact (hgx x).le
    · have hf0 : f x = 0 := hfρ₀ x (by linarith [not_le.1 hx])
      have hg0 : |g x| < θ := by simpa [hf0] using hgx x
      rw [hf0, zero_sub, abs_neg]
      exact (hφg x).trans hg0.le

/-- **Stability of convergence in probability under controlled uniform approximation.** Suppose that
for every `θ > 0` there are `X'`, `Y'` with `X' → Y'` in probability, and events `F ε` with
`P(F ε)ᶜ → 0` on which `|X - X'| ≤ θ |G|` and `|Y - Y'| ≤ θ |Z|`, where `G → Z` in probability and `Z`
is a.e. measurable. Then `X → Y` in probability (outer measure; no measurability of `X`, `Y`). -/
theorem tendstoInProbability_of_approx {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X G : ℝ → Ω → ℝ} {Y Z : Ω → ℝ} (hZ : AEMeasurable Z P)
    (hG : TendstoInProbability P G Z)
    (happrox : ∀ θ : ℝ, 0 < θ → ∃ (X' : ℝ → Ω → ℝ) (Y' : Ω → ℝ) (F : ℝ → Set Ω),
      TendstoInProbability P X' Y' ∧ Tendsto (fun ε => P (F ε)ᶜ) (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ F ε, |X ε ω - X' ε ω| ≤ θ * |G ε ω| ∧ |Y ω - Y' ω| ≤ θ * |Z ω|) :
    TendstoInProbability P X Y := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set e₄ : ℝ≥0∞ := e / 2 / 2 with he₄
  have he₄0 : 0 < e₄ := ENNReal.half_pos (ENNReal.half_pos he.ne').ne'
  -- tightness of the a.e. measurable `Z`
  have htight : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < |Z ω|}) atTop (𝓝 0) := by
    have hcongr : ∀ n : ℕ, P {ω | (n : ℝ) < |Z ω|} = P {ω | (n : ℝ) < |hZ.mk Z ω|} := fun n =>
      measure_congr (eventuallyEqSet_iff.2 (hZ.ae_eq_mk.mono fun ω h => by simp only [mem_ofPred_eq, h]))
    simp_rw [hcongr]
    have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℝ) < |hZ.mk Z ω|} P := fun n =>
      (measurableSet_lt measurable_const hZ.measurable_mk.abs).nullMeasurableSet
    have hanti : Antitone fun n : ℕ => {ω | (n : ℝ) < |hZ.mk Z ω|} := fun n m hnm ω (hω : (m : ℝ) < _) =>
      show (n : ℝ) < _ from lt_of_le_of_lt (by exact_mod_cast hnm) hω
    have hempty : (⋂ n : ℕ, {ω | (n : ℝ) < |hZ.mk Z ω|}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact exists_nat_ge _
    have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
    rwa [hempty, measure_empty] at h
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 htight e₄ he₄0).exists
  set M : ℝ := (n : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg n
  set θ : ℝ := δ / (2 * (1 + 2 * M)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθM : θ * (1 + 2 * M) = δ / 2 := by rw [hθ]; field_simp
  obtain ⟨X', Y', F, hX', hF, hb⟩ := happrox θ hθ0
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hX' (δ / 2) (half_pos hδ)) e₄ he₄0,
    ENNReal.tendsto_nhds_zero.1 (hG 1 one_pos) e₄ he₄0, ENNReal.tendsto_nhds_zero.1 hF e₄ he₄0,
    hb] with ε h1 h2 h3 hb
  calc P {ω | δ < |X ε ω - Y ω|}
      ≤ P ((F ε)ᶜ ∪ {ω | δ / 2 < |X' ε ω - Y' ω|} ∪ {ω | 1 < |G ε ω - Z ω|} ∪
          {ω | M < |Z ω|}) := by
        refine measure_mono fun ω hω => ?_
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq] at hω ⊢
        by_contra hc
        push Not at hc
        obtain ⟨⟨⟨hFω, hc1⟩, hc2⟩, hc3⟩ := hc
        obtain ⟨hx, hy⟩ := hb ω hFω
        have hGZ : |G ε ω| ≤ 1 + M := by
          have := abs_sub_abs_le_abs_sub (G ε ω) (Z ω); linarith
        have hkey : θ * |G ε ω| + θ * |Z ω| ≤ θ * (1 + 2 * M) := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hθ0.le
        have t1 := abs_sub_le (X ε ω) (X' ε ω) (Y ω)
        have t2 := abs_sub_le (X' ε ω) (Y' ω) (Y ω)
        rw [abs_sub_comm (Y' ω) (Y ω)] at t2
        linarith
    _ ≤ P (F ε)ᶜ + P {ω | δ / 2 < |X' ε ω - Y' ω|} + P {ω | 1 < |G ε ω - Z ω|} +
          P {ω | M < |Z ω|} := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ e₄ + e₄ + e₄ + e₄ := by gcongr
    _ = e := by rw [he₄, add_assoc, ENNReal.add_halves, ENNReal.add_halves]

/-- `|∫ f - ∫ f'| ≤ θ |∫ g|` when `|f - f'| ≤ θ g` pointwise and all three are integrable. -/
theorem abs_integral_sub_le_mul_abs_integral {ν : Measure ℂ} {f f' g : ℂ → ℝ} {θ : ℝ}
    (hf : Integrable f ν) (hf' : Integrable f' ν) (hg : Integrable g ν) (hθ : 0 ≤ θ)
    (h : ∀ x, |f x - f' x| ≤ θ * g x) :
    |∫ x, f x ∂ν - ∫ x, f' x ∂ν| ≤ θ * |∫ x, g x ∂ν| := by
  rw [← integral_sub hf hf']
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ x, |f x - f' x| ∂ν ≤ ∫ x, θ * g x ∂ν := integral_mono (hf.sub hf').abs (hg.const_mul θ) h
    _ = θ * ∫ x, g x ∂ν := integral_const_mul θ _
    _ ≤ θ * |∫ x, g x ∂ν| := mul_le_mul_of_nonneg_left (le_abs_self _) hθ

private theorem tendsto_rpow_nhdsGT_zero_of_pos' {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h0 : ContinuousAt (fun r : ℝ => r ^ a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h1 : Tendsto (fun r : ℝ => r ^ a) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ a)) :=
    h0.tendsto.mono_left nhdsWithin_le_nhds
  simpa [Real.zero_rpow ha.ne'] using h1

/-- **Corollary A.6 for continuous test functions on a ball, from Lemma A.5** (BG20). Under the
hypotheses of `tendstoInProbability_degreeWeightedMeasure_of_ball` (cell size estimate, two-sided
degree-weighted counting bound of Lemma A.5 on every ball `B_r`, `r < 1`, with polynomially high
probability), for every continuous `f` vanishing off `B_ρ`, `ρ < 1`, `∫ f dμ^ε_h → 6 ∫ f dμ_h` in
probability. -/
theorem tendstoInProbability_degreeWeightedMeasure_of_continuous_ball {𝒮 : SpaceFillingSLEModel}
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
    {f : ℂ → ℝ} (hf : Continuous f) {ρ : ℝ} (hρ : ρ < 1) (hfρ : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, f x ∂S.μ ω) := by
  have := hS.isProbabilityMeasure
  set ρ₀ : ℝ := max ρ 0 with hρ₀
  have hρ₀1 : ρ₀ < 1 := max_lt hρ one_pos
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  set s : ℝ := (1 - ρ₀) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  set r : ℝ := ρ₀ + 2 * s with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr, hs]; linarith
  -- the bump `g`: `1` on `B_{ρ₀ + s}`, `0` off `B_r`
  let φ : ContDiffBump (0 : ℂ) := ⟨ρ₀ + s, r, by linarith, by rw [hr]; linarith⟩
  have hrIn : φ.rIn = ρ₀ + s := rfl
  have hrOut : φ.rOut = r := rfl
  have hgc : Continuous fun x => φ x := φ.continuous
  have hg0 : ∀ x ∉ ball (0 : ℂ) r, φ x = 0 := fun x hx =>
    φ.zero_of_le_dist (by rw [hrOut, dist_zero_right]; simpa [mem_ball_zero_iff, not_lt] using hx)
  have hg1 : ∀ x ∈ ball (0 : ℂ) (ρ₀ + s), φ x = 1 := fun x hx =>
    φ.one_of_mem_closedBall (by rw [hrIn]; exact ball_subset_closedBall hx)
  obtain ⟨Lg, hLg⟩ := exists_abs_sub_le_of_contDiffBump φ
  have hgK : ∀ x, |φ x| ≤ 1 := fun x => by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
  have hG := tendstoInProbability_degreeWeightedMeasure_of_ball hcell hγ hγ2 hS hα hb hA5 hgc hr1
    hgK hLg hg0
  have hZ : AEMeasurable (fun ω => 6 * ∫ x, φ x ∂S.μ ω) S.P :=
    (frozenLQGTestIntegralMeasurable_holds γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ
      ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ _ hgc
      φ.hasCompactSupport).const_mul 6
  -- the event on which the cells meeting `B_r` are finitely many
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq_def
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨c, hc, C, hcov⟩ := hMoT.coverage
  have hcovP : PolyHighProb S.P fun ε =>
      {ω | ball (0 : ℂ) 1 ⊆ η' ω '' Icc (-(ε ^ (-(1 : ℝ)))) (ε ^ (-(1 : ℝ)))} := by
    refine ⟨c * 1, by positivity, C, 1, one_pos, fun ε hε hε1 => ?_⟩
    have hM : 1 < ε ^ (-(1 : ℝ)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by norm_num)
    have h := hcov _ hM
    rw [← Real.rpow_mul hε.le, show -(1 : ℝ) * -c = c * 1 by ring] at h
    exact h
  have hdiam := hcell γ hγ hγ2 q r hq hq1 hr0 hr1 Ω S hS
  have hLQG : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | (IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω) ∧
      IsLocallyFiniteMeasure (S.μ ω)} :=
    (hS.isAreaParametrized.and (hae.mono fun ω h => h.1)).and
      (hLQG.mono fun ω h => h.isLocallyFiniteMeasure)
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ₀)
    fun x hx => hfρ x fun h => hx (ball_subset_closedBall
      (ball_subset_ball (le_max_left ρ 0) h))
  refine tendstoInProbability_of_approx hZ hG fun θ hθ => ?_
  obtain ⟨f', hf'c, ⟨K', hK'⟩, ⟨L', hL'⟩, hf'0, hff'⟩ :=
    exists_lipschitz_approx_of_continuous hf hs0 hθ hfρ
  have hf'cs : HasCompactSupport f' := HasCompactSupport.intro
    (isCompact_closedBall (0 : ℂ) (ρ₀ + s)) fun x hx => hf'0 x fun h => hx (ball_subset_closedBall h)
  have hpt : ∀ x, |f x - f' x| ≤ θ * φ x := fun x => by
    by_cases hx : x ∈ ball (0 : ℂ) (ρ₀ + s)
    · rw [hg1 x hx, mul_one]; exact hff' x
    · have h1 : f x = 0 := hfρ x fun h => hx (ball_subset_ball (by linarith [le_max_left ρ 0]) h)
      rw [h1, hf'0 x hx, sub_zero, abs_zero]
      exact mul_nonneg hθ.le φ.nonneg
  refine ⟨_, _, _, tendstoInProbability_degreeWeightedMeasure_of_ball hcell hγ hγ2 hS hα hb hA5
    hf'c (ρ := ρ₀ + s) (by linarith) hK' hL' hf'0,
    S5c.tendsto_compl_of_polyHighProb ((hdiam.inter hcovP).inter_ae hW), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rpow_nhdsGT_zero_of_pos' hq).eventually_lt_const (show (0 : ℝ) < 1 - r by linarith)]
    with ε hε0 hεq
  rintro ω ⟨⟨hdω, hcω⟩, ⟨hpar, hηω⟩, hlf⟩
  have hε : (0 : ℝ) < ε := hε0
  simp only [mem_ofPred_eq] at hdω hcω
  rw [hηω] at hcω
  have hM : 0 < ε ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hε _
  have hdiam' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 r).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ q := fun k hk => by
    have h := (hdω k hk).2
    rwa [hexp] at h
  obtain ⟨t, ht⟩ :=
    hpar.exists_finset_cellVertices_ball hε hM (show r + ε ^ q < 1 by linarith) hcω hdiam'
  have hint : ∀ u : ℂ → ℝ, Continuous u → (∀ x ∉ ball (0 : ℂ) r, u x = 0) →
      Integrable u (degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω)) := by
    intro u hu hu0
    refine integrable_degreeWeightedMeasure hu hpar.1 t (fun k hk x hx => ?_)
      (fun k _ => hpar.integrableOn_cell hε hu k)
    by_contra hux
    have hxr : x ∈ ball (0 : ℂ) r := by
      by_contra h; exact hux (hu0 x h)
    exact hk ((ht k).2 ⟨x, hx, hxr⟩)
  have hsub : ∀ x ∉ ball (0 : ℂ) r, x ∉ ball (0 : ℂ) (ρ₀ + s) := fun x hx h =>
    hx (ball_subset_ball (by rw [hr]; linarith) h)
  have hρr : ρ ≤ r := by rw [hr]; linarith [le_max_left ρ 0]
  constructor
  · exact abs_integral_sub_le_mul_abs_integral
      (hint f hf fun x hx => hfρ x fun h => hx (ball_subset_ball hρr h))
      (hint f' hf'c fun x hx => hf'0 x (hsub x hx)) (hint _ hgc hg0) hθ.le hpt
  · have := hlf
    have h := abs_integral_sub_le_mul_abs_integral (ν := S.μ ω)
      (hf.integrable_of_hasCompactSupport hfc) (hf'c.integrable_of_hasCompactSupport hf'cs)
      (hgc.integrable_of_hasCompactSupport φ.hasCompactSupport) hθ.le hpt
    rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    calc 6 * |∫ x, f x ∂S.μ ω - ∫ x, f' x ∂S.μ ω| ≤ 6 * (θ * |∫ x, φ x ∂S.μ ω|) := by gcongr
      _ = θ * (6 * |∫ x, φ x ∂S.μ ω|) := by ring

end MatedCRT
