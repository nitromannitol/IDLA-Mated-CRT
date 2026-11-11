import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma28

/-!
# Small LQG balls of a whole-plane GFF, uniformly over `B_{1-δ}`

Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations), module
`MatedCRTHarmonic.GMSLemma27.Lemma28` (commit 31e7483, as ported to Lattice-Probability:
`LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma28`), theorem `lemma28_wholePlane_strict`.

Bonanno's theorem bounds `P[∃ z ∈ B_ρ(0), μ(B_δ(z)) ≤ δ^{2+γ²/2+p}]` for a fixed `ρ < 1`. Lemma 2.7 of the paper
ranges over `z ∈ B_{1-δ}`, the radius growing to `1` as `δ → 0`. The same union bound works with `ρ = 1 - δ`: the grid
points `w` of `(δ/4)ℤ²` with `|w| < ρ + δ/4` satisfy `|w| + δ/2 ≤ 1`, which is all that the one-point estimate
`measure_ball_lt_le` ((2.11) of GMS19 with GHM15 Lemma 3.12) needs. The proof below is Bonanno's with `ρ := 1 - δ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT

open MatedCRTHarmonic.GMSLemma27

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- **GMS19 Lemma 2.8 for a whole-plane GFF over `B_{1-δ}`, strict form** (Bonanno's `lemma28_wholePlane_strict`
with `ρ = 1 - δ`). For `γ > 0`, `p > 0` and every `e < p²/(2γ²) − 2` there is `C` with, for all `δ ∈ (0, 1)`,
`P[∃ z ∈ B_{1-δ}(0), μ(B_δ(z)) ≤ δ^{2+γ²/2+p}] ≤ C δ^e`. Input: `GMCLowerTail γ` (proved by Bonanno for
`γ ∈ (0, 2)`: `MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds`). -/
theorem wholePlane_measure_ball_le_unitBall (hGMC : GMCLowerTail γ) (hγ : 0 < γ)
    (hH : LQGDimension.IsGFFCircleAverage H P) (hμ : IsLQGAreaOf γ H μ P) {p e : ℝ} (hp : 0 < p)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ z ∈ ball (0 : ℂ) (1 - δ), μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨θ, hθ0, hθp, heθ⟩ := exists_exponent_lt hp he
  set E : ℝ := θ ^ 2 / (2 * γ ^ 2) with hE
  have hE0 : 0 ≤ E := by positivity
  set ζ : ℝ := (p - θ) / 2 with hζ
  have hζ0 : 0 < ζ := by rw [hζ]; linarith
  set p₁ : ℝ := θ + ζ with hp₁
  have hp₁p : p₁ < p := by rw [hp₁, hζ]; linarith
  set N : ℝ := E / ζ with hN
  have hζN : ζ * N = E := by rw [hN]; field_simp
  have hp₁ζ : p₁ - ζ = θ := by rw [hp₁]; ring
  set x₀ : ℝ := 2 + γ ^ 2 / 2 with hx₀
  have hx₀0 : 0 < x₀ := by positivity
  obtain ⟨r₀, hr₀, hbd⟩ := measure_ball_lt_le (p := p₁) (N := N) hGMC hγ hH hμ hζ0
    (by rw [hp₁]; linarith)
  -- smallness conditions on `δ`
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 := eventually_lt_nhdsGT_zero one_pos
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < r₀ := eventually_lt_nhdsGT_zero hr₀
  have hev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (p - p₁) < (2 : ℝ) ^ (-(x₀ + p₁)) :=
    eventually_rpow_lt (by linarith) (Real.rpow_pos_of_pos two_pos _)
  refine exists_bound_of_eventually (C₀ := 338) (fun δ => prob_le_one) ?_
  filter_upwards [hev1, hev2, hev4, self_mem_nhdsWithin] with δ h1 h2 h4 hδ0
  have hδ0' : 0 < δ := hδ0
  -- the grid absorbs the factor `2^{x₀ + p₁}`
  have habs : δ ^ (x₀ + p) < (δ / 2) ^ (x₀ + p₁) := by
    have e1 : δ ^ (x₀ + p) = δ ^ (x₀ + p₁) * δ ^ (p - p₁) := by
      rw [← Real.rpow_add hδ0']; congr 1; ring
    have e2 : (δ / 2) ^ (x₀ + p₁) = δ ^ (x₀ + p₁) * (2 : ℝ) ^ (-(x₀ + p₁)) := by
      rw [Real.div_rpow hδ0'.le zero_le_two, Real.rpow_neg zero_le_two, div_eq_mul_inv]
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left h4 (Real.rpow_pos_of_pos hδ0' _)
  set S : ℤ × ℤ → Set Ω := fun i =>
    {ω | μ ω (ball (ballGridPt (δ / 4) i) (δ / 2)) < ENNReal.ofReal ((δ / 2) ^ (x₀ + p₁))} with hS
  have hcover : {ω | ∃ z ∈ ball (0 : ℂ) (1 - δ), μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (x₀ + p))} ⊆
      ⋃ i ∈ ballGrid δ (1 - δ), S i := by
    rintro ω ⟨z, hz, hle⟩
    obtain ⟨i, hi, hzi⟩ := exists_mem_ballGrid hδ0' hz
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    have hsub : ball (ballGridPt (δ / 4) i) (δ / 2) ⊆ ball z δ := by
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - z‖ ≤ ‖y - ballGridPt (δ / 4) i‖ + ‖z - ballGridPt (δ / 4) i‖ := by
            calc ‖y - z‖ = ‖(y - ballGridPt (δ / 4) i) - (z - ballGridPt (δ / 4) i)‖ := by ring_nf
              _ ≤ _ := norm_sub_le _ _
        _ < δ := by linarith
    exact (measure_mono hsub).trans_lt
      (hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr habs))
  have hS_le : ∀ i ∈ ballGrid δ (1 - δ), P (S i) ≤ ENNReal.ofReal (2 * δ ^ E) := by
    intro i hi
    have hiw : ‖ballGridPt (δ / 4) i‖ < 1 - δ + δ / 4 := (Finset.mem_filter.mp hi).2
    have hb := hbd (δ / 2) ⟨by positivity, by linarith⟩ (ballGridPt (δ / 4) i) (by linarith)
    rw [hζN, hp₁ζ] at hb
    refine hb.trans ?_
    have hle : (δ / 2) ^ E ≤ δ ^ E := Real.rpow_le_rpow (by positivity) (by linarith) hE0
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcard := card_ballGrid_le hδ0' h1.le (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith : 1 - δ ≤ 1)
  calc P {ω | ∃ z ∈ ball (0 : ℂ) (1 - δ), μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (x₀ + p))}
      ≤ P (⋃ i ∈ ballGrid δ (1 - δ), S i) := measure_mono hcover
    _ ≤ ∑ i ∈ ballGrid δ (1 - δ), P (S i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ ballGrid δ (1 - δ), ENNReal.ofReal (2 * δ ^ E) := Finset.sum_le_sum hS_le
    _ = ENNReal.ofReal ((ballGrid δ (1 - δ)).card * (2 * δ ^ E)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (338 * δ ^ e) := by
        apply ENNReal.ofReal_le_ofReal
        have hδE : δ ^ E / δ ^ 2 ≤ δ ^ e := by
          rw [← Real.rpow_natCast, ← Real.rpow_sub hδ0']
          exact Real.rpow_le_rpow_of_exponent_ge hδ0' h1.le (by push_cast; linarith)
        have hpos : 0 ≤ 2 * δ ^ E := by positivity
        calc ((ballGrid δ (1 - δ)).card : ℝ) * (2 * δ ^ E) ≤ 169 / δ ^ 2 * (2 * δ ^ E) :=
              mul_le_mul_of_nonneg_right hcard hpos
          _ = 338 * (δ ^ E / δ ^ 2) := by ring
          _ ≤ 338 * δ ^ e := by linarith

/-- **The same for a measure dominating `μ` on `B_1`** (Bonanno's `lemma28_strict`, over `B_{1-δ}`): if a.s.
`μ(A) ≤ ν(A)` for every Borel `A ⊆ B_1`, then for all `δ ∈ (0, 1)`,
`P[∃ z ∈ B_{1-δ}(0), ν(B_δ(z)) ≤ δ^{2+γ²/2+p}] ≤ C δ^e`. -/
theorem measure_ball_le_unitBall_of_dominates (hGMC : GMCLowerTail γ) (hγ : 0 < γ)
    (hH : LQGDimension.IsGFFCircleAverage H P) (hμ : IsLQGAreaOf γ H μ P) {ν : Ω → Measure ℂ}
    (hdom : ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 → μ ω A ≤ ν ω A)
    {p e : ℝ} (hp : 0 < p) (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ z ∈ ball (0 : ℂ) (1 - δ), ν ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨C, hC⟩ := wholePlane_measure_ball_le_unitBall hGMC hγ hH hμ hp he
  refine ⟨C, fun δ hδ => le_trans (measure_mono_ae ?_) (hC δ hδ)⟩
  filter_upwards [hdom] with ω hω
  rintro ⟨z, hz, hzle⟩
  refine ⟨z, hz, le_trans (hω _ measurableSet_ball ?_) hzle⟩
  intro y hy
  rw [mem_ball_zero_iff] at hz ⊢
  rw [mem_ball, dist_eq_norm] at hy
  calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
    _ < 1 := by linarith

end MatedCRT
