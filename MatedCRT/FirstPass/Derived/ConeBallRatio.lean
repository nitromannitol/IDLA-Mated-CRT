import MatedCRT.FirstPass.Derived.ConeBallRatioFar
import MatedCRT.FirstPass.Derived.ConeBallRatioNear
import LatticeProb.LQG.LQGSingularRatioTail
import LatticeProb.LQG.LQGMeasureNonatomicUpper

/-!
# Concentric ball-mass ratio bound for the quantum cone measure

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320v2), Lemma A.2 (p. 66), concentric form: for `0 < c < 1` and `ζ > 0`, with polynomially high
probability as `δ → 0`, every `z ∈ B_{1-δ}(0)` satisfies `δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))`, where
`μ_h` is the γ-LQG measure of the γ-quantum cone field.

The far case `|z| ≥ 3δ` is `polyHighProb_coneBallRatio_far`. The near case `|z| < 3δ` combines the deterministic
step `coneBallRatio_near_le_rpow` with the whole-plane ratio bound at scale `8δ` and the polynomial tail of the
centred singular-weight ratio at a single dyadic radius `r ∈ [4δ, 8δ]`, which does not depend on `z`.
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- A family of events whose complements have probability at most `C δ^p` for small `δ > 0` has polynomially
high probability. -/
lemma polyHighProb_of_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    {p r₀ : ℝ} (hp : 0 < p) (hr₀ : 0 < r₀) (C : ℝ≥0)
    (h : ∀ δ, 0 < δ → δ < r₀ → P (E δ)ᶜ ≤ C * ENNReal.ofReal (δ ^ p)) : PolyHighProb P E := by
  refine ⟨p, hp, C, r₀, hr₀, fun δ hδ hδr => ?_⟩
  rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact h δ hδ hδr

/-- For `0 < δ ≤ 1/16` there is a dyadic radius `r = 2^{-n}/4` with `4δ ≤ r ≤ 8δ`. -/
lemma exists_dyadicScale_quarter_mem {δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) :
    ∃ n : ℕ, 4 * δ ≤ LQG.dyadicScale n * (1 / 4) ∧ LQG.dyadicScale n * (1 / 4) ≤ 8 * δ := by
  have hx : 1 ≤ 1 / (16 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
  have ha : (0 : ℝ) < (2⁻¹) ^ n := by positivity
  have hab : (2⁻¹ : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have habδ : (2⁻¹ : ℝ) ^ n * 2 ^ n * δ = δ := by rw [hab, one_mul]
  have h1 : 2 ^ n * (16 * δ) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hn1
  have h2 : 1 < 2 ^ n * 2 * (16 * δ) := by rwa [pow_succ, div_lt_iff₀ (by positivity)] at hn2
  refine ⟨n, ?_, ?_⟩ <;> unfold LQG.dyadicScale
  · nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]
  · nlinarith [mul_lt_mul_of_pos_left h2 ha]

/-- **Near case of the concentric ball-mass ratio bound for the quantum cone measure** (Berestycki-Gwynne,
arXiv:2003.10320v2, Lemma A.2, p. 66, for `|z| < 3δ`). For `0 < c < 1` and `ζ > 0`, with polynomially high
probability as `δ → 0`, every `z` with `|z| < 3δ` satisfies `δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))`. -/
theorem polyHighProb_coneBallRatio_near {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsConeField γ P hC hcirc μ)
    {c ζ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hζ : 0 < ζ) :
    PolyHighProb P fun δ => {ω | ∀ z : ℂ, ‖z‖ < 3 * δ →
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))} := by
  obtain ⟨hC', hcirc', μ₀, hG, hμ₀, hrep⟩ := exists_coneGFF_singularWeight hγ hγ2 hcone
  have hGL := (LPBridge.isWholePlaneGFF_iff _ _ _).1 hG
  have hμ₀L := (LPBridge.isLQGMeasureOfField_iff _ _ _ _ _).1 hμ₀
  have hμL := LQG.isLQGMeasure_of_isLQGMeasureOfField_zero hμ₀L
  have h0 := LQG.LQGMeasureNonatomicUpper.ae_singleton_eq_zero_of_isWholePlaneGFF hγ hγ2 hGL hμ₀L
  -- the whole-plane ratio bound at scale `8δ`, with `c/8` and `ζ/2`
  have hc8 : 0 < c / 8 := by positivity
  have hW3 := polyHighProb_comp_mul (LQG.LQGBallMassRatioUniform.polyHighProb_ball_ratio hγ hγ2 hc8
    (by linarith) (half_pos hζ) one_pos hGL hμL) (by norm_num : (0 : ℝ) < 8)
  -- the singular-weight tail at one dyadic radius in `[4δ, 8δ]`
  obtain ⟨q, hq, C, hT⟩ := LQG.LQGSingularRatioTail.measure_mul_ball_lt_singular_le hγ hγ2
  have hTail : PolyHighProb (P.prod (brownianMotion 0)) fun δ => {x | ∃ r : ℝ, 4 * δ ≤ r ∧ r ≤ 8 * δ ∧
      ENNReal.ofReal (r ^ (γ ^ 2)) * ∫⁻ y in ball (0 : ℂ) r, ENNReal.ofReal (‖y‖ ^ (-γ ^ 2)) ∂μ₀ x ≤
        ENNReal.ofReal (δ ^ (-(ζ / 4))) * μ₀ x (ball 0 (r / 2))} := by
    refine polyHighProb_of_measure_compl_le (p := ζ / 4 * q) (by positivity)
      (by norm_num : (0 : ℝ) < 1 / 16) C fun δ hδ hδ16 => ?_
    obtain ⟨n, hn4, hn8⟩ := exists_dyadicScale_quarter_mem hδ hδ16.le
    have ht : 1 ≤ δ ^ (-(ζ / 4)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (by linarith) (by linarith)
    refine (measure_mono ?_).trans ((hT _ _ _ _ _ hGL hμL n _ ht).trans_eq ?_)
    · intro x hx
      by_contra hcon
      refine hx ⟨_, hn4, hn8, ?_⟩
      rw [show LQG.dyadicScale n * (1 / 4) / 2 = LQG.dyadicScale n * (1 / 8) by ring]
      exact not_lt.1 hcon
    · rw [← Real.rpow_mul hδ.le]
      congr 3
      ring
  have hW := polyHighProb_inter_ae (polyHighProb_inter hW3 hTail)
    (W := {x | ∀ z : ℂ, μ₀ x {z} = 0}) h0
  have hW' := polyHighProb_inter_ae hW (W := {q | ∀ s : Set ℂ, MeasurableSet s → s ⊆ closedBall 0 1 →
    μ q.1 s = ∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂(μ₀ q)}) hrep
  refine polyHighProb_of_prod_fst (ν := brownianMotion 0) ?_
  refine polyHighProb_mono_of_small hW' (by norm_num : (0 : ℝ) < 1 / 8) fun δ hδ hδ8 x hx => ?_
  obtain ⟨⟨⟨hx3, r, hr4, hr8, hG⟩, hx0⟩, hxrep⟩ := hx
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; linarith
  have hW3z : ENNReal.ofReal ((8 * δ) ^ (γ ^ 2 / 2 + ζ / 2)) * μ₀ x (ball z (8 * δ)) ≤
      μ₀ x (ball z (c * δ)) := by
    have := hx3 z hz1
    rwa [show c / 8 * (8 * δ) = c * δ by ring] at this
  exact coneBallRatio_near_le_rpow hxrep (hx0 0) hδ (by linarith) hζ hc1.le hz hr4 hr8 (by linarith)
    hW3z hG

/-- **Berestycki-Gwynne, Lemma A.2** (arXiv:2003.10320v2, p. 66), concentric form, for the γ-LQG measure `μ_h`
of the γ-quantum cone field. For `0 < c < 1` and `ζ > 0`, with polynomially high probability as `δ → 0`, every
`z ∈ B_{1-δ}(0)` satisfies `δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))`. -/
theorem polyHighProb_coneBallRatio {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsConeField γ P hC hcirc μ)
    {c ζ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hζ : 0 < ζ) :
    PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))} := by
  refine polyHighProb_mono (polyHighProb_inter (polyHighProb_coneBallRatio_far hγ hγ2 hcone hc0 hc1 hζ)
    (polyHighProb_coneBallRatio_near hγ hγ2 hcone hc0 hc1 hζ)) fun δ ω hω z hz => ?_
  obtain ⟨hfar, hnear⟩ := hω
  rcases lt_or_ge ‖z‖ (3 * δ) with h | h
  · exact hnear z h
  · exact hfar z hz h

end MatedCRT.FirstPass.Derived
