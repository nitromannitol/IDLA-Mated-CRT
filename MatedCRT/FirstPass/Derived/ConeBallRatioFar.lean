import MatedCRT.FirstPass.Derived.ConeMeasureSingularWeight
import LatticeProb.LQG.LQGBallMassRatioUniform
import LatticeProb.LQG.LQGBallMassBoundsOfNegMoment
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# Concentric ball-mass ratios of the quantum cone measure away from the origin

Let `μ_h` be the γ-LQG measure of a γ-quantum cone in its circle average embedding (`IsConeField`, `0 < γ < 2`).
This file proves the far case of the concentric form of Berestycki-Gwynne (arXiv:2003.10320v2), Lemma A.2, p. 66:
for `0 < c < 1` and `ζ > 0`, with polynomially high probability as `δ → 0`,
  `δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))` for every `z ∈ B_{1-δ}(0)` with `|z| ≥ 3δ`
(`polyHighProb_coneBallRatio_far`).

The proof follows the source: on `B̄_1(0)` the cone measure is `|x|^{-γ²} μ₀` with `μ₀` a whole-plane γ-LQG measure
(`exists_coneGFF_singularWeight`). For `|z| ≥ 3δ` the weight `|x|^{-γ²}` varies by a factor at most `2^{γ²}` on
`B_δ(z)` (`setLIntegral_ball_norm_rpow_neg_le`, `le_setLIntegral_ball_norm_rpow_neg`), and the whole-plane bound
for `μ₀` with exponent `γ²/2 + ζ/2` (`LQGBallMassRatioUniform.polyHighProb_ball_ratio`) absorbs this factor into
`δ^{ζ/2}` for small `δ`. The bound holds on the coupled space `Ω × C(ℝ≥0, ℝ)` and transfers to `P` because the
event depends on the first coordinate only (`polyHighProb_of_prod_fst`).
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- On a ball `B_r(z)` with `r < |z|`, the singular weight `|x|^{-a}` (`a ≥ 0`) is at most `(|z| - r)^{-a}`. -/
lemma setLIntegral_ball_norm_rpow_neg_le (ν : Measure ℂ) {a r : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hr : r < ‖z‖) :
    ∫⁻ x in ball z r, ENNReal.ofReal (‖x‖ ^ (-a)) ∂ν ≤
      ENNReal.ofReal ((‖z‖ - r) ^ (-a)) * ν (ball z r) := by
  calc ∫⁻ x in ball z r, ENNReal.ofReal (‖x‖ ^ (-a)) ∂ν
      ≤ ∫⁻ _ in ball z r, ENNReal.ofReal ((‖z‖ - r) ^ (-a)) ∂ν := by
        refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hx' : ‖z - x‖ < r := by rw [mem_ball, dist_eq_norm] at hx; rwa [norm_sub_rev]
        have hzx : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
          simpa using norm_add_le x (z - x)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    _ = _ := setLIntegral_const _ _

/-- On a ball `B_r(z)` with `r < |z|`, the singular weight `|x|^{-a}` (`a ≥ 0`) is at least `(|z| + r)^{-a}`. -/
lemma le_setLIntegral_ball_norm_rpow_neg (ν : Measure ℂ) {a r : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hr : r < ‖z‖) :
    ENNReal.ofReal ((‖z‖ + r) ^ (-a)) * ν (ball z r) ≤
      ∫⁻ x in ball z r, ENNReal.ofReal (‖x‖ ^ (-a)) ∂ν := by
  rw [← setLIntegral_const]
  refine setLIntegral_mono (by fun_prop) fun x hx => ENNReal.ofReal_le_ofReal ?_
  have hx' : ‖x - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hx
  have hzx : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by simpa using norm_add_le x (z - x)
  have hxz : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by simpa using norm_add_le z (x - z)
  rw [norm_sub_rev] at hzx
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

/-- An event of polynomially high probability on a product space with a probability measure in the second factor,
which depends on the first coordinate only, has polynomially high probability for the first factor. -/
lemma polyHighProb_of_prod_fst {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {E : ℝ → Set Ω}
    (h : PolyHighProb (P.prod ν) fun r => Prod.fst ⁻¹' E r) : PolyHighProb P E := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => ?_⟩
  have := hE r hr hrr
  rwa [← preimage_compl, ← prod_univ, Measure.prod_prod, measure_univ, mul_one] at this

/-- **Far case of the concentric ball-mass ratio bound for the quantum cone measure** (Berestycki-Gwynne,
arXiv:2003.10320v2, Lemma A.2, p. 66, for `|z| ≥ 3δ`). For `0 < c < 1` and `ζ > 0`, with polynomially high
probability as `δ → 0`, every `z ∈ B_{1-δ}(0)` with `|z| ≥ 3δ` satisfies
`δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))`. -/
theorem polyHighProb_coneBallRatio_far {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsConeField γ P hC hcirc μ)
    {c ζ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hζ : 0 < ζ) :
    PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ), 3 * δ ≤ ‖z‖ →
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))} := by
  obtain ⟨hC', hcirc', μ₀, hG, hμ₀, hrep⟩ := exists_coneGFF_singularWeight hγ hγ2 hcone
  have hW3 := LQG.LQGBallMassRatioUniform.polyHighProb_ball_ratio hγ hγ2 hc0 hc1 (half_pos hζ) one_pos
    ((LPBridge.isWholePlaneGFF_iff _ _ _).1 hG)
    (LQG.isLQGMeasure_of_isLQGMeasureOfField_zero ((LPBridge.isLQGMeasureOfField_iff _ _ _ _ _).1 hμ₀))
  have hW := polyHighProb_inter_ae hW3 (W := {q | ∀ s : Set ℂ, MeasurableSet s → s ⊆ closedBall 0 1 →
    μ q.1 s = ∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂(μ₀ q)}) hrep
  refine polyHighProb_of_prod_fst (ν := brownianMotion 0) ?_
  set a : ℝ := γ ^ 2 with ha_def
  have ha : 0 ≤ a := sq_nonneg γ
  have hζ2 : 0 < ζ / 2 := half_pos hζ
  -- the scale below which `δ^{ζ/2} ≤ 2^{-a}`
  set r₁ : ℝ := (2 : ℝ) ^ (-(2 * a / ζ)) with hr₁_def
  have hr₁ : 0 < r₁ := Real.rpow_pos_of_pos two_pos _
  refine polyHighProb_mono_of_small hW hr₁ fun δ hδ hδr₁ q hq => ?_
  obtain ⟨hq3, hqrep⟩ := hq
  intro z hz hz3
  have hz1 : ‖z‖ < 1 - δ := by simpa using hz
  have hzδ : δ < ‖z‖ := by linarith
  have hcδ : c * δ ≤ δ := by nlinarith
  have hcδpos : 0 < c * δ := mul_pos hc0 hδ
  have hsub : ball z δ ⊆ closedBall (0 : ℂ) 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hxz : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by simpa using norm_add_le z (x - z)
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hsubc : ball z (c * δ) ⊆ ball z δ := ball_subset_ball hcδ
  have hμδ : μ q.1 (ball z δ) ≤ ENNReal.ofReal ((‖z‖ - δ) ^ (-a)) * μ₀ q (ball z δ) := by
    rw [hqrep _ measurableSet_ball hsub]
    exact setLIntegral_ball_norm_rpow_neg_le _ ha hzδ
  have hμcδ : ENNReal.ofReal ((‖z‖ + c * δ) ^ (-a)) * μ₀ q (ball z (c * δ)) ≤ μ q.1 (ball z (c * δ)) := by
    rw [hqrep _ measurableSet_ball (hsubc.trans hsub)]
    exact le_setLIntegral_ball_norm_rpow_neg _ ha (hcδ.trans_lt hzδ)
  have hW3z := hq3 z (by rw [mem_ball, dist_zero_right]; linarith)
  -- the real inequality `(|z| - δ)^{-a} δ^{ζ/2} ≤ (|z| + cδ)^{-a}`
  have hδζ : δ ^ (ζ / 2) ≤ (2 : ℝ) ^ (-a) := by
    calc δ ^ (ζ / 2) ≤ r₁ ^ (ζ / 2) := Real.rpow_le_rpow hδ.le hδr₁.le hζ2.le
      _ = (2 : ℝ) ^ (-a) := by
        rw [hr₁_def, ← Real.rpow_mul two_pos.le]
        congr 1
        field_simp
  have hreal : (‖z‖ - δ) ^ (-a) * δ ^ (ζ / 2) ≤ (‖z‖ + c * δ) ^ (-a) := by
    have hzδ' : 0 < ‖z‖ - δ := by linarith
    calc (‖z‖ - δ) ^ (-a) * δ ^ (ζ / 2) ≤ (‖z‖ - δ) ^ (-a) * (2 : ℝ) ^ (-a) :=
          mul_le_mul_of_nonneg_left hδζ (Real.rpow_nonneg hzδ'.le _)
      _ = (2 * (‖z‖ - δ)) ^ (-a) := by rw [Real.mul_rpow two_pos.le hzδ'.le, mul_comm]
      _ ≤ (‖z‖ + c * δ) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hsplit : δ ^ (a / 2 + ζ) = δ ^ (ζ / 2) * δ ^ (a / 2 + ζ / 2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ q.1 (ball z δ)
      ≤ ENNReal.ofReal (δ ^ (a / 2 + ζ)) *
          (ENNReal.ofReal ((‖z‖ - δ) ^ (-a)) * μ₀ q (ball z δ)) := mul_le_mul' le_rfl hμδ
    _ = ENNReal.ofReal ((‖z‖ - δ) ^ (-a) * δ ^ (ζ / 2)) *
          (ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ / 2)) * μ₀ q (ball z δ)) := by
        rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
        ring
    _ ≤ ENNReal.ofReal ((‖z‖ + c * δ) ^ (-a)) * μ₀ q (ball z (c * δ)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) hW3z
    _ ≤ μ q.1 (ball z (c * δ)) := hμcδ

end MatedCRT.FirstPass.Derived
