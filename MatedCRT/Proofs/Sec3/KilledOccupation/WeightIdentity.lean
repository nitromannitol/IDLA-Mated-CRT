import Mathlib

/-!
# Mass bound and weight identity for the disk occupation clock (Appendix B, step S2)

Source: `paper/appendix-occupation-C16.tex`, eq:occ-mass (lines 245-250) and eq:occ-weight (lines 256-258).
The input eq:occ-BGmass (lines 110-115, labelled an exact input, locator not pinned in the paper) enters
as the Prop `BGMassUpperBoundDyadic`. The paper's argument for eq:occ-mass is "apply eq:occ-BGmass at dyadic
radii and use Borel-Cantelli and monotonicity" (lines 245-250); it is carried out in
`ae_ballMass_le_rpow` below. The weight identity eq:occ-weight is kept as the Prop `OccWeightIdentity`:
its proof (lines 252-255, local convergence away from `0` and a countable exhaustion) is not written in the
paper as an argument.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal

namespace MatedCRT.KilledOccupation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The dyadic radii `δ_k = 2^{-(k+1)}` used in the Borel-Cantelli argument (tex:245-250). -/
def dyadicRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)

lemma dyadicRadius_pos (k : ℕ) : 0 < dyadicRadius k := by
  unfold dyadicRadius
  positivity

lemma dyadicRadius_succ (k : ℕ) : dyadicRadius (k + 1) = dyadicRadius k / 2 := by
  unfold dyadicRadius
  rw [pow_succ]
  ring

lemma dyadicRadius_antitone : Antitone dyadicRadius := by
  intro m n hmn
  unfold dyadicRadius
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma dyadicRadius_rpow (p : ℝ) (k : ℕ) :
    dyadicRadius k ^ p = ((1 / 2 : ℝ) ^ p) ^ (k + 1) := by
  unfold dyadicRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (x := (1 / 2 : ℝ)) (by norm_num), mul_comm,
    Real.rpow_mul (x := (1 / 2 : ℝ)) (by norm_num), Real.rpow_natCast]

/-- The upper half of eq:occ-BGmass (tex:110-115) at the dyadic radii, with exponent `e`:
for each `k`, the probability that `μ(B_{δ_k}(v)) ≤ δ_k^e` fails for some `v ∈ B_{1-δ_k}` is at most
`C δ_k^p`. The paper states this with "polynomially high probability as δ↓0" (tex:110-115); the rate
`p > 0` is made explicit here as a hypothesis. Source: `paper/appendix-occupation-C16.tex:108-121`
(exact input; the lower bound of eq:occ-BGmass is not needed for eq:occ-mass). -/
def BGMassUpperBoundDyadic (P : Measure Ω) (μ : Ω → Measure ℂ) (e : ℝ) : Prop :=
  ∃ p C : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ k : ℕ,
    P {ω | ¬ ∀ v ∈ ball (0 : ℂ) (1 - dyadicRadius k),
        μ ω (ball v (dyadicRadius k)) ≤ ENNReal.ofReal (dyadicRadius k ^ e)}
      ≤ ENNReal.ofReal (C * dyadicRadius k ^ p)

/-- The weight identity eq:occ-weight (tex:256-258): on `B_1`, `μ_h(dx) = |x|^{-γ²} ν(dx)`, and
`μ_h({0}) = 0`. `ν ω` is the nonsingular regularization of the circle-average clock (tex:122-140; not
formalized here). The paper's proof (tex:252-255) is not written as an argument; this Prop is a hypothesis of
its consumers. -/
def OccWeightIdentity (P : Measure Ω) (μ ν : Ω → Measure ℂ) (γ : ℝ) : Prop :=
  ∀ᵐ ω ∂P, μ ω {0} = 0 ∧ ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 →
    μ ω A = ∫⁻ x in A, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂(ν ω)

/-- **eq:occ-mass** (tex:245-250). Assume the upper eq:occ-BGmass bound with exponent `e > 0`.
Then almost surely there are `C, r₀ > 0` with `μ(B_a(v)) ≤ C a^e` for all `v ∈ B_{ρ₁}` and `0 < a < r₀`.
The paper's exponent `b ∈ (0, (2-γ)²/2)` is `e` here. Proof: Borel-Cantelli on the dyadic failure events,
then monotonicity in the radius (tex:245-250). -/
theorem ae_ballMass_le_rpow (P : Measure Ω) (μ : Ω → Measure ℂ) {e ρ₁ : ℝ} (he : 0 < e)
    (hρ₁ : ρ₁ < 1) (hBG : BGMassUpperBoundDyadic P μ e) :
    ∀ᵐ ω ∂P, ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ v ∈ ball (0 : ℂ) ρ₁, ∀ a : ℝ, 0 < a → a < r₀ →
      μ ω (ball v a) ≤ ENNReal.ofReal (C * a ^ e) := by
  obtain ⟨p, C, hp, hC, hfail⟩ := hBG
  set E : ℕ → Set Ω := fun k => {ω | ¬ ∀ v ∈ ball (0 : ℂ) (1 - dyadicRadius k),
      μ ω (ball v (dyadicRadius k)) ≤ ENNReal.ofReal (dyadicRadius k ^ e)} with hE
  have hgeo : Summable (fun k : ℕ => C * dyadicRadius k ^ p) := by
    have hr0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := by positivity
    have hr1 : (1 / 2 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left (C * (1 / 2 : ℝ) ^ p)
    refine h.congr (fun k => ?_)
    rw [dyadicRadius_rpow]
    ring
  have hsum : ∑' k, P (E k) ≠ ∞ := by
    have hle : ∑' k, P (E k) ≤ ∑' k, ENNReal.ofReal (C * dyadicRadius k ^ p) :=
      ENNReal.tsum_le_tsum fun k => hfail k
    have heq : ∑' k, ENNReal.ofReal (C * dyadicRadius k ^ p)
        = ENNReal.ofReal (∑' k, C * dyadicRadius k ^ p) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun k => mul_nonneg hC (Real.rpow_nonneg (dyadicRadius_pos k).le _)) hgeo).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle.trans heq.le)
  have hBC : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E k := ae_eventually_notMem hsum
  filter_upwards [hBC] with ω hω
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hω
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 - ρ₁ by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set k₁ : ℕ := max k₀ n with hk₁def
  have hk₁₀ : k₀ ≤ k₁ := le_max_left _ _
  have hδ₁ : dyadicRadius k₁ ≤ 1 - ρ₁ := by
    have h1 : (1 / 2 : ℝ) ^ (k₁ + 1) ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := le_max_right k₀ n; omega)
    exact le_trans h1 hn.le
  refine ⟨2 ^ e, dyadicRadius k₁, dyadicRadius_pos k₁, ?_⟩
  intro v hv a ha hae
  have hex : ∃ m : ℕ, dyadicRadius m < a := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ha (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨m, lt_of_le_of_lt ?_ hm⟩
    unfold dyadicRadius
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, dyadicRadius m < a ∧ ∀ j < m, a ≤ dyadicRadius j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_lt.1 (Nat.find_min hex hj)⟩
  have hm_gt : k₁ < m := by
    by_contra h
    rw [not_lt] at h
    have := dyadicRadius_antitone h
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk1k : k₁ ≤ k := by omega
  have hak : a ≤ dyadicRadius k := hmin k (by omega)
  have hgood : ∀ v ∈ ball (0 : ℂ) (1 - dyadicRadius k),
      μ ω (ball v (dyadicRadius k)) ≤ ENNReal.ofReal (dyadicRadius k ^ e) := by
    have h := hk₀ k (le_trans hk₁₀ hk1k)
    simpa [hE] using h
  have hv' : v ∈ ball (0 : ℂ) (1 - dyadicRadius k) := by
    have hanti := dyadicRadius_antitone hk1k
    rw [mem_ball, dist_zero_right] at hv ⊢
    linarith
  have hδk : dyadicRadius k ≤ 2 * a := by
    have h2 : dyadicRadius k = 2 * dyadicRadius (k + 1) := by
      rw [dyadicRadius_succ]; ring
    linarith
  calc μ ω (ball v a) ≤ μ ω (ball v (dyadicRadius k)) := measure_mono (ball_subset_ball hak)
    _ ≤ ENNReal.ofReal (dyadicRadius k ^ e) := hgood v hv'
    _ ≤ ENNReal.ofReal (2 ^ e * a ^ e) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.mul_rpow (by norm_num) ha.le]
      exact Real.rpow_le_rpow (dyadicRadius_pos k).le hδk he.le

end MatedCRT.KilledOccupation
