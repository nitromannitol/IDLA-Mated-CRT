import Mathlib
import MatedCRT.FirstPass.S6e.Cutoff

/-!
# FIRST PASS: the induction of LEMMA68 (C17): `P(H_N) ≤ (1 - q(r))^N` (task fp-S6e-lemma68-C17, z9)

Source: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, C15-C17 (lines 848-884) and the induction there.
The walk is abstract here: `G j` is the exit event of the `j`-th test (`F_j = (G j)ᶜ`), `m j` is the
σ-algebra `F_{T_j}` (monotone in `j`), `H j = ∩_{i<j} F_i` with `H j ∈ m j`. The conditional lower bound of
the exit probability (C15) is the hypothesis `hstep`, with `R j` the random radius of the `j`-th test. The
comparison of C15 with `q(r) = q0/(1+log(1/r))²` (C16) is `q_bound_of_radius`.
-/

open MeasureTheory Set

namespace MatedCRT

namespace Lemma68Induction

/-- One step (C17, first inequality): if `H` is `m`-measurable and the conditional probability of the exit event
`G` given `m` is at least `q` almost surely, then `P(H ∩ Gᶜ) ≤ (1 - q) P(H)`. -/
theorem measureReal_inter_compl_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {H G : Set Ω}
    (hH : MeasurableSet[m] H)
    (hG : MeasurableSet[mΩ] G) {q : ℝ} (hq : ∀ᵐ ω ∂μ, q ≤ (μ[G.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    μ.real (H ∩ Gᶜ) ≤ (1 - q) * μ.real H := by
  have hf : Integrable (G.indicator (fun _ => (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hG
  have hcond := setIntegral_condExp hm hf hH
  have hind : ∫ ω in H, G.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real (H ∩ G) := by
    rw [setIntegral_indicator hG]
    simp
  have hlow : μ.real H * q ≤ ∫ ω in H, (μ[G.indicator (fun _ => (1 : ℝ)) | m]) ω ∂μ := by
    have h : ∫ _ in H, q ∂μ ≤ ∫ ω in H, (μ[G.indicator (fun _ => (1 : ℝ)) | m]) ω ∂μ :=
      setIntegral_mono_ae (integrable_const q).integrableOn integrable_condExp.integrableOn
        (by filter_upwards [hq] with ω hω using hω)
    simpa [setIntegral_const, smul_eq_mul] using h
  have hsplit := measureReal_inter_add_sdiff (μ := μ) hG (s := H)
  rw [Set.sdiff_eq] at hsplit
  linarith

/-- The iteration (C17, the induction giving `P(H_N) ≤ (1-q)^N`): with `H 0 = Ω` and `H (j+1) = H j ∩ (G j)ᶜ`,
where `G j` is `m (j+1)`-measurable, `H j` is `m j`-measurable (monotone filtration `m`), and the conditional exit
probability given `m j` is at least `q ≤ 1` almost surely, `P(H_N) ≤ (1 - q)^N`. -/
theorem measureReal_iterate_le_pow {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hGad : ∀ j, MeasurableSet[m (j + 1)] (G j)) {q : ℝ} (hq1 : q ≤ 1)
    (hcond : ∀ j, ∀ᵐ ω ∂μ, q ≤ (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω)
    (H : ℕ → Set Ω) (hH0 : H 0 = Set.univ) (hHs : ∀ j, H (j + 1) = H j ∩ (G j)ᶜ) :
    ∀ N : ℕ, μ.real (H N) ≤ (1 - q) ^ N := by
  have hmeas : ∀ N, MeasurableSet[m N] (H N) := by
    intro N
    induction N with
    | zero => rw [hH0]; exact MeasurableSet.univ
    | succ N ih =>
      rw [hHs N]
      exact (hmono (Nat.le_succ N) _ ih).inter (hGad N).compl
  intro N
  induction N with
  | zero => simp [hH0]
  | succ N ih =>
    have h := measureReal_inter_compl_le μ (hm N) (hmeas N) (hG N) (hcond N)
    have h1 : 0 ≤ 1 - q := by linarith
    rw [hHs N, pow_succ]
    calc μ.real (H N ∩ (G N)ᶜ) ≤ (1 - q) * μ.real (H N) := h
      _ ≤ (1 - q) * (1 - q) ^ N := mul_le_mul_of_nonneg_left ih h1
      _ = (1 - q) ^ N * (1 - q) := mul_comm _ _

/-- (C15 and C16, real comparison) For `0 < r ≤ 1`, `0 < R ≤ 1` with `r^p/2 < R` and `0 ≤ p ≤ 3`:
`(q*/9)/(1+log(1/r))² ≤ q*/(1+log(1/R))²`. The random radius `R_j` of the write-up satisfies `R_j ≥ δ > r^p/2`. -/
theorem q_bound_of_radius {qStar r p R : ℝ} (hq : 0 ≤ qStar) (hp : p ≤ 3) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hR0 : 0 < R) (hR1 : R ≤ 1) (hRr : r ^ p / 2 < R) :
    qStar / 9 / (1 + Real.log (1 / r)) ^ 2 ≤ qStar / (1 + Real.log (1 / R)) ^ 2 := by
  have ht : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
  have hu : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR0 hR1)
  have e1 : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  have hlog : Real.log (1 / R) < Real.log 2 + p * Real.log (1 / r) := by
    have h1 : 1 / R < 2 / r ^ p := by
      rw [div_lt_div_iff₀ hR0 (by positivity)]
      linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_div (x := 2) (y := r ^ p) (by norm_num) (by positivity), Real.log_rpow hr0] at h2
    rw [e1]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hpt : p * Real.log (1 / r) ≤ 3 * Real.log (1 / r) := mul_le_mul_of_nonneg_right hp ht
  have hu3 : 1 + Real.log (1 / R) ≤ 3 * (1 + Real.log (1 / r)) := by linarith
  have hpos : 0 < 1 + Real.log (1 / R) := by linarith
  have hsq : (1 + Real.log (1 / R)) ^ 2 ≤ 9 * (1 + Real.log (1 / r)) ^ 2 := by
    have := pow_le_pow_left₀ hpos.le hu3 2
    linarith [show (3 * (1 + Real.log (1 / r))) ^ 2 = 9 * (1 + Real.log (1 / r)) ^ 2 by ring]
  rw [div_div]
  exact div_le_div_of_nonneg_left hq (pow_pos hpos 2) hsq

/-- (C17, random radii) The induction with the conditional exit bound of C15 and the radii `R j` of the tests:
almost surely `0 < R j ≤ 1`, `r^p/2 < R j`, and the conditional exit probability given `m j` is at least
`qStar/(1+log(1/R j))²`. Then `P(H_N) ≤ (1 - q0/(1+log(1/r))²)^N` with `q0 = qStar/9` (C16). The hypothesis
`qStar ≤ 9` is the condition `q0 ≤ 1` of the write-up, which is not stated there (N1). -/
theorem C17_le_pow {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hGad : ∀ j, MeasurableSet[m (j + 1)] (G j)) {qStar r p : ℝ} (hq : 0 ≤ qStar) (hq9 : qStar ≤ 9)
    (hp : p ≤ 3) (hr0 : 0 < r) (hr1 : r ≤ 1) (R : ℕ → Ω → ℝ)
    (hR : ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ p / 2 < R j ω)
    (hstep : ∀ j, ∀ᵐ ω ∂μ, qStar / (1 + Real.log (1 / R j ω)) ^ 2 ≤
      (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω)
    (H : ℕ → Set Ω) (hH0 : H 0 = Set.univ) (hHs : ∀ j, H (j + 1) = H j ∩ (G j)ᶜ) (N : ℕ) :
    μ.real (H N) ≤ (1 - qStar / 9 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
  have ht : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
  have hq1 : qStar / 9 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := by
    have h1 : qStar / 9 / (1 + Real.log (1 / r)) ^ 2 ≤ qStar / 9 :=
      div_le_self (by linarith) (by nlinarith)
    linarith
  have hcond : ∀ j, ∀ᵐ ω ∂μ, qStar / 9 / (1 + Real.log (1 / r)) ^ 2 ≤
      (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω := by
    intro j
    filter_upwards [hstep j, hR j] with ω h1 h2
    exact (q_bound_of_radius hq hp hr0 hr1 h2.1 h2.2.1 h2.2.2).trans h1
  exact measureReal_iterate_le_pow μ m hmono hm hG hGad hq1 hcond H hH0 hHs N

/-- (C17 and D1) With the count `N ≥ r^(-ζ)/200` and the cutoff `r ≤ r0` of (D3), the test chain has
`P(H_N) ≤ 1/2` (`Lemma68Cutoff.D1_le_half_of_le_r0`). The constant is `q0 = qStar/9` (C16). -/
theorem C17_le_half {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hGad : ∀ j, MeasurableSet[m (j + 1)] (G j)) {qStar ρ s₀ p b lam cv c0 ζ r : ℝ}
    (hq : 0 < qStar) (hq9 : qStar ≤ 9) (hp : p ≤ 3) (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv)
    (hc0 : 0 < c0) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrr0 : r ≤ Lemma68Cutoff.r0 ρ s₀ p b lam cv c0 (qStar / 9) ζ) (R : ℕ → Ω → ℝ)
    (hR : ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ p / 2 < R j ω)
    (hstep : ∀ j, ∀ᵐ ω ∂μ, qStar / (1 + Real.log (1 / R j ω)) ^ 2 ≤
      (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω)
    (H : ℕ → Set Ω) (hH0 : H 0 = Set.univ) (hHs : ∀ j, H (j + 1) = H j ∩ (G j)ᶜ) {N : ℕ}
    (hN : r ^ (-ζ) / 200 ≤ (N : ℝ)) :
    μ.real (H N) ≤ 1 / 2 := by
  have hpow := C17_le_pow μ m hmono hm hG hGad (le_of_lt hq) hq9 hp hr0 hr1 R hR hstep H hH0 hHs N
  exact hpow.trans (Lemma68Cutoff.D1_le_half_of_le_r0 hρ hs₀ hcv hc0 (div_pos hq (by norm_num))
    (by linarith) hζ hζ' hr0 hrr0 hN)

end Lemma68Induction

end MatedCRT
