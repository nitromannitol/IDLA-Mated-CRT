import MatedCRT.FirstPass.S6p
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Counting
import MatedCRT.Proofs.Field.LawTransferComplete

/-!
# Short-window good-radius prevalence (PRO step 3, `short_window_good_radius_prevalence`; chat 188 S2.3)

For `0 < a < 1` and a small `d ∈ (0,1)`, the candidate radii are the seven-adic points of the short window
`[d, d^a]` (`shortWindowRadii`), and the eligible centres are the grid points `(d/100) ℤ²` in
`B_{ρ-3s} \ B_{10s}`, `s = d^a` (`shortEligible`). The good event is the [C5]-corrected annulus event
`IsGoodAnnulusEvent` used by `firstPass_6_4_uniform` (`S6p.lean`).

`ShortWindowGoodRadiusPrevalenceStmt` says: `P(∃ z eligible, no candidate radius is good at z) ≤ C' d⁶`.
The proof is the annulus-iteration argument of `goodAnnulusPrevalence_uniform_of_steps` (S6p.lean), with the window
and rate changed:
* radii `r_k = 7^{-(s+2k)}`, `s = ⌈a L / log 7⌉` (`L = log(1/d)`), `1 ≤ k ≤ K`, `K = ⌊(L/log 7 - s)/2⌋`. These are
  seven-adic points of `[d, d^a]` with ratio `1/49`, so the annulus inputs `(r/3, 3r)` and `s₁ = 1/12` of S6p apply
  unchanged. This subfamily of the PRO radii (ratio `1/7`) is what those inputs require; any good radius found in it is
  a good radius of `[d, d^a]`.
* rate `α = 16 log 7 / (1-a)`: `K ≥ (1-a) L / (2 log 7) - 3/2`, so `α K ≥ 8L - 24 log 7/(1-a)` and
  `exp(-α K) ≤ exp(24 log 7/(1-a)) d⁸` (PRO's `α_mix = 8 log 7/(1-a)` on the seven-adic scales gives the same `d⁸`).
* grid: `|Z_d| ≤ (201/d)²`, union bound over `Z_d`, giving `C' d⁶`.

Named inputs (hypotheses, as in S6p): the annulus-iteration statement `AnnulusIterateStmt` (Draft/Section6), the
one-annulus hit bound `AnnulusHitUniformStmt` (S6p; the chat's "choose `C_G` so that the one-annulus probability exceeds
`p(α_mix)`"), the cone transfer `AnnulusIterateConeTransferStep` and the locality `GoodAnnulusEventLocalityStep`.
Borel-Cantelli (the random cutoff `d_*(h)` of PRO step 3) is in `shortWindow_borel_cantelli`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, annulus iteration), Berestycki-Powell and Duplantier-Sheffield (LQG
measure, cone fields), Armitage-Gardiner (potential theory).
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

/-- The first exponent `s = ⌈a L / log 7⌉` of the short window, `L = log(1/d) = -log d`. -/
noncomputable def shortStart (d a : ℝ) : ℕ := ⌈a * (-Real.log d) / Real.log 7⌉₊

/-- The number `K = ⌊(L/log 7 - s)/2⌋` of candidate radii used by the annulus iteration. -/
noncomputable def shortCount (d a : ℝ) : ℕ :=
  ⌊((-Real.log d) / Real.log 7 - (shortStart d a : ℝ)) / 2⌋₊

/-- The radii `r_k = 7^{-(s + 2k)}`. -/
noncomputable def shortRadius (d a : ℝ) (k : ℕ) : ℝ := (7 : ℝ)⁻¹ ^ (shortStart d a + 2 * k)

/-- The seven-adic radii of the short window `[d, d^a]` (PRO step 3, `ℛ_d`). -/
def shortWindowRadii (d a : ℝ) : Set ℝ := {r | (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ d ≤ r ∧ r ≤ d ^ a}

/-- The eligible centres `Z_d = (d/100) ℤ² ∩ (B_{ρ-3s} \ B_{10s})`, `s = d^a` (PRO step 3). -/
def shortEligible (ρ d a : ℝ) : Set ℂ :=
  {z | z ∈ ball (0 : ℂ) (ρ - 3 * d ^ a) \ ball 0 (10 * d ^ a) ∧
    ∃ m n : ℤ, z = ((d / 100 : ℝ) : ℂ) * (m + n * Complex.I)}

/-- **PRO step 3** (`short_window_good_radius_prevalence`): for every `a ∈ (0,1)`, `γ`, `c₀`, there are `C` (the
constant of the good event) and `C'` such that, for every whole-plane cone field, every `ρ ∈ (0,1)` and every
`d ∈ (0,1)`, the probability that some eligible centre has no good seven-adic radius in `[d, d^a]` is at most `C' d⁶`. -/
def ShortWindowGoodRadiusPrevalenceStmt : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 →
  ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ d : ℝ, 0 < d → d < 1 →
    P {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
        ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} ≤ ENNReal.ofReal (C' * d ^ 6)

lemma log_seven_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)

lemma neg_log_nonneg {d : ℝ} (hd : 0 < d) (hd1 : d < 1) : 0 ≤ -Real.log d := by
  have := Real.log_neg hd hd1
  linarith

lemma shortRadius_pos (d a : ℝ) (k : ℕ) : 0 < shortRadius d a k := by
  unfold shortRadius
  positivity

lemma shortRadius_succ (d a : ℝ) (k : ℕ) : shortRadius d a (k + 1) = shortRadius d a k / 49 := by
  unfold shortRadius
  rw [show shortStart d a + 2 * (k + 1) = (shortStart d a + 2 * k) + 2 by ring, pow_add]
  norm_num [div_eq_mul_inv]

/-- The radii lie below the top of the window: `r_k ≤ d^a`. -/
lemma shortRadius_le_rpow {d a : ℝ} (hd : 0 < d) (hd1 : d < 1) (ha : 0 < a) (k : ℕ) :
    shortRadius d a k ≤ d ^ a := by
  have hX : 0 ≤ a * (-Real.log d) := mul_nonneg ha.le (neg_log_nonneg hd hd1)
  have hs : a * (-Real.log d) / Real.log 7 ≤ (shortStart d a : ℝ) := Nat.le_ceil _
  rw [← Real.log_le_log_iff (shortRadius_pos d a k) (Real.rpow_pos_of_pos hd a)]
  unfold shortRadius
  rw [Real.log_pow, Real.log_inv, Real.log_rpow hd]
  have h1 : a * (-Real.log d) ≤ (shortStart d a : ℝ) * Real.log 7 := by
    have := mul_le_mul_of_nonneg_right hs log_seven_pos.le
    rwa [div_mul_cancel₀ _ log_seven_pos.ne'] at this
  have h2 : (shortStart d a : ℝ) ≤ ((shortStart d a + 2 * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  push_cast at h2 ⊢
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg (sub_nonneg.2 h2) log_seven_pos.le, mul_nonneg hk0 log_seven_pos.le]

/-- The radii `r_k`, `1 ≤ k ≤ K`, lie above `d`. -/
lemma shortRadius_ge {d a : ℝ} (hd : 0 < d) (k : ℕ) (hk1 : 1 ≤ k) (hK : k ≤ shortCount d a) :
    d ≤ shortRadius d a k := by
  have hk : (k : ℝ) ≤ ((-Real.log d) / Real.log 7 - (shortStart d a : ℝ)) / 2 := by
    unfold shortCount at hK
    exact (Nat.le_floor_iff' (by omega)).1 hK
  have hl7 : Real.log 7 ≠ 0 := log_seven_pos.ne'
  have e : ((-Real.log d) / Real.log 7 - (shortStart d a : ℝ)) / 2 * (2 * Real.log 7) =
      -Real.log d - (shortStart d a : ℝ) * Real.log 7 := by
    field_simp
  have h := mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ 2 * Real.log 7)
  rw [e] at h
  have key : ((shortStart d a : ℝ) + 2 * k) * Real.log 7 ≤ -Real.log d := by nlinarith
  rw [← Real.log_le_log_iff hd (shortRadius_pos d a k)]
  unfold shortRadius
  rw [Real.log_pow, Real.log_inv]
  push_cast
  nlinarith

/-- The count bound `K ≥ (1-a) L / (2 log 7) - 3/2` (PRO step 3: `K(d) ≥ (1-a) log(1/d)/log 7 - 2`, on even scales). -/
lemma shortCount_ge {d a : ℝ} (hd : 0 < d) (hd1 : d < 1) (ha : 0 < a) :
    (1 - a) * (-Real.log d) / (2 * Real.log 7) - 3 / 2 ≤ (shortCount d a : ℝ) := by
  have hX : 0 ≤ a * (-Real.log d) / Real.log 7 :=
    div_nonneg (mul_nonneg ha.le (neg_log_nonneg hd hd1)) log_seven_pos.le
  have hs : (shortStart d a : ℝ) < a * (-Real.log d) / Real.log 7 + 1 := Nat.ceil_lt_add_one hX
  have hK : ((-Real.log d) / Real.log 7 - (shortStart d a : ℝ)) / 2 - 1 < (shortCount d a : ℝ) := by
    unfold shortCount
    exact Nat.sub_one_lt_floor _
  have hl7 : Real.log 7 ≠ 0 := log_seven_pos.ne'
  have e : (1 - a) * (-Real.log d) / (2 * Real.log 7) =
      ((-Real.log d) / Real.log 7 - a * (-Real.log d) / Real.log 7) / 2 := by
    field_simp
    ring
  linarith

/-- The exponential bound `exp(-α K) ≤ exp(24 log 7/(1-a)) d⁸` with `α = 16 log 7/(1-a)` (PRO: `C e^{-α K} ≤ C' d⁸`). -/
lemma exp_shortCount_le {d a : ℝ} (hd : 0 < d) (hd1 : d < 1) (ha : 0 < a) (ha1 : a < 1) :
    Real.exp (-(16 * Real.log 7 / (1 - a)) * (shortCount d a : ℝ)) ≤
      Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 8 := by
  have hαpos : 0 < 16 * Real.log 7 / (1 - a) :=
    div_pos (by linarith [log_seven_pos]) (by linarith)
  have hK := shortCount_ge hd hd1 ha
  have h1 : -(16 * Real.log 7 / (1 - a)) * (shortCount d a : ℝ) ≤
      -(16 * Real.log 7 / (1 - a)) * ((1 - a) * (-Real.log d) / (2 * Real.log 7) - 3 / 2) := by
    have := mul_le_mul_of_nonneg_left hK hαpos.le
    linarith
  have h1a : (1 - a) ≠ 0 := (sub_pos.2 ha1).ne'
  have hl7 : Real.log 7 ≠ 0 := log_seven_pos.ne'
  have h2 : -(16 * Real.log 7 / (1 - a)) * ((1 - a) * (-Real.log d) / (2 * Real.log 7) - 3 / 2) =
      8 * Real.log d + 24 * Real.log 7 / (1 - a) := by
    field_simp
    ring
  have hexp8 : Real.exp (8 * Real.log d) = d ^ 8 := by
    rw [show (8 : ℝ) * Real.log d = ((8 : ℕ) : ℝ) * Real.log d by norm_num, Real.exp_nat_mul,
      Real.exp_log hd]
  calc Real.exp (-(16 * Real.log 7 / (1 - a)) * (shortCount d a : ℝ))
      ≤ Real.exp (8 * Real.log d + 24 * Real.log 7 / (1 - a)) := Real.exp_le_exp.2 (h1.trans (le_of_eq h2))
    _ = Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 8 := by
      rw [Real.exp_add, hexp8, mul_comm]

lemma card_shortGrid (M : ℕ) :
    ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).card = (2 * M + 1) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc, show ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 by omega]
  ring

/-- **Borel-Cantelli form of PRO step 3** (the random cutoff): if the bad events have summable probabilities along the
dyadic scales, then almost surely only finitely many dyadic scales are bad. -/
theorem shortWindow_borel_cantelli {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℕ → Set Ω)
    (hsum : ∑' k : ℕ, P (B k) ≠ ⊤) : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ B k :=
  ae_eventually_notMem hsum

/-- **PRO step 3 (short-window good-radius prevalence)**, from the named annulus inputs of S6p. -/
theorem shortWindow_prevalence_of_steps (h66 : AnnulusIterateStmt) (h65 : FirstPass64.AnnulusHitUniformStmt)
    (hT : AnnulusIterateConeTransferStep) (hL : GoodAnnulusEventLocalityStep) :
    ShortWindowGoodRadiusPrevalenceStmt := by
  intro a ha ha1 γ hγ hγ2 c₀ hc₀ hc₀'
  have hαpos : 0 < 16 * Real.log 7 / (1 - a) := div_pos (by linarith [log_seven_pos]) (by linarith)
  obtain ⟨p, C₆, hp, hp1, hC₆, hiter⟩ :=
    hT h66 (1 / 12) (3 / 4) (by norm_num) (by norm_num) (by norm_num) _ hαpos
  obtain ⟨C, hCpos, hhitU⟩ := h65 γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  refine ⟨C, 201 ^ 2 * C₆ * Real.exp (24 * Real.log 7 / (1 - a)),
    hCpos, mul_pos (mul_pos (by norm_num) hC₆) (Real.exp_pos _), ?_⟩
  intro ρ hρ hρ1 Ω _ P hC hcirc μ hcone
  have : IsProbabilityMeasure P := hcone.1
  have hhit := hhitU ρ hρ hρ1
  intro d hd hd1
  set K : ℕ := shortCount d a with hKdef
  set reg : Set ℂ := ball (0 : ℂ) (ρ - 3 * d ^ a) \ ball 0 (10 * d ^ a) with hreg
  set M : ℕ := ⌊100 / d⌋₊ with hMdef
  set S : Finset (ℤ × ℤ) := (Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M) with hS
  -- the one-point bound from the annulus iteration (S6p `hpoint`, with the short window)
  have hpoint : ∀ z ∈ reg, P {ω | ∀ k ∈ Finset.Icc 1 K,
      ω ∉ {ω | IsGoodAnnulusEvent (μ ω) c₀ C (shortRadius d a k) z}} ≤
        ENNReal.ofReal (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ))) := by
    intro z hz
    have hadm : ∀ k, annulus z (shortRadius d a k / 3) (3 * shortRadius d a k) ⊆ ball 0 ρ ∧
        shortRadius d a k / 100 ≤ infDist 0 (annulus z (shortRadius d a k / 3) (3 * shortRadius d a k)) :=
      fun k => annulus_region_admissible (shortRadius_pos d a k) (shortRadius_le_rpow hd hd1 ha k) hz
    have hann : ∀ k, annulus z (1 / 12 * (4 * shortRadius d a k)) (3 / 4 * (4 * shortRadius d a k)) =
        annulus z (shortRadius d a k / 3) (3 * shortRadius d a k) := by
      intro k
      congr 1 <;> ring
    refine hiter γ hγ hγ2 Ω P hC hcirc μ hcone z (fun k => 4 * shortRadius d a k)
      (fun k => {ω | IsGoodAnnulusEvent (μ ω) c₀ C (shortRadius d a k) z}) ?_ ?_ ?_ ?_ ?_ ?_ K
    · refine antitone_nat_of_succ_le fun k => ?_
      show 4 * shortRadius d a (k + 1) ≤ 4 * shortRadius d a k
      rw [shortRadius_succ]
      linarith [shortRadius_pos d a k]
    · intro k
      show 0 < 4 * shortRadius d a k
      linarith [shortRadius_pos d a k]
    · intro k
      show 4 * shortRadius d a (k + 1) / (4 * shortRadius d a k) ≤ 1 / 12
      rw [shortRadius_succ, div_le_iff₀ (by linarith [shortRadius_pos d a k])]
      linarith [shortRadius_pos d a k]
    · intro k
      show annulus z (1 / 12 * (4 * shortRadius d a k)) (3 / 4 * (4 * shortRadius d a k)) ⊆ ball 0 1
      rw [hann k]
      exact (hadm k).1.trans (ball_subset_ball hρ1.le)
    · intro k
      show ∃ E' : Set Ω, MeasurableSet[modConstSigma hC
          (annulus z (1 / 12 * (4 * shortRadius d a k)) (3 / 4 * (4 * shortRadius d a k)))] E' ∧
          {ω | IsGoodAnnulusEvent (μ ω) c₀ C (shortRadius d a k) z} =ᵐ[P] E'
      rw [hann k]
      exact hL γ hγ hγ2 c₀ hc₀ hc₀' C hCpos Ω P hC hcirc μ hcone (shortRadius d a k) z
        (shortRadius_pos d a k) ((hadm k).1.trans (ball_subset_ball hρ1.le))
    · intro k
      exact ofReal_le_measure_of_compl_le hp.le hp1.le
        (hhit Ω P hC hcirc μ hcone (shortRadius d a k) z (shortRadius_pos d a k) (hadm k).1 (hadm k).2)
  -- the bad events on the grid cells
  set B : ℤ × ℤ → Set Ω := fun x => {ω | ((d / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I) ∈ reg ∧
    ∀ k ∈ Finset.Icc 1 K, ¬ IsGoodAnnulusEvent (μ ω) c₀ C (shortRadius d a k)
      (((d / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I))} with hBdef
  have hsub : {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
      ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} ⊆ ⋃ x ∈ S, B x := by
    intro ω hω
    rw [mem_ofPred_eq] at hω
    obtain ⟨z, hzE, hno⟩ := hω
    obtain ⟨hz, m, n, rfl⟩ := hzE
    have hz1 : ‖((d / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ < 1 := by
      have h := hz.1
      rw [mem_ball, dist_zero_right] at h
      have : 0 ≤ d ^ a := by positivity
      linarith
    refine mem_iUnion₂.2 ⟨(m, n), Finset.mem_product.2 (grid_mem_Icc hd hz1), hz, fun k hk hE => ?_⟩
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.1 hk
    exact hno (shortRadius d a k) ⟨⟨shortStart d a + 2 * k, rfl⟩, shortRadius_ge hd k hk1 hkK,
      shortRadius_le_rpow hd hd1 ha k⟩ hE
  have hBle : ∀ x ∈ S, P (B x) ≤ ENNReal.ofReal (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ))) := by
    intro x _
    by_cases hx : ((d / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I) ∈ reg
    · exact (measure_mono fun ω hω => hω.2).trans (hpoint _ hx)
    · calc P (B x) ≤ P ∅ := measure_mono fun ω hω => (hx hω.1).elim
        _ = 0 := measure_empty
        _ ≤ _ := zero_le
  have hcard : (S.card : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
    rw [hS, card_shortGrid]
    push_cast
    ring
  have hMle : (M : ℝ) ≤ 100 / d := Nat.floor_le (by positivity)
  have h1d : 1 ≤ 1 / d := by
    rw [le_div_iff₀ hd]
    linarith
  have h2M : 2 * (M : ℝ) + 1 ≤ 201 / d := by
    have e : (201 : ℝ) / d = 2 * (100 / d) + 1 / d := by ring
    rw [e]
    linarith
  have hsq : (2 * (M : ℝ) + 1) ^ 2 ≤ (201 / d) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have hexp := exp_shortCount_le hd hd1 ha ha1
  have hC6e : 0 ≤ C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ)) :=
    mul_nonneg hC₆.le (Real.exp_pos _).le
  have hreal : (S.card : ℝ) * (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ))) ≤
      201 ^ 2 * C₆ * Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 6 := by
    rw [hcard]
    calc (2 * (M : ℝ) + 1) ^ 2 * (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ)))
        ≤ (201 / d) ^ 2 * (C₆ * (Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 8)) :=
          mul_le_mul hsq (mul_le_mul_of_nonneg_left hexp hC₆.le) hC6e (by positivity)
      _ = 201 ^ 2 * C₆ * Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 6 := by
          field_simp
  calc P {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
        ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z}
      ≤ P (⋃ x ∈ S, B x) := measure_mono hsub
    _ ≤ ∑ x ∈ S, P (B x) := measure_biUnion_finset_le S B
    _ ≤ ∑ x ∈ S, ENNReal.ofReal (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ))) :=
        Finset.sum_le_sum hBle
    _ = ENNReal.ofReal ((S.card : ℝ) * (C₆ * Real.exp (-(16 * Real.log 7 / (1 - a)) * (K : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (201 ^ 2 * C₆ * Real.exp (24 * Real.log 7 / (1 - a)) * d ^ 6) :=
        ENNReal.ofReal_le_ofReal hreal

/-- **PRO step 3, with the annulus iteration discharged**: `AnnulusIterateStmt` is the unconditional theorem
`MatedCRT.annulusIterate` (`Proofs/Field/LawTransferComplete.lean`). The remaining named inputs are the one-annulus hit
bound `FirstPass64.AnnulusHitUniformStmt` (S6p; from `firstPass_6_5_uniform` with its frozen inputs), the cone transfer
`AnnulusIterateConeTransferStep` (needs the Step `ConeMeanZeroRestrictionStep`) and the locality
`GoodAnnulusEventLocalityStep` (needs the Step `Field.ConeCircle.circleAverageModConstStep`). -/
theorem shortWindow_prevalence (h65 : FirstPass64.AnnulusHitUniformStmt)
    (hT : AnnulusIterateConeTransferStep) (hL : GoodAnnulusEventLocalityStep) :
    ShortWindowGoodRadiusPrevalenceStmt :=
  shortWindow_prevalence_of_steps annulusIterate h65 hT hL

end Lemma68Window

end MatedCRT
