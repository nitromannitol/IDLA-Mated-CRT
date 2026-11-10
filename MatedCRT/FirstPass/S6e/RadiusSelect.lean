import Mathlib
import MatedCRT.FirstPass.S6e.Scales
import MatedCRT.FirstPass.S6e.C17Induction

/-!
# FIRST PASS: the selected radii `R_j` of LEMMA68 (N2 selection, hR of C17; task fp-S6e-lemma68-C17, z9)

Sources (repository notes; no Lean credit before this file):
* `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` A4 (lines 249-301): for `0 < δ` with `L = log(1/δ)`,
  `n_- = ⌈L/(2 log 7)⌉`, `n_+ = ⌊L/log 7⌋`, `K = n_+ - n_- + 1`, the radii `R_k = 7^{-(n_- + k - 1)}`, `1 ≤ k ≤ K`,
  are the seven-adic radii in `[δ, √δ]` (the statement there assumes `δ ≤ 7^{-4}`; only the membership is used here).
* `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` C1 (line 685) and A5 (lines 302-372): `R_z` is the first good radius among
  the candidates, with the default `R_z = δ` when the point is inadmissible or no candidate is good.
* `notes/fp-gaps/CHATGPT-z9-lemma68-B1B2.md` §8.1-8.2 (lines 819-890, equations (19)-(21)): `Δ(r) = 2^{-n(r)}`,
  every selected radius lies in `[Δ(r), √Δ(r)]`, hence `r^p/2 < R_j ≤ r^{p/2}`. This is the `hR` of `C17_le_pow`
  (`Lemma68Induction`, `C17Induction.lean`).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Radius

open Lemma68Scales

/-- The seven-adic radii `7^{-m}`, `m ∈ ℤ`, lying in `[δ, √δ]` (A4). -/
def sevenAdicIn (δ : ℝ) : Set ℝ :=
  {ρ | ∃ m : ℤ, ρ = (7 : ℝ) ^ (-m) ∧ δ ≤ ρ ∧ ρ ≤ Real.sqrt δ}

/-- The values a selected radius can take: the default `δ` or a seven-adic radius in `[δ, √δ]` (A4, C1). -/
def selectable (δ : ℝ) : Set ℝ :=
  insert δ (sevenAdicIn δ)

/-- The lower index `n_- = ⌈L/(2 log 7)⌉` of A4, with `L = log(1/δ) = -log δ`. -/
noncomputable def nMinus (δ : ℝ) : ℤ :=
  ⌈-Real.log δ / (2 * Real.log 7)⌉

/-- The upper index `n_+ = ⌊L/log 7⌋` of A4. -/
noncomputable def nPlus (δ : ℝ) : ℤ :=
  ⌊-Real.log δ / Real.log 7⌋

/-- The A4 candidates `R_k = 7^{-(n_- + k)}`, indexed from `k = 0` (A4 writes `7^{-(n_- + k - 1)}`, `1 ≤ k ≤ K`). -/
noncomputable def cand (δ : ℝ) (k : ℕ) : ℝ :=
  (7 : ℝ) ^ (-(nMinus δ + (k : ℤ)))

/-- The number `K = n_+ - n_- + 1` of A4 candidates. -/
noncomputable def numCand (δ : ℝ) : ℕ :=
  (nPlus δ - nMinus δ + 1).toNat

lemma log_seven_pos : 0 < Real.log 7 :=
  Real.log_pos (by norm_num)

/-- (A4) A seven-adic radius `7^{-m}` with `L/(2 log 7) ≤ m ≤ L/log 7`, `L = log(1/δ)`, lies in `[δ, √δ]`. -/
lemma sevenAdic_bounds {δ : ℝ} (hδ : 0 < δ) {m : ℤ}
    (hlo : -Real.log δ / (2 * Real.log 7) ≤ (m : ℝ)) (hhi : (m : ℝ) ≤ -Real.log δ / Real.log 7) :
    δ ≤ (7 : ℝ) ^ (-m) ∧ (7 : ℝ) ^ (-m) ≤ Real.sqrt δ := by
  have h7 : 0 < Real.log 7 := log_seven_pos
  have hpos : 0 < (7 : ℝ) ^ (-m) := zpow_pos (by norm_num) _
  have hlog : Real.log ((7 : ℝ) ^ (-m)) = ((-m : ℤ) : ℝ) * Real.log 7 := Real.log_zpow _ _
  have hA : (m : ℝ) * Real.log 7 ≤ -Real.log δ := by
    rwa [le_div_iff₀ h7] at hhi
  have hB : -Real.log δ ≤ (m : ℝ) * (2 * Real.log 7) := by
    rwa [div_le_iff₀ (by positivity)] at hlo
  constructor
  · rw [← Real.log_le_log_iff hδ hpos, hlog]
    push_cast
    linarith
  · rw [← Real.log_le_log_iff hpos (Real.sqrt_pos.2 hδ), Real.log_sqrt hδ.le, hlog]
    push_cast
    linarith

/-- (A4) For `m = n_- + k` with `k ≤ n_+ - n_-`, the candidate `cand δ k` is a seven-adic radius in `[δ, √δ]`. -/
lemma cand_mem_sevenAdicIn {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : (k : ℤ) ≤ nPlus δ - nMinus δ) :
    cand δ k ∈ sevenAdicIn δ := by
  have hceil : -Real.log δ / (2 * Real.log 7) ≤ (nMinus δ : ℝ) := Int.le_ceil _
  have hfloor : (nPlus δ : ℝ) ≤ -Real.log δ / Real.log 7 := Int.floor_le _
  have hk' : (k : ℝ) ≤ (nPlus δ : ℝ) - (nMinus δ : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  obtain ⟨h1, h2⟩ := sevenAdic_bounds hδ (m := nMinus δ + (k : ℤ))
    (by push_cast; linarith) (by push_cast; linarith)
  exact ⟨nMinus δ + (k : ℤ), rfl, h1, h2⟩

open Classical in
/-- (A5, C1) The first-good-radius choice: the first candidate `cand k` (`k < K`) whose good event `good k` holds;
the default `δ` when no candidate is good. -/
noncomputable def firstGoodRadius (δ : ℝ) (cand : ℕ → ℝ) (K : ℕ) (good : ℕ → Prop) : ℝ :=
  if h : ∃ k, k < K ∧ good k then cand (Nat.find h) else δ

open Classical in
/-- The first-good-radius choice takes values in `selectable δ` whenever every candidate `cand k`, `k < K`, is
a seven-adic radius in `[δ, √δ]`. -/
lemma firstGoodRadius_mem {δ : ℝ} {cand : ℕ → ℝ} {K : ℕ} {good : ℕ → Prop}
    (hcand : ∀ k, k < K → cand k ∈ sevenAdicIn δ) :
    firstGoodRadius δ cand K good ∈ selectable δ := by
  unfold firstGoodRadius
  split_ifs with h
  · exact Set.mem_insert_of_mem _ (hcand _ (Nat.find_spec h).1)
  · exact Set.mem_insert _ _

/-- (A4 + A5, N2) The first-good-radius choice over the A4 candidates `cand δ k`, `k < numCand δ`, is selectable. -/
lemma firstGood_cand_mem {δ : ℝ} (hδ : 0 < δ) (good : ℕ → Prop) :
    firstGoodRadius δ (cand δ) (numCand δ) good ∈ selectable δ := by
  apply firstGoodRadius_mem
  intro k hk
  unfold numCand at hk
  have hk1 : (k : ℤ) < nPlus δ - nMinus δ + 1 := Int.lt_toNat.1 hk
  exact cand_mem_sevenAdicIn hδ (by omega)

/-- For `0 < δ ≤ 1`, every selectable radius lies in `[δ, √δ]`, and `√δ ≤ 1`. -/
lemma selectable_bounds {δ ρ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : ρ ∈ selectable δ) :
    δ ≤ ρ ∧ ρ ≤ Real.sqrt δ := by
  have hs1 : Real.sqrt δ ≤ 1 := by simpa using Real.sqrt_le_sqrt hδ1
  have hsq : δ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ, mul_nonneg (Real.sqrt_nonneg δ) (sub_nonneg.2 hs1)]
  rcases hρ with h | h
  · rw [h]
    exact ⟨le_rfl, hsq⟩
  · obtain ⟨m, rfl, h1, h2⟩ := h
    exact ⟨h1, h2⟩

/-- `Δ(r) = 2^{-n(r)}` is positive (write-up (19)). -/
lemma delta_pos (p r : ℝ) : 0 < Delta p r := by
  unfold Delta
  positivity

/-- (N2, (20)-(21); C17 `hR`) For `0 < p`, `0 < r < 1`, a selectable radius with default `Δ(r)` satisfies
`0 < R ≤ 1` and `r^p/2 < R`. -/
lemma selectable_delta_bounds {p r ρ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hρ : ρ ∈ selectable (Delta p r)) : 0 < ρ ∧ ρ ≤ 1 ∧ r ^ p / 2 < ρ := by
  have hΔ0 : 0 < Delta p r := delta_pos p r
  have hΔ1 : Delta p r ≤ 1 :=
    (Delta_le_rpow hp hr0 hr1).trans (Real.rpow_le_one hr0.le hr1.le hp.le)
  have hlow : r ^ p / 2 < Delta p r := half_rpow_lt_Delta hp hr0 hr1
  obtain ⟨h1, h2⟩ := selectable_bounds hΔ0 hΔ1 hρ
  have hs1 : Real.sqrt (Delta p r) ≤ 1 := by simpa using Real.sqrt_le_sqrt hΔ1
  exact ⟨lt_of_lt_of_le hΔ0 h1, h2.trans hs1, lt_of_lt_of_le hlow h1⟩

/-- (C17 `hR`) If every selected radius `R j ω` is selectable with default `Δ(r)`, then the hypothesis `hR` of
`C17_le_pow` holds (surely, hence almost surely). -/
lemma hR_of_selectable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r)
    (hr1 : r < 1) (R : ℕ → Ω → ℝ) (hsel : ∀ j ω, R j ω ∈ selectable (Delta p r)) :
    ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ p / 2 < R j ω :=
  fun j => ae_of_all μ fun ω => selectable_delta_bounds hp hr0 hr1 (hsel j ω)

/-- (N2 selection of `R_j`, C17 `hR`) The radii `R j ω` selected by the first-good-radius choice over the A4 candidates,
with default `Δ(r)`, satisfy the hypothesis `hR` of `C17_le_pow` almost surely. The good events `good j k ω` are
arbitrary here (A5 supplies their measurability and probability bounds, not used for the range). -/
lemma hR_firstGood {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r)
    (hr1 : r < 1) (good : ℕ → ℕ → Ω → Prop) (R : ℕ → Ω → ℝ)
    (hR_def : ∀ j ω, R j ω = firstGoodRadius (Delta p r) (cand (Delta p r)) (numCand (Delta p r))
      (fun k => good j k ω)) :
    ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ p / 2 < R j ω := by
  refine hR_of_selectable μ hp hr0 hr1 R (fun j ω => ?_)
  rw [hR_def]
  exact firstGood_cand_mem (delta_pos p r) _

/-- (C17 with the selected radii) The induction `P(H_N) ≤ (1 - q(r))^N` of `C17_le_pow`, with the radii `R j ω`
selected by the first-good-radius choice over the A4 candidates (default `Δ(r)`), so that `hR` is proved. The only
remaining input is the step bound `hstep` (C15, from B5 (B18) and the strong Markov property at `S_j`). -/
theorem C17_le_pow_selected {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hGad : ∀ j, MeasurableSet[m (j + 1)] (G j)) {qStar r p : ℝ} (hq : 0 ≤ qStar) (hq9 : qStar ≤ 9)
    (hp0 : 0 < p) (hp : p ≤ 3) (hr0 : 0 < r) (hr1 : r < 1)
    (good : ℕ → ℕ → Ω → Prop) (R : ℕ → Ω → ℝ)
    (hR_def : ∀ j ω, R j ω = firstGoodRadius (Delta p r) (cand (Delta p r)) (numCand (Delta p r))
      (fun k => good j k ω))
    (hstep : ∀ j, ∀ᵐ ω ∂μ, qStar / (1 + Real.log (1 / R j ω)) ^ 2 ≤
      (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω)
    (H : ℕ → Set Ω) (hH0 : H 0 = Set.univ) (hHs : ∀ j, H (j + 1) = H j ∩ (G j)ᶜ) (N : ℕ) :
    μ.real (H N) ≤ (1 - qStar / 9 / (1 + Real.log (1 / r)) ^ 2) ^ N :=
  Lemma68Induction.C17_le_pow μ m hmono hm hG hGad hq hq9 hp hr0 hr1.le R
    (hR_firstGood μ hp0 hr0 hr1 good R hR_def) hstep H hH0 hHs N

end Lemma68Radius

end MatedCRT
