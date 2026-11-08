import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Proposed.PrestonAnalytic2008
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Clock
import MatedCRT.Proofs.Sec1.EnvironmentScaling

/-!
# All-starts clock set `𝒢` (lem:allstarts, env-steps.tex:380-446): definitions, Steps, transfer

Source: `lem:allstarts` (env-steps.tex:380-446) and the proof of `prop:clock` (env-steps.tex:449-487).

Lean names for the paper's objects:
* `posCircleExt a`: the continuous positive-circle field `a ∈ C((0,∞) × ℂ, ℝ)` (env-steps.tex:112), extended by `0`
  to radius `0` so that `lqgClockApprox` can read it; only the dyadic radii `dyadicScale n` are read.
* `clockApprox γ a n w`: the approximating clock `A_n(a,w,·)` of eq:clockapprox (`lqgClockApprox` at `dyadicScale n`).
* `pathDist`: the metric `d_𝒯` of env-steps.tex:398-400. `CauchyInProbability`: the condition eq:cauchy.
* `timeClockSet`: `𝒯_*` of eq:timeclock.
* `AdmitsAllStartClock γ a`, `allStartsSet γ`: `a ∈ 𝒢` iff one `F` satisfies eq:ucp and eq:timeclock for every start.
* `clockLimit γ nsel a z`: `J(a,z,·)` (env-steps.tex:402-407) for a subsequence choice `nsel`.
* `SelectedAllStartsRelation γ nsel a z`: `Q(a,z)`; `selectedAllStartsSet γ nsel`: `{a : ∀ z, Q(a,z)}`.

Proved here (no Step hypothesis):
* `allStartsSet_eq_selected` / `allStartsCharacterization_of_tail`: `𝒢 = {a : ∀ z, Q(a,z)}`, both directions, from the
  subsequence tail property `SubsequenceTailProperty` (union bounds; no Borel-Cantelli). The almost-sure clause of `Q`
  is `∀ᵐ`, not the outer-measure equation (see `SelectedAllStartsRelation`).
* `pathDist` estimates and tail limits (`pathDist_le_of_abs_le`, `tail_tendstoLocallyUniformly`), `continuous_clockApprox`.
* `isLQGClock_congr_dyadic`: fields that agree on the dyadic radii have the same `IsLQGClock` (common-clock step).
* `ae_allStarts_of_map_eq` and `allStartsSet_isUniversallyMeasurable` (hypotheses: staged Preston input, Borel step).
  `ae_allStarts_of_map_eq`: `a₀ ∈ 𝒢` almost surely and equality in law give `aᵦ ∈ 𝒢` almost surely.

Proved for the constructed subsequence `nselFun` (Mathlib compact-open Borel structure, no binder):
* `borelSubsequenceSelectionStep_nselFun`: `BorelSubsequenceSelectionStep γ (nselFun γ)` (lem:allstarts proof,
  env-steps.tex:380-446: Borel recursive choice of `n_k(a,z)`, strictly increasing, with the tail bound).
* `borelAllStartsRelationStep_nselFun`: `BorelAllStartsRelationStep γ (nselFun γ)` (env-steps.tex:413-421: `Q` is Borel,
  via the good sets, the pointwise limsup, the rational reduction `isTimeChangeClock_iff_rat`, and the kernel section lemma).

Still hypotheses (binder form, outside the constructed subsequence): `[MeasurableSpace CircleFns] [BorelSpace CircleFns]`
and `[PolishSpace CircleFns]` in `allStartsSet_isUniversallyMeasurable` / `ae_allStarts_of_map_eq` (Polish structure: owned by
the circle-process-space task).
-/

open MatedCRT.EnvClock

namespace MatedCRT.AllStarts

open HarmonicBalls MeasureTheory MarkovProcess Filter
open scoped ENNReal NNReal

/-- The positive-circle index set `E = (0,∞) × ℂ` (env-steps.tex:112). -/
abbrev PosCircle : Type := Set.Ioi (0 : ℝ) × ℂ

/-- `H = C(E,ℝ)` with the compact-open topology (env-steps.tex:380). -/
abbrev CircleFns : Type := C(PosCircle, ℝ)

/-- Zero extension of a continuous circle function to all radii; only the dyadic radii are read. -/
noncomputable def posCircleExt (a : CircleFns) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then a (⟨r, h⟩, z) else 0

/-- `A_n(a,w,·)` of eq:clockapprox: `lqgClockApprox` at the dyadic scale `dyadicScale n`. -/
noncomputable def clockApprox (γ : ℝ) (a : CircleFns) (n : ℕ) (w : ContinuousPath ℂ) : ℝ≥0 → ℝ :=
  lqgClockApprox γ (posCircleExt a) (dyadicScale n) w

/-- The metric `d_𝒯` of env-steps.tex:398-400 on `C([0,∞),ℝ)`: `∑_{j≥1} 2^{-j} min {1, sup_{t≤j} |f(t) - g(t)|}`,
indexed here by `j ↦ j+1`. -/
noncomputable def pathDist (f g : ℝ≥0 → ℝ) : ℝ :=
  ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Set.Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|)

/-- The condition eq:cauchy: for every `k ≥ 1` there is `N` with `W_z {d_𝒯(A_n, A_m) > 2^{-k}} < 2^{-k}` for `n, m ≥ N`. -/
def CauchyInProbability (γ : ℝ) (a : CircleFns) (z : ℂ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
    planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
      < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)

/-- `𝒯_*` of eq:timeclock: `F 0 = 0`, `F` continuous and strictly increasing, `F t → ∞` (`IsTimeChangeClock`). -/
def timeClockSet : Set (ℝ≥0 → ℝ) := {f | IsTimeChangeClock f}

/-- lem:allstarts: `a ∈ 𝒢` iff some single `F (w,t)` satisfies eq:ucp (`IsLQGClock`, with `hε = posCircleExt a`)
and eq:timeclock for every starting point `z`; eq:timeclock holds `W_z`-almost surely. -/
def AdmitsAllStartClock (γ : ℝ) (a : CircleFns) : Prop :=
  ∃ F : ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ z : ℂ,
    IsLQGClock planarBrownianMotion γ (posCircleExt a) z F ∧
      ∀ᵐ B ∂planarBrownianMotion z, IsTimeChangeClock (F B)

/-- The set `𝒢` of lem:allstarts (env-steps.tex:380-446). -/
def allStartsSet (γ : ℝ) : Set CircleFns := {a | AdmitsAllStartClock γ a}

open Classical in
/-- `J(a,z,w)` (env-steps.tex:402-407) for a subsequence choice `nsel a z k = n_k(a,z)`: the locally uniform limit of
`A_{n_k}(a,·,w)` when it exists, and `t ↦ t` otherwise. -/
noncomputable def clockLimit (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ)
    (w : ContinuousPath ℂ) : ℝ≥0 → ℝ :=
  if h : ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop then
    h.choose
  else fun t => (t : ℝ)

/-- `Q(a,z)` (lem:allstarts proof, env-steps.tex:380-446): eq:cauchy holds, and `J(a,z,w) ∈ 𝒯_*` for `W_z`-almost
every `w`. The probability-one clause `W_z{J ∈ 𝒯_*} = 1` is read as the almost-sure statement: for a nonmeasurable
`J` the outer-measure equation does not give almost-sure membership, and the almost-sure form needs no measurability
of `J` in the characterization (`J` is measurable for the Borel Step, which is still outstanding). -/
def SelectedAllStartsRelation (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ) : Prop :=
  CauchyInProbability γ a z ∧ ∀ᵐ w ∂planarBrownianMotion z, clockLimit γ nsel a z w ∈ timeClockSet

/-- `{a : ∀ z, Q(a,z)}` for the subsequence choice `nsel`. -/
def selectedAllStartsSet (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Set CircleFns :=
  {a | ∀ z : ℂ, SelectedAllStartsRelation γ nsel a z}

/-! ### Deterministic facts on `pathDist` and locally uniform limits (env-steps.tex:398-411)

A `pathDist`-small step gives a small sup-distance on each `[0, J]`, and a tail of small steps gives a locally uniform
limit with an explicit rate. These are the metric inputs of the characterization below. -/

section PathDistFacts

open Set Topology

lemma pathDist_summand_nonneg (f g : ℝ≥0 → ℝ) (j : ℕ) :
    0 ≤ (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|) :=
  mul_nonneg (pow_nonneg (by norm_num) _)
    (le_min zero_le_one (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _))

lemma pathDist_summand_le_half_pow (f g : ℝ≥0 → ℝ) (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|)
      ≤ (1 / 2 : ℝ) ^ (j + 1) :=
  mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (min_le_left _ _)

lemma summable_half_pow_succ : Summable fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) := by
  simpa only [pow_succ] using (summable_geometric_two).mul_right (1 / 2 : ℝ)

lemma summable_pathDist_summand (f g : ℝ≥0 → ℝ) :
    Summable fun j : ℕ =>
      (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|) :=
  Summable.of_nonneg_of_le (pathDist_summand_nonneg f g) (pathDist_summand_le_half_pow f g)
    summable_half_pow_succ

/-- One summand of `pathDist` is at most `pathDist`. -/
lemma summand_le_pathDist (f g : ℝ≥0 → ℝ) (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|)
      ≤ pathDist f g :=
  (summable_pathDist_summand f g).le_tsum j (fun i _ => pathDist_summand_nonneg f g i)

/-- A pointwise value of `|f - g|` on `[0, j+1]` is seen by the `j`-th summand of `pathDist`. -/
lemma half_pow_min_le_pathDist {f g : ℝ≥0 → ℝ} (hf : Continuous f) (hg : Continuous g) {j : ℕ} {t : ℝ≥0}
    (ht : t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)) :
    (1 / 2 : ℝ) ^ (j + 1) * min 1 |f t - g t| ≤ pathDist f g := by
  refine le_trans ?_ (summand_le_pathDist f g j)
  refine mul_le_mul_of_nonneg_left (min_le_min_left _ ?_) (pow_nonneg (by norm_num) _)
  have hc : Continuous fun s => |f s - g s| := by fun_prop
  have hK : IsCompact (Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)) := isCompact_Icc
  obtain ⟨M, hM⟩ := (hK.image hc).bddAbove
  have hF : ∀ s : ℝ≥0, (⨆ (_ : s ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)), |f s - g s|) ≤ max M 0 := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)
    · rw [ciSup_pos hs]
      exact le_max_of_le_left (hM ⟨s, hs, rfl⟩)
    · rw [ciSup_neg hs, Real.sSup_empty]
      exact le_max_right _ _
  have hbddF : BddAbove (Set.range fun s : ℝ≥0 =>
      ⨆ (_ : s ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)), |f s - g s|) :=
    ⟨max M 0, by rintro _ ⟨s, rfl⟩; exact hF s⟩
  refine le_ciSup_of_le hbddF t ?_
  show |f t - g t| ≤ ⨆ (_ : t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)), |f t - g t|
  rw [ciSup_pos ht]

/-- If `pathDist f g ≤ c` and `2^(j+1) c < 1`, then `|f - g| ≤ 2^(j+1) c` on `[0, j+1]`. -/
lemma abs_le_of_pathDist_le {f g : ℝ≥0 → ℝ} (hf : Continuous f) (hg : Continuous g) {j : ℕ} {t : ℝ≥0}
    {c : ℝ} (hc : pathDist f g ≤ c) (hcj : (2 : ℝ) ^ (j + 1) * c < 1)
    (ht : t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)) :
    |f t - g t| ≤ (2 : ℝ) ^ (j + 1) * c := by
  by_contra hlt
  rw [not_le] at hlt
  have hmin : (2 : ℝ) ^ (j + 1) * c < min 1 |f t - g t| := lt_min hcj hlt
  have hkey : (1 / 2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (j + 1) * c) = c := by
    rw [← mul_assoc, ← mul_pow]; norm_num
  have h1 := mul_lt_mul_of_pos_left hmin (show (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) by positivity)
  have h2 := half_pow_min_le_pathDist hf hg ht
  linarith

lemma sum_half_pow_succ_range (J : ℕ) :
    ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ (1 / 2 : ℝ) n]; ring

lemma tsum_half_pow_succ : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) = 1 := by
  simp only [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]
  norm_num

/-- If `|f - g| ≤ η` on `[0, J]`, then `pathDist f g ≤ η + 2^{-J}`. -/
lemma pathDist_le_of_abs_le {f g : ℝ≥0 → ℝ} {η : ℝ} (hη : 0 ≤ η) (J : ℕ)
    (h : ∀ t ∈ Icc (0 : ℝ≥0) (J : ℝ≥0), |f t - g t| ≤ η) :
    pathDist f g ≤ η + (1 / 2 : ℝ) ^ J := by
  have hs := summable_pathDist_summand f g
  have hsplit := Summable.sum_add_tsum_nat_add J hs
  have hfin : ∑ i ∈ Finset.range J,
      (1 / 2 : ℝ) ^ (i + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((i + 1 : ℕ) : ℝ≥0), |f t - g t|) ≤ η := by
    have hterm : ∀ i ∈ Finset.range J,
        (1 / 2 : ℝ) ^ (i + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((i + 1 : ℕ) : ℝ≥0), |f t - g t|)
          ≤ (1 / 2 : ℝ) ^ (i + 1) * η := by
      intro i hi
      have hiJ : i + 1 ≤ J := Finset.mem_range.mp hi
      refine mul_le_mul_of_nonneg_left (min_le_of_right_le ?_) (pow_nonneg (by norm_num) _)
      refine Real.iSup_le (fun t => Real.iSup_le (fun ht => h t ⟨ht.1, ht.2.trans ?_⟩) hη) hη
      exact_mod_cast hiJ
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, sum_half_pow_succ_range J]
    have hJ0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := pow_nonneg (by norm_num) _
    nlinarith [mul_nonneg hJ0 hη]
  have hgeo : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + J + 1) = (1 / 2 : ℝ) ^ J := by
    have hrw : ∀ i : ℕ, (1 / 2 : ℝ) ^ (i + J + 1) = (1 / 2 : ℝ) ^ J * (1 / 2 : ℝ) ^ (i + 1) := by
      intro i
      rw [← pow_add]
      congr 1
      ring
    simp_rw [hrw]
    rw [tsum_mul_left, tsum_half_pow_succ, mul_one]
  have hsumT : Summable fun i : ℕ => (1 / 2 : ℝ) ^ (i + J + 1) :=
    (summable_nat_add_iff J).mpr summable_half_pow_succ
  have htail : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + J + 1)
      * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((i + J + 1 : ℕ) : ℝ≥0), |f t - g t|) ≤ (1 / 2 : ℝ) ^ J := by
    rw [← hgeo]
    exact Summable.tsum_le_tsum (fun i => pathDist_summand_le_half_pow f g (i + J))
      ((summable_nat_add_iff J).mpr hs) hsumT
  unfold pathDist
  linarith [hsplit, hfin, htail]

/-- One telescoping step of a `pathDist`-small tail, on `[0, J]` with `i ≥ max K (J+2)`. -/
lemma tail_abs_step {f : ℕ → ℝ≥0 → ℝ} (hf : ∀ m, Continuous (f m)) {K : ℕ}
    (h : ∀ m, K ≤ m → pathDist (f m) (f (m + 1)) ≤ (1 / 2 : ℝ) ^ m) {J i : ℕ} (hKi : K ≤ i)
    (hJi : J + 2 ≤ i) {t : ℝ≥0} (ht : t ∈ Icc (0 : ℝ≥0) (J : ℝ≥0)) :
    |f i t - f (i + 1) t| ≤ (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ i := by
  have hpow : (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (J + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hle : (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ (J + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJi
  have h5 : (1 / 2 : ℝ) ^ (J + 2) = (1 / 2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) := by ring
  have hcj : (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ i < 1 := by
    have h3 : (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ i ≤ (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (J + 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h4 : (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (J + 2) = 1 / 2 := by
      rw [h5, show (2 : ℝ) ^ (J + 1) * ((1 / 2 : ℝ) ^ (J + 1) * (1 / 2))
          = ((2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (J + 1)) * (1 / 2) by ring, hpow]
      norm_num
    linarith
  have ht' : t ∈ Icc (0 : ℝ≥0) ((J + 1 : ℕ) : ℝ≥0) :=
    ⟨ht.1, ht.2.trans (by exact_mod_cast Nat.le_succ J)⟩
  exact abs_le_of_pathDist_le (hf i) (hf (i + 1)) (h i hKi) hcj ht'

/-- Under a tail of `pathDist`-small steps, a pointwise limit `L` satisfies `|f m t - L t| ≤ 2^(J+2) 2^{-m}` on `[0, J]`
for `m ≥ max K (J+2)`. -/
lemma tail_abs_le_limit {f : ℕ → ℝ≥0 → ℝ} (hf : ∀ m, Continuous (f m)) {K : ℕ}
    (h : ∀ m, K ≤ m → pathDist (f m) (f (m + 1)) ≤ (1 / 2 : ℝ) ^ m) {L : ℝ≥0 → ℝ}
    (hL : ∀ t, Tendsto (fun m => f m t) atTop (𝓝 (L t))) {J m : ℕ} (hKm : K ≤ m) (hJm : J + 2 ≤ m)
    {t : ℝ≥0} (ht : t ∈ Icc (0 : ℝ≥0) (J : ℝ≥0)) :
    |f m t - L t| ≤ (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m := by
  have hC0 : 0 ≤ (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m := by positivity
  have hpart : ∀ n : ℕ, |f m t - f (m + n) t| ≤
      (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m * (1 - (1 / 2 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hnm : m + (n + 1) = m + n + 1 := by omega
      rw [hnm]
      have hstep := tail_abs_step hf h (J := J) (i := m + n) (by omega) (by omega) ht
      have hcombine : (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m * (1 - (1 / 2 : ℝ) ^ n)
          + (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (m + n)
          = (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m * (1 - (1 / 2 : ℝ) ^ (n + 1)) := by
        ring
      have htri := abs_sub_le (f m t) (f (m + n) t) (f (m + n + 1) t)
      linarith [htri, ih, hstep, hcombine]
  have hshift : Tendsto (fun n : ℕ => f (m + n) t) atTop (𝓝 (L t)) :=
    (hL t).comp (tendsto_atTop_mono (fun n => Nat.le_add_left n m) tendsto_id)
  have hlim : Tendsto (fun n : ℕ => |f m t - f (m + n) t|) atTop (𝓝 |f m t - L t|) :=
    ((tendsto_const_nhds).sub hshift).abs
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  refine (hpart n).trans (mul_le_of_le_one_right hC0 ?_)
  linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- A tail of `pathDist`-small steps makes `m ↦ f m t` converge for every `t`. -/
lemma tail_exists_limit {f : ℕ → ℝ≥0 → ℝ} (hf : ∀ m, Continuous (f m)) {K : ℕ}
    (h : ∀ m, K ≤ m → pathDist (f m) (f (m + 1)) ≤ (1 / 2 : ℝ) ^ m) (t : ℝ≥0) :
    ∃ ℓ : ℝ, Tendsto (fun m => f m t) atTop (𝓝 ℓ) := by
  set J : ℕ := ⌈(t : ℝ)⌉₊ with hJdef
  have ht : t ∈ Icc (0 : ℝ≥0) (J : ℝ≥0) := ⟨by positivity, by
    have := Nat.le_ceil (t : ℝ)
    exact_mod_cast this⟩
  set M : ℕ := K + J + 2 with hM
  have hcs : CauchySeq fun n : ℕ => f (n + M) t := by
    refine cauchySeq_of_le_geometric (1 / 2 : ℝ) ((2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ M)
      (by norm_num) ?_
    intro n
    have hn : n + 1 + M = n + M + 1 := by omega
    show dist (f (n + M) t) (f (n + 1 + M) t) ≤ _
    rw [hn, Real.dist_eq]
    have hstep := tail_abs_step hf h (J := J) (i := n + M) (by omega) (by omega) ht
    calc |f (n + M) t - f (n + M + 1) t| ≤ (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ (n + M) := hstep
      _ = (2 : ℝ) ^ (J + 1) * (1 / 2 : ℝ) ^ M * (1 / 2 : ℝ) ^ n := by ring
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  exact ⟨ℓ, (tendsto_add_atTop_iff_nat M).mp hℓ⟩

/-- A tail of `pathDist`-small steps has a locally uniform limit, with the rate `2^(J+2) 2^{-m}` on `[0, J]`. -/
lemma tail_tendstoLocallyUniformly {f : ℕ → ℝ≥0 → ℝ} (hf : ∀ m, Continuous (f m)) {K : ℕ}
    (h : ∀ m, K ≤ m → pathDist (f m) (f (m + 1)) ≤ (1 / 2 : ℝ) ^ m) :
    ∃ L : ℝ≥0 → ℝ, (∀ t, Tendsto (fun m => f m t) atTop (𝓝 (L t))) ∧
      TendstoLocallyUniformly f L atTop := by
  choose ℓ hℓ using fun t => tail_exists_limit hf h t
  refine ⟨ℓ, hℓ, ?_⟩
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  set J : ℕ := ⌈(x : ℝ)⌉₊ + 1 with hJ
  have hxJ : x < (J : ℝ≥0) := by
    have h1 : (x : ℝ) < ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (x : ℝ)]
    exact_mod_cast h1
  refine ⟨Iio (J : ℝ≥0), Iio_mem_nhds hxJ, ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 2 ^ (J + 2) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hkey : (1 / 2 : ℝ) ^ k * 2 ^ (J + 2) < ε := (lt_div_iff₀ (by positivity)).mp hk
  filter_upwards [eventually_ge_atTop (k + K + J + 3)] with m hm
  intro y hy
  have hy' : y ∈ Icc (0 : ℝ≥0) (J : ℝ≥0) := ⟨by positivity, (Set.mem_Iio.mp hy).le⟩
  have hb := tail_abs_le_limit hf h hℓ (J := J) (m := m) (by omega) (by omega) hy'
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [Real.dist_eq, abs_sub_comm]
  calc |f m y - ℓ y| ≤ (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ m := hb
    _ ≤ (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ < ε := by rw [mul_comm]; exact hkey

/-- The clock approximation `A_n(a,w,·)` is continuous in the time variable (the integrand is continuous). -/
lemma continuous_clockApprox (γ : ℝ) (a : CircleFns) (n : ℕ) (w : ContinuousPath ℂ) :
    Continuous (clockApprox γ a n w) := by
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hg : Continuous fun s : ℝ =>
      dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * posCircleExt a (dyadicScale n) (w s.toNNReal)) := by
    have hpos : ∀ z : ℂ, posCircleExt a (dyadicScale n) z = a (⟨dyadicScale n, hε⟩, z) := by
      intro z
      simp [posCircleExt, hε]
    simp only [hpos]
    have hcont : Continuous fun s : ℝ => a (⟨dyadicScale n, hε⟩, w s.toNNReal) :=
      a.continuous.comp (continuous_const.prodMk (w.continuous.comp continuous_real_toNNReal))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hprim := intervalIntegral.continuous_primitive
    (fun x y => hg.intervalIntegrable (μ := MeasureTheory.volume) x y) 0
  unfold clockApprox lqgClockApprox
  exact hprim.comp NNReal.continuous_coe

end PathDistFacts

/-- The tail property of a subsequence choice `k ↦ n_k(a,z)` (lem:allstarts proof, env-steps.tex:404-411): strictly
increasing in `k`, and when eq:cauchy holds at `(a,z)`, the chosen indices satisfy the displayed tail bound for every
`k ≥ 1` and all `n, m ≥ n_k`. -/
def SubsequenceTailProperty (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  (∀ (a : CircleFns) (z : ℂ), StrictMono (nsel a z)) ∧
  (∀ (a : CircleFns) (z : ℂ), CauchyInProbability γ a z → ∀ k : ℕ, 1 ≤ k →
    ∀ n m : ℕ, nsel a z k ≤ n → nsel a z k ≤ m →
      planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
        < ENNReal.ofReal ((1 / 2 : ℝ) ^ k))

/-- **Named Step `BorelSubsequenceSelectionStep` (measurability clause outstanding).** The recursive choice of the
lem:allstarts proof: each `(a,z) ↦ n_k(a,z)` is Borel (clause 1, not proved here), and the tail property
`SubsequenceTailProperty` holds (clauses 2-3). -/
def BorelSubsequenceSelectionStep [MeasurableSpace CircleFns] (γ : ℝ)
    (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  (∀ k : ℕ, Measurable fun p : CircleFns × ℂ => nsel p.1 p.2 k) ∧ SubsequenceTailProperty γ nsel

/-- **Named Step `BorelAllStartsRelationStep` (outstanding, not proved).** `Q` is a Borel subset of
`C(E,ℝ) × ℂ`: the `W_z`-probabilities of eq:cauchy and of `{J ∈ 𝒯_*}` are Borel in `(a,z)`. -/
def BorelAllStartsRelationStep [MeasurableSpace CircleFns] (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  MeasurableSet {p : CircleFns × ℂ | SelectedAllStartsRelation γ nsel p.1 p.2}

/-- **Step `AllStartsCharacterizationStep`, proved** (`allStartsCharacterization_of_tail`, from `SubsequenceTailProperty`).
Both directions of lem:allstarts: `F = J(a, w(0), ·)` witnesses `a ∈ 𝒢` when `Q(a,·)` holds for every start, and
conversely any `F` witnessing `a ∈ 𝒢` forces eq:cauchy and `J = F` `W_z`-a.s. (env-steps.tex:380-446). -/
def AllStartsCharacterizationStep (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  allStartsSet γ = selectedAllStartsSet γ nsel

/-! ### Probability: the characterization of `𝒢` (lem:allstarts, env-steps.tex:380-446)

Union bounds only (no Borel-Cantelli). With `D_m = {2^{-m} < d_𝒯(A_{n_m}, A_{n_{m+1}})}`, `W_z(D_m) < 2^{-m}` for
`m ≥ 1`; the good set `G_K` (steps at rate `2^{-m}` from `K+1` on) has `W_z(G_K^c) ≤ 2^{-K}`. On `G_K` the selected
approximations converge locally uniformly, and the limit `J` is controlled by the same bounds. -/

section Characterization

open Set Topology MeasureTheory

/-- Locally uniform convergence gives pointwise convergence (`Metric` form of `TendstoLocallyUniformly`). -/
lemma tendsto_at_of_tendstoLocallyUniformly {F : ℕ → ℝ≥0 → ℝ} {f : ℝ≥0 → ℝ}
    (h : TendstoLocallyUniformly F f atTop) (x : ℝ≥0) :
    Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, ht, hev⟩ := (Metric.tendstoLocallyUniformly_iff.mp h) ε hε x
  filter_upwards [hev] with n hn
  rw [dist_comm]
  exact hn x (mem_of_mem_nhds ht)

/-- The good set `G_K`: from index `K+1` on, consecutive selected approximations are `d_𝒯`-close at rate `2^{-m}`. -/
def goodSet (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ) (K : ℕ) :
    Set (ContinuousPath ℂ) :=
  {w | ∀ m, K + 1 ≤ m →
    pathDist (clockApprox γ a (nsel a z m) w) (clockApprox γ a (nsel a z (m + 1)) w) ≤ (1 / 2 : ℝ) ^ m}

/-- The exceptional set where `J(a,z,·)` and `F` differ by at least `η` at some `t ≤ T`. -/
def badSet (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ)
    (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (T : ℕ) (η : ℝ) : Set (ContinuousPath ℂ) :=
  {w | ∃ t ≤ (T : ℝ≥0), η ≤ |clockLimit γ nsel a z w t - F w t|}

/-- Union bound for a geometric tail: `μ (⋃_{m ≥ K+1} D_m) ≤ 2^{-K}` when `μ (D_m) ≤ 2^{-m}`. -/
lemma measure_iUnion_half_pow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (D : ℕ → Set Ω) (K : ℕ)
    (hD : ∀ m, K + 1 ≤ m → μ (D m) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) :
    μ (⋃ i : ℕ, D (K + 1 + i)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
  refine (measure_iUnion_le _).trans ?_
  have hsum : ∀ i : ℕ, μ (D (K + 1 + i)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (K + 1 + i)) :=
    fun i => hD _ (by omega)
  refine (ENNReal.tsum_le_tsum hsum).trans ?_
  have hs : Summable fun i : ℕ => (1 / 2 : ℝ) ^ (K + 1 + i) := by
    simp only [pow_add]
    exact (summable_geometric_two).mul_left _
  have htsum : ∑' i : ℕ, (1 / 2 : ℝ) ^ (K + 1 + i) = (1 / 2 : ℝ) ^ K := by
    simp only [pow_add]
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs, htsum]

/-- `IsLQGClock` at one starting point makes the approximations Cauchy in probability (eq:cauchy). -/
theorem cauchyInProbability_of_isLQGClock {γ : ℝ} {a : CircleFns} {z : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hL : IsLQGClock planarBrownianMotion γ (posCircleExt a) z F) :
    CauchyInProbability γ a z := by
  intro k _hk
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  have hlim := hL ((k + 1 : ℕ) : ℝ≥0) ((1 / 2 : ℝ) ^ (k + 2)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hx)))
  refine ⟨N, fun n m hn hm => ?_⟩
  have hn' := hN n hn
  have hm' := hN m hm
  have hsub : {w : ContinuousPath ℂ | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)} ⊆
      {w | ∃ t ≤ ((k + 1 : ℕ) : ℝ≥0), (1 / 2 : ℝ) ^ (k + 2) ≤ |clockApprox γ a n w t - F w t|} ∪
      {w | ∃ t ≤ ((k + 1 : ℕ) : ℝ≥0), (1 / 2 : ℝ) ^ (k + 2) ≤ |clockApprox γ a m w t - F w t|} := by
    intro w hw
    by_contra hcon
    have hn_lt : ∀ t ≤ ((k + 1 : ℕ) : ℝ≥0), |clockApprox γ a n w t - F w t| < (1 / 2 : ℝ) ^ (k + 2) :=
      fun t ht => lt_of_not_ge (fun h => hcon (Or.inl ⟨t, ht, h⟩))
    have hm_lt : ∀ t ≤ ((k + 1 : ℕ) : ℝ≥0), |clockApprox γ a m w t - F w t| < (1 / 2 : ℝ) ^ (k + 2) :=
      fun t ht => lt_of_not_ge (fun h => hcon (Or.inr ⟨t, ht, h⟩))
    have hdist := pathDist_le_of_abs_le (f := clockApprox γ a n w) (g := clockApprox γ a m w)
      (η := 2 * (1 / 2 : ℝ) ^ (k + 2)) (by positivity) (k + 1) (fun t ht => by
        have h1 := hn_lt t ht.2
        have h2 := hm_lt t ht.2
        have htri := abs_sub_le (clockApprox γ a n w t) (F w t) (clockApprox γ a m w t)
        rw [abs_sub_comm (F w t)] at htri
        linarith)
    have heq : 2 * (1 / 2 : ℝ) ^ (k + 2) + (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k := by ring
    have hw' : (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w) := hw
    linarith
  have hsum : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
      ≤ planarBrownianMotion z _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ < ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) :=
        ENNReal.add_lt_add hn' hm'
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := hsum

/-- The complement of the good set `G_K` has measure at most `2^{-K}` (union bound over the tails `D_m`, `m > K`). -/
lemma measure_compl_goodSet_le {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} (htail : SubsequenceTailProperty γ nsel)
    {a : CircleFns} {z : ℂ} (hC : CauchyInProbability γ a z) (K : ℕ) :
    planarBrownianMotion z (goodSet γ nsel a z K)ᶜ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
  have hsub : (goodSet γ nsel a z K)ᶜ ⊆ ⋃ i : ℕ, {w : ContinuousPath ℂ | (1 / 2 : ℝ) ^ (K + 1 + i) <
      pathDist (clockApprox γ a (nsel a z (K + 1 + i)) w) (clockApprox γ a (nsel a z (K + 1 + i + 1)) w)} := by
    intro w hw
    have hw' : ¬ ∀ m, K + 1 ≤ m → pathDist (clockApprox γ a (nsel a z m) w)
        (clockApprox γ a (nsel a z (m + 1)) w) ≤ (1 / 2 : ℝ) ^ m := hw
    obtain ⟨m, hm⟩ := not_forall.mp hw'
    obtain ⟨hKm, hlt⟩ := not_imp.mp hm
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hKm
    exact mem_iUnion.mpr ⟨i, not_le.mp hlt⟩
  have hbound := measure_iUnion_half_pow_le (planarBrownianMotion z)
    (fun m => {w : ContinuousPath ℂ | (1 / 2 : ℝ) ^ m <
      pathDist (clockApprox γ a (nsel a z m) w) (clockApprox γ a (nsel a z (m + 1)) w)}) K
    (fun m hm => (htail.2 a z hC m (by omega) (nsel a z m) (nsel a z (m + 1)) le_rfl
      ((htail.1 a z).monotone (Nat.le_succ m))).le)
  exact (measure_mono hsub).trans hbound

/-- `⋃_K G_K` has full `W_z`-measure. -/
lemma measure_iUnion_goodSet_compl {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ}
    (htail : SubsequenceTailProperty γ nsel) {a : CircleFns} {z : ℂ} (hC : CauchyInProbability γ a z) :
    planarBrownianMotion z (⋃ K : ℕ, goodSet γ nsel a z K)ᶜ = 0 := by
  have ht : Tendsto (fun K : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ K)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
    simpa using h
  refine le_antisymm (ge_of_tendsto ht (Eventually.of_forall fun K => ?_)) (zero_le)
  exact (measure_mono (compl_subset_compl.mpr (subset_iUnion (goodSet γ nsel a z) K))).trans
    (measure_compl_goodSet_le htail hC K)

/-- On `G_K` the selected approximations converge locally uniformly, to the value of `clockLimit`. -/
lemma clockLimit_tendsto_of_goodSet {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} {a : CircleFns} {z : ℂ}
    {w : ContinuousPath ℂ} {K : ℕ} (hw : w ∈ goodSet γ nsel a z K) :
    TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) (clockLimit γ nsel a z w) atTop := by
  have hex : ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop := by
    obtain ⟨L, -, hL⟩ := tail_tendstoLocallyUniformly (K := K + 1)
      (f := fun k => clockApprox γ a (nsel a z k) w) (fun k => continuous_clockApprox γ a (nsel a z k) w) hw
    exact ⟨L, hL⟩
  unfold clockLimit
  split_ifs
  exact hex.choose_spec

/-- The exceptional sets have measure zero: on `G_K`, `J(a,z,·)` is the locally uniform limit, and the limit of the
probabilities of `{ η/2 ≤ |A_{n_k} - F| }` tends to `0` (outer-measure argument of env-steps.tex:438-446). -/
theorem measure_badSet_eq_zero {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} (htail : SubsequenceTailProperty γ nsel)
    {a : CircleFns} {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hL : IsLQGClock planarBrownianMotion γ (posCircleExt a) z F) (T : ℕ) {η : ℝ} (hη : 0 < η) :
    planarBrownianMotion z (badSet γ nsel a z F T η) = 0 := by
  have hC : CauchyInProbability γ a z := cauchyInProbability_of_isLQGClock hL
  have hYto : Tendsto (fun k => planarBrownianMotion z
      {w : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |clockApprox γ a (nsel a z k) w t - F w t|})
      atTop (𝓝 0) :=
    (hL (T : ℝ≥0) (η / 2) (by positivity)).comp (htail.1 a z).tendsto_atTop
  have hZnull : ∀ k0 : ℕ, planarBrownianMotion z
      {w : ContinuousPath ℂ | ∀ k, k0 ≤ k → ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |clockApprox γ a (nsel a z k) w t - F w t|} = 0 := by
    intro k0
    refine le_antisymm (ge_of_tendsto hYto (eventually_atTop.mpr ⟨k0, fun k hk => measure_mono ?_⟩)) (zero_le)
    intro w hw
    exact hw k hk
  have hcover : badSet γ nsel a z F T η ⊆ (⋃ K : ℕ, goodSet γ nsel a z K)ᶜ ∪
      ⋃ k0 : ℕ, {w : ContinuousPath ℂ | ∀ k, k0 ≤ k →
        ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |clockApprox γ a (nsel a z k) w t - F w t|} := by
    intro w hw
    obtain ⟨t, ht, hdiff⟩ := hw
    by_cases hgw : w ∈ ⋃ K : ℕ, goodSet γ nsel a z K
    · obtain ⟨K, hK⟩ := mem_iUnion.mp hgw
      have hconv := tendsto_at_of_tendstoLocallyUniformly (clockLimit_tendsto_of_goodSet hK) t
      obtain ⟨k0, hk0⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hconv (η / 2) (by positivity))
      refine mem_union_right _ (mem_iUnion.mpr ⟨k0, fun k hk => ⟨t, ht, ?_⟩⟩)
      have h1 := hk0 k hk
      rw [Real.dist_eq, abs_sub_comm] at h1
      have htri := abs_sub_le (clockLimit γ nsel a z w t) (clockApprox γ a (nsel a z k) w t) (F w t)
      linarith
    · exact mem_union_left _ hgw
  exact measure_mono_null hcover
    (measure_union_null (measure_iUnion_goodSet_compl htail hC) (measure_iUnion_null hZnull))

/-- (⇒, a.s. identity) For an admitted clock `F`, `J(a,z,·) = F` almost surely. -/
theorem ae_clockLimit_eq_of_isLQGClock {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ}
    (htail : SubsequenceTailProperty γ nsel) {a : CircleFns} {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hL : IsLQGClock planarBrownianMotion γ (posCircleExt a) z F) :
    ∀ᵐ w ∂planarBrownianMotion z, clockLimit γ nsel a z w = F w := by
  have hae : ∀ᵐ w ∂planarBrownianMotion z, ∀ T : ℕ, ∀ m : ℕ,
      w ∉ badSet γ nsel a z F T (1 / ((m : ℝ) + 1)) := by
    rw [ae_all_iff]
    intro T
    rw [ae_all_iff]
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    refine ae_iff.mpr ?_
    simpa using measure_badSet_eq_zero htail hL T hpos
  filter_upwards [hae] with w hw
  funext t
  by_contra hne
  have hd : 0 < |clockLimit γ nsel a z w t - F w t| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hd
  exact hw ⌈(t : ℝ)⌉₊ m ⟨t, by exact_mod_cast Nat.le_ceil (t : ℝ), hm.le⟩

/-- (⇒) An admitted clock gives the selected relation for every starting point. -/
theorem selected_of_admits {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} (htail : SubsequenceTailProperty γ nsel)
    {a : CircleFns} (hA : AdmitsAllStartClock γ a) (z : ℂ) : SelectedAllStartsRelation γ nsel a z := by
  obtain ⟨F, hF⟩ := hA
  have hL : IsLQGClock planarBrownianMotion γ (posCircleExt a) z F := (hF z).1
  have hT : ∀ᵐ w ∂planarBrownianMotion z, IsTimeChangeClock (F w) := (hF z).2
  refine ⟨cauchyInProbability_of_isLQGClock hL, ?_⟩
  filter_upwards [ae_clockLimit_eq_of_isLQGClock htail hL, hT] with w h1 h2
  rw [h1]
  exact h2

/-- (⇐) The selected relation for `z` gives the locally uniform convergence to `J(B 0, B)` in `W_z`-probability. -/
theorem isLQGClock_of_selected {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ}
    (htail : SubsequenceTailProperty γ nsel) {a : CircleFns} {z : ℂ}
    (hz : SelectedAllStartsRelation γ nsel a z) :
    IsLQGClock planarBrownianMotion γ (posCircleExt a) z (fun B => clockLimit γ nsel a (B 0) B) := by
  intro T η hη
  have hC : CauchyInProbability γ a z := hz.1
  have hae : ∀ᵐ B ∂planarBrownianMotion z, B 0 = z := ae_planarBrownianMotion_eval_zero z
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hrlt, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hrlt
  set J : ℕ := ⌈(T : ℝ)⌉₊ with hJ
  have hTJ : (T : ℝ≥0) ≤ (J : ℝ≥0) := by exact_mod_cast Nat.le_ceil (T : ℝ)
  have hcpos : 0 < min (min (r / 3) (η / 2 / 2 ^ (J + 2))) ((1 / 2 : ℝ) ^ (J + 1) * min 1 (η / 2)) := by
    refine lt_min (lt_min (div_pos hrpos (by norm_num)) (div_pos (div_pos hη (by norm_num)) (by positivity)))
      (mul_pos (by positivity) (lt_min one_pos (div_pos hη (by norm_num))))
  obtain ⟨k1, hk1⟩ := exists_pow_lt_of_lt_one hcpos (by norm_num : (1 / 2 : ℝ) < 1)
  set K : ℕ := k1 + J + 4 with hK
  have hKk1 : (1 / 2 : ℝ) ^ (K + 1) ≤ (1 / 2 : ℝ) ^ k1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hc1 : (1 / 2 : ℝ) ^ (K + 1) < r / 3 :=
    lt_of_le_of_lt hKk1 (lt_of_lt_of_le hk1 ((min_le_left _ _).trans (min_le_left _ _)))
  have hc2 : (1 / 2 : ℝ) ^ (K + 1) < η / 2 / 2 ^ (J + 2) :=
    lt_of_le_of_lt hKk1 (lt_of_lt_of_le hk1 ((min_le_left _ _).trans (min_le_right _ _)))
  have hc3 : (1 / 2 : ℝ) ^ (K + 1) < (1 / 2 : ℝ) ^ (J + 1) * min 1 (η / 2) :=
    lt_of_le_of_lt hKk1 (lt_of_lt_of_le hk1 (min_le_right _ _))
  have hK2 : (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ (K + 1) < η / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (J + 2))).mp hc2
    linarith [this, mul_comm ((1 / 2 : ℝ) ^ (K + 1)) ((2 : ℝ) ^ (J + 2))]
  filter_upwards [eventually_ge_atTop (nsel a z (K + 1))] with n hn
  -- Step A: replace `h^{(B 0)}`-clock by the clock at `z` (almost surely `B 0 = z`).
  have hA : planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
      η ≤ |clockApprox γ a n B t - clockLimit γ nsel a (B 0) B t|}
      ≤ planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
        η ≤ |clockApprox γ a n B t - clockLimit γ nsel a z B t|} := by
    refine measure_mono_ae (hae.mono fun B h0 hB => ?_)
    obtain ⟨t, ht, h⟩ := hB
    rw [h0] at h
    exact ⟨t, ht, h⟩
  -- Step B: split at the approximation with index `nsel (K+1)`.
  have hB : planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
      η ≤ |clockApprox γ a n B t - clockLimit γ nsel a z B t|}
      ≤ planarBrownianMotion z
        ({B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
            η / 2 ≤ |clockApprox γ a n B t - clockApprox γ a (nsel a z (K + 1)) B t|} ∪
          {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
            η / 2 ≤ |clockApprox γ a (nsel a z (K + 1)) B t - clockLimit γ nsel a z B t|}) := by
    refine measure_mono ?_
    rintro B ⟨t, ht, h⟩
    have htri := abs_sub_le (clockApprox γ a n B t) (clockApprox γ a (nsel a z (K + 1)) B t)
      (clockLimit γ nsel a z B t)
    by_cases h1 : η / 2 ≤ |clockApprox γ a n B t - clockApprox γ a (nsel a z (K + 1)) B t|
    · exact Or.inl ⟨t, ht, h1⟩
    · refine Or.inr ⟨t, ht, ?_⟩
      linarith [not_le.mp h1]
  -- Step C: the first piece has measure `< 2^{-(K+1)}` (pathDist tail at index `K+1`, `n ≥ nsel (K+1)`).
  have hE : planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
      η / 2 ≤ |clockApprox γ a n B t - clockApprox γ a (nsel a z (K + 1)) B t|}
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (K + 1)) := by
    refine le_trans (measure_mono ?_)
      (htail.2 a z hC (K + 1) (by omega) n (nsel a z (K + 1)) hn le_rfl).le
    rintro B ⟨t, ht, h⟩
    have htJ : t ∈ Icc (0 : ℝ≥0) ((J + 1 : ℕ) : ℝ≥0) :=
      ⟨by positivity, le_trans ht (le_trans hTJ (by exact_mod_cast Nat.le_succ J))⟩
    have hmin : min 1 (η / 2) ≤
        min 1 |clockApprox γ a n B t - clockApprox γ a (nsel a z (K + 1)) B t| :=
      min_le_min_left _ h
    have hp := half_pow_min_le_pathDist (continuous_clockApprox γ a n B)
      (continuous_clockApprox γ a (nsel a z (K + 1)) B) htJ
    have hmul : (1 / 2 : ℝ) ^ (J + 1) * min 1 (η / 2) ≤
        (1 / 2 : ℝ) ^ (J + 1) * min 1 |clockApprox γ a n B t - clockApprox γ a (nsel a z (K + 1)) B t| :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    show (1 / 2 : ℝ) ^ (K + 1) < pathDist (clockApprox γ a n B) (clockApprox γ a (nsel a z (K + 1)) B)
    linarith [hc3, hmul, hp]
  -- Step D: the second piece lies in the complement of `G_K` (on `G_K` the limit is within `2^{J+2} 2^{-(K+1)}`).
  have hS : planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
      η / 2 ≤ |clockApprox γ a (nsel a z (K + 1)) B t - clockLimit γ nsel a z B t|}
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
    refine le_trans (measure_mono ?_) (measure_compl_goodSet_le htail hC K)
    rintro B ⟨t, ht, h⟩ hG
    have hb := tail_abs_le_limit (f := fun m => clockApprox γ a (nsel a z m) B)
      (fun m => continuous_clockApprox γ a (nsel a z m) B) (K := K + 1) hG
      (fun t' => tendsto_at_of_tendstoLocallyUniformly (clockLimit_tendsto_of_goodSet hG) t')
      (J := J) (m := K + 1) le_rfl
      (by omega) (show t ∈ Icc (0 : ℝ≥0) (J : ℝ≥0) from ⟨by positivity, le_trans ht hTJ⟩)
    have hb' : |clockApprox γ a (nsel a z (K + 1)) B t - clockLimit γ nsel a z B t|
        ≤ (2 : ℝ) ^ (J + 2) * (1 / 2 : ℝ) ^ (K + 1) := hb
    linarith
  -- Step E: sum the three bounds.
  have hfin : ENNReal.ofReal ((1 / 2 : ℝ) ^ (K + 1)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ K)
      = ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ (K + 1)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hfinal : planarBrownianMotion z {B : ContinuousPath ℂ | ∃ t ≤ (T : ℝ≥0),
      η ≤ |lqgClockApprox γ (posCircleExt a) (dyadicScale n) B t - clockLimit γ nsel a (B 0) B t|}
      ≤ ENNReal.ofReal r := by
    refine hA.trans (hB.trans ((measure_union_le _ _).trans ((add_le_add hE hS).trans ?_)))
    rw [hfin]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact hfinal.trans hrε.le

/-- (⇐) The selected relation for every starting point gives an admitted clock `F(B) = J(B 0, B)`. -/
theorem admitsAllStartClock_of_selected {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ}
    (htail : SubsequenceTailProperty γ nsel) {a : CircleFns} (hS : ∀ z : ℂ, SelectedAllStartsRelation γ nsel a z) :
    AdmitsAllStartClock γ a := by
  refine ⟨fun B => clockLimit γ nsel a (B 0) B, fun z => ⟨isLQGClock_of_selected htail (hS z), ?_⟩⟩
  filter_upwards [ae_planarBrownianMotion_eval_zero z, (hS z).2] with B h0 hB
  show IsTimeChangeClock (clockLimit γ nsel a (B 0) B)
  rw [h0]
  exact hB

/-- **The characterization of lem:allstarts**: `𝒢 = {a : ∀ z, Q(a,z)}` for any subsequence choice with the tail
property. Proved from `SubsequenceTailProperty` (the measurability clause of `BorelSubsequenceSelectionStep` is not
used here). -/
theorem allStartsSet_eq_selected (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ)
    (htail : SubsequenceTailProperty γ nsel) : allStartsSet γ = selectedAllStartsSet γ nsel := by
  ext a
  exact ⟨fun hA z => selected_of_admits htail hA z, fun hS => admitsAllStartClock_of_selected htail hS⟩

end Characterization

/-- The characterization Step `AllStartsCharacterizationStep` holds, given the subsequence tail property. -/
theorem allStartsCharacterization_of_tail (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ)
    (htail : SubsequenceTailProperty γ nsel) : AllStartsCharacterizationStep γ nsel :=
  allStartsSet_eq_selected γ nsel htail

/-! ### Measurability of the selection (lem:allstarts proof, env-steps.tex:380-421)

`CircleFns = C(Set.Ioi 0 × ℂ, ℝ)` and `ContinuousPath ℂ = C(ℝ≥0, ℂ)` carry Mathlib's compact-open Borel structure
(`ContinuousMap.measurableSpace`, `BorelSpace`), and both are second countable (`ContinuousMap.instSecondCountableTopology`:
the domains are locally compact and second countable). Hence continuous maps on their product are measurable. The
selection below is the recursive choice of env-steps.tex:404-411, made total by a fallback index. -/

section Measurability

open Set Topology MeasureTheory Filter ProbabilityTheory

lemma allStarts_dyadicScale_pos (n : ℕ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

/-- The clock approximation as an integral of the positive-circle evaluation at the dyadic radius. -/
lemma clockApprox_eq_integral (γ : ℝ) (a : CircleFns) (n : ℕ) (w : ContinuousPath ℂ) (t : ℝ≥0) :
    clockApprox γ a n w t = ∫ s in (0 : ℝ)..(t : ℝ),
      dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * a (⟨dyadicScale n, allStarts_dyadicScale_pos n⟩, w s.toNNReal)) := by
  unfold clockApprox lqgClockApprox
  simp [posCircleExt, allStarts_dyadicScale_pos n]

/-- The open half-line `(0, ∞)` is locally compact, so the positive-circle domain `E = (0,∞) × ℂ` is too
(needed for the joint evaluation `ContinuousEval` on `C(E, ℝ)`). -/
instance Ioi_zero_locallyCompactSpace : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- The clock approximation is jointly continuous in `(a, w, t)` (env-steps.tex:395-397). -/
theorem continuous_clockApprox_joint (γ : ℝ) (n : ℕ) :
    Continuous fun x : CircleFns × ContinuousPath ℂ × ℝ≥0 => clockApprox γ x.1 n x.2.1 x.2.2 := by
  set p0 : Set.Ioi (0 : ℝ) := ⟨dyadicScale n, allStarts_dyadicScale_pos n⟩ with hp0
  have hw : Continuous fun q : (CircleFns × ContinuousPath ℂ × ℝ≥0) × ℝ => q.1.2.1 q.2.toNNReal :=
    continuous_eval.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_real_toNNReal.comp continuous_snd))
  have ha : Continuous fun q : (CircleFns × ContinuousPath ℂ × ℝ≥0) × ℝ =>
      q.1.1 (p0, q.1.2.1 q.2.toNNReal) :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_const.prodMk hw))
  have hf : Continuous fun q : (CircleFns × ContinuousPath ℂ × ℝ≥0) × ℝ =>
      dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * q.1.1 (p0, q.1.2.1 q.2.toNNReal)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ha))
  have hs : Continuous fun x : CircleFns × ContinuousPath ℂ × ℝ≥0 => (x.2.2 : ℝ) :=
    NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd)
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (μ := MeasureTheory.volume)
    (f := fun (x : CircleFns × ContinuousPath ℂ × ℝ≥0) (s : ℝ) =>
      dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * x.1 (p0, x.2.1 s.toNNReal))) hf hs
  have heq : (fun x : CircleFns × ContinuousPath ℂ × ℝ≥0 => clockApprox γ x.1 n x.2.1 x.2.2) =
      fun x => ∫ s in (0 : ℝ)..(x.2.2 : ℝ),
        dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * x.1 (p0, x.2.1 s.toNNReal)) := by
    funext x
    exact clockApprox_eq_integral γ x.1 n x.2.1 x.2.2
  rw [heq]
  exact hint

/-- A supremum over a set equals the supremum over its image, for nonnegative functions (real `⨆` vs `sSup`). -/
lemma iSup_mem_eq_sSup_image {h : ℝ≥0 → ℝ} {K : Set ℝ≥0} (hne : K.Nonempty) (hbdd : BddAbove (h '' K))
    (hnn : ∀ t, 0 ≤ h t) : (⨆ t ∈ K, h t) = sSup (h '' K) := by
  obtain ⟨t0, ht0⟩ := hne
  have hsup0 : 0 ≤ sSup (h '' K) := le_trans (hnn t0) (le_csSup hbdd ⟨t0, ht0, rfl⟩)
  have hle : ∀ t, (⨆ (_ : t ∈ K), h t) ≤ sSup (h '' K) := by
    intro t
    by_cases ht : t ∈ K
    · rw [ciSup_pos ht]
      exact le_csSup hbdd ⟨t, ht, rfl⟩
    · rw [ciSup_neg ht, Real.sSup_empty]
      exact hsup0
  apply le_antisymm
  · exact ciSup_le hle
  · refine csSup_le (Set.Nonempty.image h ⟨t0, ht0⟩) ?_
    rintro y ⟨t, ht, rfl⟩
    have hbdd' : BddAbove (Set.range fun t' : ℝ≥0 => ⨆ (_ : t' ∈ K), h t') :=
      ⟨sSup (h '' K), by rintro _ ⟨t', rfl⟩; exact hle t'⟩
    exact le_ciSup_of_le hbdd' t (ciSup_pos (f := fun _ : t ∈ K => h t) ht).ge

/-- Continuity of `x ↦ ⨆ t ∈ K, h x t` for a jointly continuous nonnegative family and a compact `K`. -/
lemma continuous_iSup_mem_of_isCompact {X : Type*} [TopologicalSpace X] {h : X → ℝ≥0 → ℝ}
    (hc : Continuous fun q : X × ℝ≥0 => h q.1 q.2) {K : Set ℝ≥0} (hK : IsCompact K) (hne : K.Nonempty)
    (hnn : ∀ x t, 0 ≤ h x t) : Continuous fun x => ⨆ t ∈ K, h x t := by
  have hcx : ∀ x, Continuous (h x) := fun x => hc.comp (continuous_const.prodMk continuous_id)
  have heq : (fun x => ⨆ t ∈ K, h x t) = fun x => sSup (h x '' K) := by
    funext x
    exact iSup_mem_eq_sSup_image hne ((hK.image (hcx x)).bddAbove) (hnn x)
  rw [heq]
  exact hK.continuous_sSup hc

/-- Each summand of `pathDist` between two clock approximations is continuous in `(a, w)`. -/
theorem continuous_pathDist_summand (γ : ℝ) (n m j : ℕ) :
    Continuous fun x : CircleFns × ContinuousPath ℂ =>
      (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0),
        |clockApprox γ x.1 n x.2 t - clockApprox γ x.1 m x.2 t|) := by
  have hq : Continuous fun q : (CircleFns × ContinuousPath ℂ) × ℝ≥0 => (q.1.1, q.1.2, q.2) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hjoint : Continuous fun q : (CircleFns × ContinuousPath ℂ) × ℝ≥0 =>
      |clockApprox γ q.1.1 n q.1.2 q.2 - clockApprox γ q.1.1 m q.1.2 q.2| :=
    (((continuous_clockApprox_joint γ n).comp hq).sub ((continuous_clockApprox_joint γ m).comp hq)).abs
  have hK : IsCompact (Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)) := isCompact_Icc
  have hne : (Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0)).Nonempty := Set.nonempty_Icc.mpr (by positivity)
  have hsup := continuous_iSup_mem_of_isCompact
    (h := fun (x : CircleFns × ContinuousPath ℂ) (t : ℝ≥0) =>
      |clockApprox γ x.1 n x.2 t - clockApprox γ x.1 m x.2 t|) hjoint hK hne (fun x t => abs_nonneg _)
  exact continuous_const.mul (continuous_const.min hsup)

/-- `pathDist` between two clock approximations is continuous in `(a, w)` (env-steps.tex:398-400). -/
theorem continuous_pathDist_clockApprox (γ : ℝ) (n m : ℕ) :
    Continuous fun x : CircleFns × ContinuousPath ℂ =>
      pathDist (clockApprox γ x.1 n x.2) (clockApprox γ x.1 m x.2) := by
  unfold pathDist
  refine continuous_tsum (fun j => continuous_pathDist_summand γ n m j) summable_half_pow_succ ?_
  intro j x
  rw [Real.norm_of_nonneg (pathDist_summand_nonneg _ _ j)]
  exact pathDist_summand_le_half_pow _ _ j

/-- `(a, z) ↦ W_z {w | (a, w) ∈ U}` is measurable for measurable `U` (kernel section lemma). -/
theorem measurable_planarBM_section {U : Set (CircleFns × ContinuousPath ℂ)} (hU : MeasurableSet U) :
    Measurable fun p : CircleFns × ℂ => planarBrownianMotion p.2 {w | (p.1, w) ∈ U} := by
  let κ : Kernel (CircleFns × ℂ) (ContinuousPath ℂ) := planarBrownianMotion.comap Prod.snd measurable_snd
  have ht : MeasurableSet {q : (CircleFns × ℂ) × ContinuousPath ℂ | (q.1.1, q.2) ∈ U} :=
    hU.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact Kernel.measurable_kernel_prodMk_left (κ := κ) ht

/-- The level-`k` tail bound from index `N` (the form of eq:cauchy, env-steps.tex:398-402). -/
def tailBelow (γ : ℝ) (k N : ℕ) (a : CircleFns) (z : ℂ) : Prop :=
  ∀ n m : ℕ, N ≤ n → N ≤ m →
    planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
      < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)

lemma allStarts_measurableSet_imp {α : Type*} [MeasurableSpace α] {c : Prop} {S : Set α}
    (hS : MeasurableSet S) : MeasurableSet {p : α | c → p ∈ S} := by
  by_cases hc : c
  · simpa [hc] using hS
  · simp [hc]

/-- The tail bound is measurable in the starting data `(a, z)`. -/
theorem measurableSet_tailBelow (γ : ℝ) (k N : ℕ) :
    MeasurableSet {p : CircleFns × ℂ | tailBelow γ k N p.1 p.2} := by
  have hset : {p : CircleFns × ℂ | tailBelow γ k N p.1 p.2} = ⋂ n : ℕ, ⋂ m : ℕ,
      {p : CircleFns × ℂ | (N ≤ n ∧ N ≤ m) →
        planarBrownianMotion p.2
            {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ p.1 n w) (clockApprox γ p.1 m w)}
          < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)} := by
    ext p
    simp only [tailBelow, Set.mem_ofPred_eq, mem_iInter, and_imp]
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => ?_
  have hU : MeasurableSet {x : CircleFns × ContinuousPath ℂ |
      (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ x.1 n x.2) (clockApprox γ x.1 m x.2)} :=
    measurableSet_lt measurable_const (continuous_pathDist_clockApprox γ n m).measurable
  exact allStarts_measurableSet_imp (measurableSet_lt (measurable_planarBM_section hU) measurable_const)

/-- The predicate selecting the `(k+1)`-th index: an index `N ≥ prev + 1` at which the level-`(k+1)` tail bound holds,
or, when there is none, the fallback `prev + 1`. -/
def selPred (γ : ℝ) (k : ℕ) (prev : CircleFns × ℂ → ℕ) (p : CircleFns × ℂ) (N : ℕ) : Prop :=
  (prev p + 1 ≤ N ∧ tailBelow γ (k + 1) N p.1 p.2) ∨
    ((¬ ∃ N' : ℕ, prev p + 1 ≤ N' ∧ tailBelow γ (k + 1) N' p.1 p.2) ∧ N = prev p + 1)

theorem exists_selPred (γ : ℝ) (k : ℕ) (prev : CircleFns × ℂ → ℕ) (p : CircleFns × ℂ) :
    ∃ N, selPred γ k prev p N := by
  by_cases h : ∃ N' : ℕ, prev p + 1 ≤ N' ∧ tailBelow γ (k + 1) N' p.1 p.2
  · obtain ⟨N', hN'⟩ := h
    exact ⟨N', Or.inl hN'⟩
  · exact ⟨prev p + 1, Or.inr ⟨h, rfl⟩⟩

theorem measurableSet_selPred (γ : ℝ) (k : ℕ) {prev : CircleFns × ℂ → ℕ} (hprev : Measurable prev) (N : ℕ) :
    MeasurableSet {p : CircleFns × ℂ | selPred γ k prev p N} := by
  have hA : MeasurableSet {p : CircleFns × ℂ | prev p + 1 ≤ N} :=
    measurableSet_le (hprev.add_const 1) measurable_const
  have hB : MeasurableSet {p : CircleFns × ℂ | ∃ N' : ℕ, prev p + 1 ≤ N' ∧ tailBelow γ (k + 1) N' p.1 p.2} := by
    have hU : {p : CircleFns × ℂ | ∃ N' : ℕ, prev p + 1 ≤ N' ∧ tailBelow γ (k + 1) N' p.1 p.2}
        = ⋃ N' : ℕ, ({p : CircleFns × ℂ | prev p + 1 ≤ N'} ∩
            {p : CircleFns × ℂ | tailBelow γ (k + 1) N' p.1 p.2}) := by
      ext p
      simp only [Set.mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [hU]
    exact MeasurableSet.iUnion fun N' =>
      (measurableSet_le (hprev.add_const 1) measurable_const).inter (measurableSet_tailBelow γ (k + 1) N')
  have hC : MeasurableSet {p : CircleFns × ℂ | N = prev p + 1} :=
    measurableSet_eq_fun measurable_const (hprev.add_const 1)
  exact (hA.inter (measurableSet_tailBelow γ (k + 1) N)).union (hB.compl.inter hC)

/-- One selection step: the least index `N` with `selPred` (exists by `exists_selPred`). -/
noncomputable def nselStep (γ : ℝ) (k : ℕ) (prev : CircleFns × ℂ → ℕ) (p : CircleFns × ℂ) : ℕ := by
  classical
  exact Nat.find (exists_selPred γ k prev p)

theorem measurable_nselStep (γ : ℝ) (k : ℕ) {prev : CircleFns × ℂ → ℕ} (hprev : Measurable prev) :
    Measurable (nselStep γ k prev) := by
  classical
  exact measurable_find (exists_selPred γ k prev) (measurableSet_selPred γ k hprev)

/-- The subsequence choice `k ↦ n_k(a,z)` of lem:allstarts (env-steps.tex:404-411), by recursion on `k`. -/
noncomputable def nselSeq (γ : ℝ) : ℕ → CircleFns × ℂ → ℕ
  | 0 => fun _ => 0
  | k + 1 => nselStep γ k (nselSeq γ k)

theorem measurable_nselSeq (γ : ℝ) (k : ℕ) : Measurable (nselSeq γ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact measurable_nselStep γ k ih

theorem nselSeq_lt_succ (γ : ℝ) (k : ℕ) (p : CircleFns × ℂ) : nselSeq γ k p < nselSeq γ (k + 1) p := by
  classical
  show nselSeq γ k p < nselStep γ k (nselSeq γ k) p
  have hspec := Nat.find_spec (exists_selPred γ k (nselSeq γ k) p)
  unfold nselStep
  rcases hspec with ⟨h1, _⟩ | ⟨_, h2⟩
  · omega
  · omega

theorem nselSeq_tail (γ : ℝ) (a : CircleFns) (z : ℂ) (hC : CauchyInProbability γ a z) (k : ℕ) (hk : 1 ≤ k) :
    ∀ n m : ℕ, nselSeq γ k (a, z) ≤ n → nselSeq γ k (a, z) ≤ m →
      planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
        < ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨N0, hN0⟩ := hC (j + 1) (by omega)
  have hex : ∃ N' : ℕ, nselSeq γ j (a, z) + 1 ≤ N' ∧ tailBelow γ (j + 1) N' a z :=
    ⟨max (nselSeq γ j (a, z) + 1) N0, le_max_left _ _, fun n' m' h1 h2 =>
      hN0 n' m' ((le_max_right _ _).trans h1) ((le_max_right _ _).trans h2)⟩
  have hspec := Nat.find_spec (exists_selPred γ j (nselSeq γ j) (a, z))
  intro n m hn hm
  rcases hspec with ⟨_, ht⟩ | ⟨hnot, _⟩
  · exact ht n m hn hm
  · exact absurd hex hnot

/-- The subsequence choice as a function of the starting data `(a, z)` and of the index `k`. -/
noncomputable def nselFun (γ : ℝ) (a : CircleFns) (z : ℂ) (k : ℕ) : ℕ := nselSeq γ k (a, z)

/-- **The selection Step `BorelSubsequenceSelectionStep` holds** for the constructed subsequence `nselFun`
(lem:allstarts proof, env-steps.tex:404-411): Borel in `(a, z)`, strictly increasing in `k`, with the tail bound. -/
theorem borelSubsequenceSelectionStep_nselFun (γ : ℝ) : BorelSubsequenceSelectionStep γ (nselFun γ) :=
  ⟨fun k => measurable_nselSeq γ k,
    (fun a z => strictMono_nat_of_lt_succ fun k => nselSeq_lt_succ γ k (a, z)),
    fun a z hC k hk n m hn hm => nselSeq_tail γ a z hC k hk n m hn hm⟩

/-- **Rational reduction of `𝒯_*`** (env-steps.tex:413-416): for a continuous `f`, `f` is an `IsTimeChangeClock` iff
`f 0 = 0`, `f` is strictly increasing on the nonnegative rationals, and `f` is unbounded on the naturals. -/
theorem isTimeChangeClock_iff_rat {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    IsTimeChangeClock f ↔ f 0 = 0 ∧
      (∀ q r : ℚ, 0 ≤ q → q < r → f (q : ℝ).toNNReal < f (r : ℝ).toNNReal) ∧
      ∀ M : ℕ, ∃ N : ℕ, (M : ℝ) < f (N : ℝ≥0) := by
  constructor
  · intro h
    refine ⟨h.map_zero, fun q r hq hqr => ?_, fun M => ?_⟩
    · have hq' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hqr' : (q : ℝ) < (r : ℝ) := by exact_mod_cast hqr
      exact h.strictMono ((Real.toNNReal_lt_toNNReal_iff (by linarith)).mpr hqr')
    · obtain ⟨N, hN⟩ := ((h.tendsto_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (M : ℝ)).exists
      exact ⟨N, hN⟩
  · rintro ⟨h0, hrat, hunb⟩
    have hsm : StrictMono f := by
      intro x y hxy
      have hxy' : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
      obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy'
      obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := le_trans (NNReal.coe_nonneg x) hxa.le
      have ha0' : (0 : ℚ) ≤ a := by exact_mod_cast ha0
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := le_trans ha0 hab.le
      have hb0' : (0 : ℚ) ≤ b := by exact_mod_cast hb0
      have hab' : a < b := by exact_mod_cast hab
      -- `f x ≤ f a`: otherwise, continuity at `x` forces `f a < f r` for rationals `r` close to `x`, contradicting `f r < f a`.
      have hxa_le : f x ≤ f (a : ℝ).toNNReal := by
        by_contra hlt
        rw [not_le] at hlt
        have hev : ∀ᶠ t in 𝓝 x, f (a : ℝ).toNNReal < f t :=
          hf.continuousAt.eventually (lt_mem_nhds hlt)
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
        obtain ⟨r, hxr, hra⟩ := exists_rat_btwn
          (lt_min hxa (show (x : ℝ) < (x : ℝ) + ε by linarith))
        have hr1 : (r : ℝ) < a := lt_of_lt_of_le hra (min_le_left _ _)
        have hr2 : (r : ℝ) < (x : ℝ) + ε := lt_of_lt_of_le hra (min_le_right _ _)
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := le_trans (NNReal.coe_nonneg x) hxr.le
        have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
        have hdist : dist (r : ℝ).toNNReal x < ε := by
          rw [NNReal.dist_eq, Real.coe_toNNReal _ hr0, abs_lt]
          constructor <;> linarith
        have h1 := hball hdist
        have h2 := hrat r a hr0' (by exact_mod_cast hr1)
        exact lt_asymm h1 h2
      -- `f b ≤ f y`: symmetric, using continuity at `y`.
      have hby_le : f (b : ℝ).toNNReal ≤ f y := by
        by_contra hlt
        rw [not_le] at hlt
        have hev : ∀ᶠ t in 𝓝 y, f t < f (b : ℝ).toNNReal :=
          hf.continuousAt.eventually (gt_mem_nhds hlt)
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
        obtain ⟨r, hbr, hry⟩ := exists_rat_btwn
          (show max (b : ℝ) ((y : ℝ) - ε) < (y : ℝ) from max_lt hby (by linarith))
        have hr1 : (b : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hbr
        have hr2 : (y : ℝ) - ε < r := lt_of_le_of_lt (le_max_right _ _) hbr
        have hr0 : (0 : ℝ) ≤ (b : ℝ) := hb0
        have hr0' : (0 : ℚ) ≤ b := hb0'
        have hdist : dist (r : ℝ).toNNReal y < ε := by
          rw [NNReal.dist_eq, Real.coe_toNNReal _ (le_trans hr0 hr1.le), abs_lt]
          constructor <;> linarith
        have h1 := hball hdist
        have h2 := hrat b r hr0' (by exact_mod_cast hr1)
        exact lt_asymm h2 h1
      have hab_lt : f (a : ℝ).toNNReal < f (b : ℝ).toNNReal := hrat a b ha0' hab'
      exact lt_of_le_of_lt hxa_le (lt_of_lt_of_le hab_lt hby_le)
    refine ⟨h0, hf, hsm, Monotone.tendsto_atTop_atTop hsm.monotone fun b => ?_⟩
    obtain ⟨N, hN⟩ := hunb ⌈b⌉₊
    exact ⟨(N : ℝ≥0), le_trans (Nat.le_ceil b) hN.le⟩

/-- The Cauchy-in-probability relation is Borel in `(a, z)` (the countable form of eq:cauchy). -/
theorem measurableSet_cauchyInProbability (γ : ℝ) :
    MeasurableSet {p : CircleFns × ℂ | CauchyInProbability γ p.1 p.2} := by
  have hset : {p : CircleFns × ℂ | CauchyInProbability γ p.1 p.2} = ⋂ k : ℕ,
      {p : CircleFns × ℂ | 1 ≤ k → ∃ N : ℕ, tailBelow γ k N p.1 p.2} := by
    ext p
    rw [Set.mem_iInter]
    exact Iff.rfl
  rw [hset]
  refine MeasurableSet.iInter fun k => ?_
  have hex : MeasurableSet {p : CircleFns × ℂ | ∃ N : ℕ, tailBelow γ k N p.1 p.2} := by
    have hU : {p : CircleFns × ℂ | ∃ N : ℕ, tailBelow γ k N p.1 p.2}
        = ⋃ N : ℕ, {p : CircleFns × ℂ | tailBelow γ k N p.1 p.2} := by
      ext p
      rw [Set.mem_iUnion]
      exact Iff.rfl
    rw [hU]
    exact MeasurableSet.iUnion fun N => measurableSet_tailBelow γ k N
  exact allStarts_measurableSet_imp hex

/-! #### The Borel relation `Q` of the selected subsequence (`BorelAllStartsRelationStep`, env-steps.tex:413-421)

For `x = ((a, z), w)` the selected approximations `A_{n_k(a,z)}(a, w)` are Borel in `x` (countable index `n_k(a,z)`,
continuity in `(a, w)`); the pointwise limit `L_t(x) = limsup_k A_{n_k(a,z)}(a,w)(t)` is Borel, and it is the
locally uniform limit on the good set `G = ⋃_K G_K`. On `G` the limit is continuous, so `IsTimeChangeClock` is the
countable rational condition `timeCondRat` (`isTimeChangeClock_iff_rat`). -/

/-- The rational form of `IsTimeChangeClock` (env-steps.tex:413-416): `L 0 = 0`, strict increase on the nonnegative
rationals, and unboundedness on the naturals. -/
def timeCondRat (L : ℝ≥0 → ℝ) : Prop :=
  L 0 = 0 ∧ (∀ q r : ℚ, 0 ≤ q → q < r → L (q : ℝ).toNNReal < L (r : ℝ).toNNReal) ∧
    ∀ M : ℕ, ∃ N : ℕ, (M : ℝ) < L (N : ℝ≥0)

lemma measurableSet_imp_imp {X : Type*} [MeasurableSpace X] {c d : Prop} {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet {x : X | c → d → x ∈ s} :=
  allStarts_measurableSet_imp (allStarts_measurableSet_imp hs)

/-- Measurability of the selected approximations at a fixed time, as functions of `((a,z),w)`. -/
theorem measurable_selApprox (γ : ℝ) (k : ℕ) (t : ℝ≥0) :
    Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ =>
      clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 t := by
  have hH : Measurable fun q : ((CircleFns × ℂ) × ContinuousPath ℂ) × ℕ =>
      clockApprox γ q.1.1.1 q.2 q.1.2 t := by
    refine measurable_from_prod_countable_left fun n => ?_
    have hc : Continuous fun x : (CircleFns × ℂ) × ContinuousPath ℂ => clockApprox γ x.1.1 n x.2 t :=
      (continuous_clockApprox_joint γ n).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.prodMk continuous_const))
    exact hc.measurable
  have hn : Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ => nselFun γ x.1.1 x.1.2 k :=
    (measurable_nselSeq γ k).comp measurable_fst
  exact hH.comp (measurable_id.prodMk hn)

/-- The pointwise limsup of the selected approximations is measurable (`Measurable.limsup`). -/
theorem measurable_selLimit (γ : ℝ) (t : ℝ≥0) :
    Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ =>
      limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 t) atTop :=
  Measurable.limsup fun k => measurable_selApprox γ k t

/-- The selected `pathDist`-steps `d_𝒯(A_{n_m(a,z)}, A_{n_{m+1}(a,z)})` are measurable in `((a,z),w)`. -/
theorem measurable_selPathDist (γ : ℝ) (m : ℕ) :
    Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ =>
      pathDist (clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 m) x.2)
        (clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 (m + 1)) x.2) := by
  have hH : Measurable fun q : ((CircleFns × ℂ) × ContinuousPath ℂ) × (ℕ × ℕ) =>
      pathDist (clockApprox γ q.1.1.1 q.2.1 q.1.2) (clockApprox γ q.1.1.1 q.2.2 q.1.2) := by
    refine measurable_from_prod_countable_left fun nn => ?_
    have hgx : Continuous fun x : (CircleFns × ℂ) × ContinuousPath ℂ => (x.1.1, x.2) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    have hc := (continuous_pathDist_clockApprox γ nn.1 nn.2).comp hgx
    exact hc.measurable
  have hn : Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ =>
      (nselFun γ x.1.1 x.1.2 m, nselFun γ x.1.1 x.1.2 (m + 1)) :=
    ((measurable_nselSeq γ m).comp measurable_fst).prodMk
      ((measurable_nselSeq γ (m + 1)).comp measurable_fst)
  have hcomp := hH.comp (measurable_id.prodMk hn)
  exact hcomp

/-- The union of the good sets `G_K` is a Borel subset of `((a,z),w)` (countable intersections of `pathDist`-bounds). -/
theorem measurableSet_goodUnion (γ : ℝ) :
    MeasurableSet {x : (CircleFns × ℂ) × ContinuousPath ℂ |
      ∃ K : ℕ, x.2 ∈ goodSet γ (nselFun γ) x.1.1 x.1.2 K} := by
  have hset : {x : (CircleFns × ℂ) × ContinuousPath ℂ | ∃ K : ℕ, x.2 ∈ goodSet γ (nselFun γ) x.1.1 x.1.2 K} =
      ⋃ K : ℕ, ⋂ m : ℕ, ⋂ (_ : K + 1 ≤ m),
        {x : (CircleFns × ℂ) × ContinuousPath ℂ | pathDist (clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 m) x.2)
          (clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 (m + 1)) x.2) ≤ (1 / 2 : ℝ) ^ m} := by
    ext x
    constructor
    · rintro ⟨K, hK⟩
      exact mem_iUnion.mpr ⟨K, mem_iInter.mpr fun m => mem_iInter.mpr fun hm => hK m hm⟩
    · intro hx
      obtain ⟨K, hK⟩ := mem_iUnion.mp hx
      exact ⟨K, fun m hm => mem_iInter.mp (mem_iInter.mp hK m) hm⟩
  rw [hset]
  refine MeasurableSet.iUnion fun K => MeasurableSet.iInter fun m => MeasurableSet.iInter fun hm => ?_
  exact measurableSet_le (measurable_selPathDist γ m) measurable_const

/-- The rational time-change condition is Borel in `((a,z),w)` (countable conditions on the measurable limsup values). -/
theorem measurableSet_timeCondRat (γ : ℝ) :
    MeasurableSet {x : (CircleFns × ℂ) × ContinuousPath ℂ | timeCondRat
      (fun t => limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 t) atTop)} := by
  have h0 : MeasurableSet {x : (CircleFns × ℂ) × ContinuousPath ℂ |
      limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 (0 : ℝ≥0)) atTop = 0} :=
    measurableSet_eq_fun (measurable_selLimit γ 0) measurable_const
  have hrat : MeasurableSet {x : (CircleFns × ℂ) × ContinuousPath ℂ |
      ∀ q r : ℚ, 0 ≤ q → q < r →
        limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 (q : ℝ).toNNReal) atTop <
        limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 (r : ℝ).toNNReal) atTop} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun q => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun r => ?_
    exact measurableSet_imp_imp (measurableSet_lt (measurable_selLimit γ (q : ℝ).toNNReal)
      (measurable_selLimit γ (r : ℝ).toNNReal))
  have hunb : MeasurableSet {x : (CircleFns × ℂ) × ContinuousPath ℂ |
      ∀ M : ℕ, ∃ N : ℕ, (M : ℝ) <
        limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 (N : ℝ≥0)) atTop} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun M => ?_
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun N =>
      measurableSet_lt measurable_const (measurable_selLimit γ (N : ℝ≥0))
  exact h0.inter (hrat.inter hunb)

/-- On the good set the clock limit is continuous, and `IsTimeChangeClock` of the limit is the rational condition on
its selected limsup values (`isTimeChangeClock_iff_rat`). -/
theorem isTimeChangeClock_iff_timeCondRat {γ : ℝ} {a : CircleFns} {z : ℂ} {w : ContinuousPath ℂ} {K : ℕ}
    (hw : w ∈ goodSet γ (nselFun γ) a z K) :
    IsTimeChangeClock (clockLimit γ (nselFun γ) a z w) ↔
      timeCondRat (fun t => limsup (fun k => clockApprox γ a (nselFun γ a z k) w t) atTop) := by
  have hconv := clockLimit_tendsto_of_goodSet hw
  have hcont : Continuous (clockLimit γ (nselFun γ) a z w) :=
    hconv.continuous (Eventually.of_forall fun k => continuous_clockApprox γ a (nselFun γ a z k) w).frequently
  have hlim : ∀ t : ℝ≥0, limsup (fun k => clockApprox γ a (nselFun γ a z k) w t) atTop =
      clockLimit γ (nselFun γ) a z w t :=
    fun t => (tendsto_at_of_tendstoLocallyUniformly hconv t).limsup_eq
  rw [isTimeChangeClock_iff_rat hcont]
  simp only [timeCondRat, hlim]

/-- The exceptional set of the Borel relation: starting data and paths in some good set whose clock limit is not a
time-change clock (env-steps.tex:413-421). -/
def selBadSet (γ : ℝ) : Set ((CircleFns × ℂ) × ContinuousPath ℂ) :=
  {x | (∃ K : ℕ, x.2 ∈ goodSet γ (nselFun γ) x.1.1 x.1.2 K) ∧
    ¬ timeCondRat (fun t => limsup (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2 t) atTop)}

theorem measurableSet_selBadSet (γ : ℝ) : MeasurableSet (selBadSet γ) :=
  (measurableSet_goodUnion γ).inter (measurableSet_timeCondRat γ).compl

/-- Measurability of the sections `w ↦ ((p, w)) ∈ S` in the starting data `p = (a,z)` (kernel section lemma). -/
theorem measurable_planarBM_section_pair {S : Set ((CircleFns × ℂ) × ContinuousPath ℂ)} (hS : MeasurableSet S) :
    Measurable fun p : CircleFns × ℂ => planarBrownianMotion p.2 {w | (p, w) ∈ S} := by
  let κ : Kernel (CircleFns × ℂ) (ContinuousPath ℂ) := planarBrownianMotion.comap Prod.snd measurable_snd
  exact Kernel.measurable_kernel_prodMk_left (κ := κ) hS

/-- For a Cauchy starting pair, almost every clock limit is a time-change clock iff the exceptional set has measure zero
(the outer-measure argument: the good sets have full measure, env-steps.tex:438-446). -/
theorem ae_timeClock_iff_measure_selBad {γ : ℝ} (htail : SubsequenceTailProperty γ (nselFun γ))
    {a : CircleFns} {z : ℂ} (hC : CauchyInProbability γ a z) :
    (∀ᵐ w ∂planarBrownianMotion z, clockLimit γ (nselFun γ) a z w ∈ timeClockSet) ↔
      planarBrownianMotion z {w | ((a, z), w) ∈ selBadSet γ} = 0 := by
  have hG : planarBrownianMotion z (⋃ K : ℕ, goodSet γ (nselFun γ) a z K)ᶜ = 0 :=
    measure_iUnion_goodSet_compl htail hC
  have hN : {w : ContinuousPath ℂ | ¬ clockLimit γ (nselFun γ) a z w ∈ timeClockSet} ⊆
      (⋃ K : ℕ, goodSet γ (nselFun γ) a z K)ᶜ ∪ {w : ContinuousPath ℂ | ((a, z), w) ∈ selBadSet γ} := by
    intro w hw
    have hw' : ¬ clockLimit γ (nselFun γ) a z w ∈ timeClockSet := hw
    by_cases hgw : w ∈ ⋃ K : ℕ, goodSet γ (nselFun γ) a z K
    · right
      obtain ⟨K, hK⟩ := mem_iUnion.mp hgw
      refine ⟨⟨K, hK⟩, ?_⟩
      intro hT
      exact hw' ((isTimeChangeClock_iff_timeCondRat hK).mpr hT)
    · exact Or.inl hgw
  have hS : {w : ContinuousPath ℂ | ((a, z), w) ∈ selBadSet γ} ⊆
      {w : ContinuousPath ℂ | ¬ clockLimit γ (nselFun γ) a z w ∈ timeClockSet} := by
    intro w hw
    obtain ⟨⟨K, hK⟩, hnot⟩ := hw
    have hnot' : ¬ timeCondRat (fun t => limsup (fun k => clockApprox γ a (nselFun γ a z k) w t) atTop) := hnot
    show ¬ clockLimit γ (nselFun γ) a z w ∈ timeClockSet
    intro hT
    exact hnot' ((isTimeChangeClock_iff_timeCondRat hK).mp hT)
  rw [ae_iff]
  constructor
  · intro h
    exact measure_mono_null hS h
  · intro h
    exact measure_mono_null hN (measure_union_null hG h)

/-- The selected relation `Q(a,z)` is Borel: for Cauchy starting pairs it is the vanishing of the exceptional set. -/
theorem selected_iff_measure_selBad {γ : ℝ} (htail : SubsequenceTailProperty γ (nselFun γ))
    (p : CircleFns × ℂ) :
    SelectedAllStartsRelation γ (nselFun γ) p.1 p.2 ↔
      CauchyInProbability γ p.1 p.2 ∧ planarBrownianMotion p.2 {w | (p, w) ∈ selBadSet γ} = 0 := by
  obtain ⟨a, z⟩ := p
  constructor
  · rintro ⟨hC, hT⟩
    exact ⟨hC, (ae_timeClock_iff_measure_selBad htail hC).mp hT⟩
  · rintro ⟨hC, hμ⟩
    exact ⟨hC, (ae_timeClock_iff_measure_selBad htail hC).mpr hμ⟩

/-- **The Borel relation Step `BorelAllStartsRelationStep` holds for the constructed subsequence `nselFun`**
(env-steps.tex:413-421: `Q` is a Borel relation). -/
theorem borelAllStartsRelationStep_nselFun (γ : ℝ) : BorelAllStartsRelationStep γ (nselFun γ) := by
  have hmeasure : Measurable fun p : CircleFns × ℂ =>
      planarBrownianMotion p.2 {w | (p, w) ∈ selBadSet γ} :=
    measurable_planarBM_section_pair (measurableSet_selBadSet γ)
  have hset : {p : CircleFns × ℂ | SelectedAllStartsRelation γ (nselFun γ) p.1 p.2} =
      {p : CircleFns × ℂ | CauchyInProbability γ p.1 p.2} ∩
        {p : CircleFns × ℂ | planarBrownianMotion p.2 {w | (p, w) ∈ selBadSet γ} = 0} :=
    Set.ext fun p => selected_iff_measure_selBad (borelSubsequenceSelectionStep_nselFun γ).2 p
  unfold BorelAllStartsRelationStep
  rw [hset]
  exact (measurableSet_cauchyInProbability γ).inter (measurableSet_eq_fun hmeasure measurable_const)

end Measurability

/-- `𝒢` is universally measurable (env-steps.tex:380-446: complement = projection of a Borel subset of `H × ℂ`,
hence analytic; analytic sets are universally measurable, staged as `PrestonAnalyticUniversallyMeasurableStmt`).
Hypotheses: the characterization Step, the Borel Step, Polish `C(E,ℝ)`, and the Preston input. -/
theorem allStartsSet_isUniversallyMeasurable [MeasurableSpace CircleFns] [BorelSpace CircleFns]
    [PolishSpace CircleFns] (hPreston : PrestonAnalyticUniversallyMeasurableStmt) (γ : ℝ)
    (nsel : CircleFns → ℂ → ℕ → ℕ) (hchar : AllStartsCharacterizationStep γ nsel)
    (hBorel : BorelAllStartsRelationStep γ nsel) :
    IsUniversallyMeasurableSet (allStartsSet γ) := by
  have hchar' : allStartsSet γ = selectedAllStartsSet γ nsel := hchar
  have hmeas' : MeasurableSet {p : CircleFns × ℂ | SelectedAllStartsRelation γ nsel p.1 p.2} := hBorel
  have hmeas : MeasurableSet {p : CircleFns × ℂ | ¬ SelectedAllStartsRelation γ nsel p.1 p.2} :=
    hmeas'.compl
  have hcompl : (allStartsSet γ)ᶜ =
      Prod.fst '' {p : CircleFns × ℂ | ¬ SelectedAllStartsRelation γ nsel p.1 p.2} := by
    rw [hchar']
    ext a
    constructor
    · intro h
      have h' : ¬ ∀ z : ℂ, SelectedAllStartsRelation γ nsel a z := h
      obtain ⟨z, hz⟩ := not_forall.mp h'
      exact ⟨(a, z), hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩ hall
      exact hp (hall p.2)
  have hanalytic : AnalyticSet (allStartsSet γ)ᶜ := by
    rw [hcompl]
    exact hmeas.analyticSet.image_of_continuous continuous_fst
  unfold IsUniversallyMeasurableSet
  intro ν hν
  have h := (hPreston CircleFns (allStartsSet γ)ᶜ hanalytic ν hν).compl
  rwa [compl_compl] at h

/-- The almost-sure membership `a₀ ∈ 𝒢` transfers to `aᵦ` under equality in law (proof of `prop:clock`,
env-steps.tex:449-487: the Borel null sandwich of the universally measurable `𝒢`). -/
theorem ae_allStarts_of_map_eq [MeasurableSpace CircleFns] [BorelSpace CircleFns] [PolishSpace CircleFns]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (hPreston : PrestonAnalyticUniversallyMeasurableStmt) (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ)
    (hchar : AllStartsCharacterizationStep γ nsel) (hBorel : BorelAllStartsRelationStep γ nsel)
    {a₀ aᵦ : Ω → CircleFns} (ha₀ : Measurable a₀) (haᵦ : Measurable aᵦ)
    (hlaw : P.map a₀ = P.map aᵦ) (hall : ∀ᵐ ω ∂P, a₀ ω ∈ allStartsSet γ) :
    ∀ᵐ ω ∂P, aᵦ ω ∈ allStartsSet γ :=
  ae_mem_of_map_eq_of_univMeas ha₀ haᵦ hlaw
    (allStartsSet_isUniversallyMeasurable hPreston γ nsel hchar hBorel) hall

/-- Fields that agree on the dyadic radii `dyadicScale k` (in particular on `E`, env-steps.tex:469-471) have the same
`IsLQGClock`: the approximations `lqgClockApprox` read only these values. -/
theorem isLQGClock_congr_dyadic {Q : ProbabilityTheory.Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {g g' : ℝ → ℂ → ℝ}
    (hg : ∀ k : ℕ, ∀ z : ℂ, g (dyadicScale k) z = g' (dyadicScale k) z) {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} :
    IsLQGClock Q γ g x F ↔ IsLQGClock Q γ g' x F := by
  have happ : ∀ (k : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0),
      lqgClockApprox γ g (dyadicScale k) b t = lqgClockApprox γ g' (dyadicScale k) b t := by
    intro k b t
    unfold lqgClockApprox
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hg k]
  unfold IsLQGClock
  simp only [happ, iff_self]

/-! ### Law transfer on `CircleFns` (the measurable-version law step of prop:clock, env-steps.tex:463-465)

The Borel σ-algebra of `CircleFns = C(E, ℝ)` is generated by the evaluations
(`ContinuousMap.measurableSpace_eq_iSup_comap_eval`). Hence a law on `CircleFns` is determined by the laws of the
coordinate vectors `f ↦ (p ↦ f p)` in the product σ-algebra of `E → ℝ`, which is the σ-algebra in which
`QuantumConeScalingInput` states equality in law of `circleProcess`. -/

section LawTransfer

open MeasureTheory

/-- The coordinate map `CircleFns → (PosCircle → ℝ)`, `f ↦ (p ↦ f p)`: the circle process of a continuous circle field. -/
def circleFnsCoord : CircleFns → (PosCircle → ℝ) := fun f p => f p

lemma measurable_circleFnsCoord : Measurable circleFnsCoord :=
  Measurable.of_eval fun p => ContinuousMap.measurable_eval p

/-- The Borel σ-algebra of `CircleFns` is generated by the coordinate map (`ContinuousMap.measurableSpace_eq_iSup_comap_eval`). -/
lemma measurableSpace_circleFns_eq_comap :
    (ContinuousMap.measurableSpace : MeasurableSpace CircleFns) =
      MeasurableSpace.comap circleFnsCoord MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- Laws on `CircleFns` agree when the laws of their coordinate maps agree (product σ-algebra on `PosCircle → ℝ`). -/
theorem map_eq_of_map_coord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → CircleFns}
    (hX : Measurable X) (hY : Measurable Y)
    (h : P.map (fun ω => circleFnsCoord (X ω)) = P.map (fun ω => circleFnsCoord (Y ω))) :
    P.map X = P.map Y := by
  have hXc : Measurable fun ω => circleFnsCoord (X ω) := measurable_circleFnsCoord.comp hX
  have hYc : Measurable fun ω => circleFnsCoord (Y ω) := measurable_circleFnsCoord.comp hY
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap circleFnsCoord MeasurableSpace.pi] A := by
    rw [← measurableSpace_circleFns_eq_comap]
    exact hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA'
  have hB2 : P.map (fun ω => circleFnsCoord (X ω)) B = P.map (fun ω => circleFnsCoord (Y ω)) B := by
    rw [h]
  rw [Measure.map_apply hXc hB, Measure.map_apply hYc hB] at hB2
  rw [Measure.map_apply hX (measurable_circleFnsCoord hB),
    Measure.map_apply hY (measurable_circleFnsCoord hB)]
  exact hB2

/-- Equality in law on `CircleFns` from almost-sure coordinate identities `circleFnsCoord (X ω) = U ω`,
`circleFnsCoord (Y ω) = V ω` and equality in law of `U` and `V` (the form in which `QuantumConeScalingInput` is applied). -/
theorem map_eq_of_ae_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → CircleFns}
    {U V : Ω → PosCircle → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXU : ∀ᵐ ω ∂P, circleFnsCoord (X ω) = U ω) (hYV : ∀ᵐ ω ∂P, circleFnsCoord (Y ω) = V ω)
    (hUV : P.map U = P.map V) : P.map X = P.map Y := by
  apply map_eq_of_map_coord_eq hX hY
  rw [Measure.map_congr hXU, Measure.map_congr hYV, hUV]

end LawTransfer

/-! ### The rescaled all-starts clock step (prop:clock, env-steps.tex:449-475)

Given a valid environment `S` and `b > 0`, the proof of prop:clock is: the measurable version `a_0` of the positive
circle process of `S` lies in `𝒢` almost surely (validity clock and dyadic congruence); the measurable version `a_b` of
the rescaled process `c` has the law of `a_0` (`QuantumConeScalingInput`, with the almost-sure coordinate identities);
the Borel null sandwich of `𝒢` transfers membership to `a_b`; the clock of `a_b` is a clock of `c` (dyadic congruence).
The two measurable versions are the Steps `CanonicalCircleVersionStep` (lem:canonical, env-steps.tex:210-216, invoked
for `a_0` at env-steps.tex:453-456) and `RescaledCircleVersionStep` (the measurable positive-circle version `a_b` of `a^b`,
env-steps.tex:463-465). -/

/-- Canonical measurable version of the positive-circle process (lem:canonical, env-steps.tex:210-216): for a valid
environment, the positive-circle process has a measurable `CircleFns`-valued version. -/
def CanonicalCircleVersionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ a0 : Ω → CircleFns, Measurable a0 ∧
      ∀ᵐ ω ∂S.P, ∀ p : PosCircle, circleFnsCoord (a0 ω) p = circleProcess (S.hcirc ω) p

/-- Measurable positive-circle version of the rescaled process `a^b` (env-steps.tex:463-465, "the measurable
positive-circle version a_b of a^b"): every almost-sure rescaling `c` of the circle process has a measurable version. -/
def RescaledCircleVersionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ b : ℝ, 0 < b → ∀ c : Ω → ℝ → ℂ → ℝ,
      (∀ᵐ ω ∂S.P, c ω = rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b) →
      ∃ ab : Ω → CircleFns, Measurable ab ∧
        ∀ᵐ ω ∂S.P, ∀ p : PosCircle, circleFnsCoord (ab ω) p = circleProcess (c ω) p

/-- The zero-extended positive-radius evaluation is the coordinate of the continuous circle function. -/
lemma posCircleExt_eq_circleFnsCoord {a : CircleFns} {r : ℝ} (hr : 0 < r) (z : ℂ) :
    posCircleExt a r z = circleFnsCoord a (⟨r, hr⟩, z) := by
  simp [posCircleExt, hr, circleFnsCoord]

/-- **The rescaled all-starts clock step**, conditional on the two measurable versions (`CanonicalCircleVersionStep`,
`RescaledCircleVersionStep`), the law-scaling input `QuantumConeScalingInput`, the staged Preston input and the Polish
structure of `CircleFns` (prop:clock, env-steps.tex:449-475). -/
theorem rescaledConeClockStep_of_canonical [PolishSpace CircleFns]
    (hPreston : PrestonAnalyticUniversallyMeasurableStmt) (hscale : QuantumConeScalingInput)
    {𝒮 : SpaceFillingSLEModel} (hcan : CanonicalCircleVersionStep 𝒮)
    (hres : RescaledCircleVersionStep 𝒮) : RescaledConeClockStep 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS b hb c hc
  obtain ⟨a0, ha0m, ha0⟩ := hcan γ hγ0 hγ2 Ω S hS
  obtain ⟨ab, habm, hab⟩ := hres γ hγ0 hγ2 Ω S hS b hb c hc
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- (1) the original positive-circle version lies in `𝒢` almost surely
  have hall0 : ∀ᵐ ω ∂S.P, a0 ω ∈ allStartsSet γ := by
    filter_upwards [hS.isLQGClock, ha0] with ω hω hω0
    refine show AdmitsAllStartClock γ (a0 ω) from ⟨S.clock ω, fun z => ⟨?_, (hω z).2⟩⟩
    refine (isLQGClock_congr_dyadic ?_).mpr (hω z).1
    intro k z'
    rw [posCircleExt_eq_circleFnsCoord (allStarts_dyadicScale_pos k) z']
    exact hω0 _
  -- (2) the same law: QuantumConeScalingInput and the almost-sure coordinate identities
  have hlaw : S.P.map a0 = S.P.map ab := by
    have hUV : S.P.map (fun ω => circleProcess (S.hcirc ω)) =
        S.P.map (fun ω => circleProcess (rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b)) :=
      (hscale γ hγ0 hγ2 Ω S.P S.hC S.hcirc hS.isProbabilityMeasure hS.isQuantumCone b hb).symm
    refine map_eq_of_ae_coord ha0m habm ?_ ?_ hUV
    · filter_upwards [ha0] with ω hω
      funext p
      exact hω p
    · filter_upwards [hab, hc] with ω hω hcω
      funext p
      rw [hω p, hcω]
  -- (3) transfer of membership in `𝒢` (Borel null sandwich of the universally measurable `𝒢`)
  have hallb : ∀ᵐ ω ∂S.P, ab ω ∈ allStartsSet γ :=
    ae_allStarts_of_map_eq hPreston γ (nselFun γ)
      (allStartsCharacterization_of_tail γ (nselFun γ) (borelSubsequenceSelectionStep_nselFun γ).2)
      (borelAllStartsRelationStep_nselFun γ) ha0m habm hlaw hall0
  -- (4) the clock: a choice of an admitting clock for `ab ω`, transported to `c ω` by dyadic congruence
  have hex : ∀ ω, ∃ F : ContinuousPath ℂ → ℝ≥0 → ℝ, ab ω ∈ allStartsSet γ → ∀ z : ℂ,
      IsLQGClock planarBrownianMotion γ (posCircleExt (ab ω)) z F ∧
        ∀ᵐ B ∂planarBrownianMotion z, IsTimeChangeClock (F B) := by
    intro ω
    by_cases h : ab ω ∈ allStartsSet γ
    · obtain ⟨F, hF⟩ := h
      exact ⟨F, fun _ => hF⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose clock' hclock using hex
  refine ⟨clock', ?_⟩
  filter_upwards [hallb, hab] with ω hωb hωab
  intro z
  obtain ⟨hL, hT⟩ := hclock ω hωb z
  refine ⟨(isLQGClock_congr_dyadic ?_).mp hL, hT⟩
  intro k z'
  rw [posCircleExt_eq_circleFnsCoord (allStarts_dyadicScale_pos k) z']
  exact hωab _

end MatedCRT.AllStarts
