import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Proposed.PrestonAnalytic2008
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Clock

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

Named Steps, NOT proved here (outstanding; Prop hypotheses, never axioms):
* `BorelSubsequenceSelectionStep`, clause 1 only: Borel measurability of `(a,z) ↦ n_k(a,z)` (lem:allstarts proof,
  env-steps.tex:380-446). Clauses 2-3 are `SubsequenceTailProperty`, which is proved to suffice.
* `BorelAllStartsRelationStep`: Borel measurability of `Q` on `C(E,ℝ) × ℂ` (needs joint measurability of `J`).
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

end MatedCRT.AllStarts
