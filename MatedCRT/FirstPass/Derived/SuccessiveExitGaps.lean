import MatedCRT.FirstPass.S6j.FiniteExit
import MatedCRT.FirstPass.S4S6c.RandomTimeTestBound
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ExitTime

/-!
# Gaps between successive exits of the walk from position-dependent regions (BG20 (6.49))

Let `A y ⊆ ℤ` be a region attached to each vertex `y` (in Berestycki–Gwynne (6.49) the vertices of the
mated-CRT map in the Euclidean ball of radius `δ` around `η y`).  The successive exit times `σ_k` of the
walk are `σ_0 = 0`, `σ_{k+1} = σ_k + τ_{A (X_{σ_k})} ∘ θ_{σ_k}` (`S6j.nextExitSchedule`).  If the `N`-th
moment of the exit time from `A y` is at most `M` for every `y` in a set `Y`, then, by the strong Markov
property at `σ_k` and the Chebyshev inequality, the probability that the `k`-th gap
`σ_{k+1} - σ_k` is at least `b + 1` while `σ_k` is before the exit time of `Y` is at most `M / (b+1) ^ N`;
a union bound over `k < K` gives `K M / (b+1) ^ N`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential

namespace SuccessiveExitGaps

/-- The successive exit times from the position-dependent regions `A y`:
`σ_0 = 0` and `σ_{k+1} = σ_k + (exit time of the shifted path from `A (X_{σ_k})`)`. -/
noncomputable abbrev succExit (A : ℤ → Set ℤ) : ℕ → (ℕ → ℤ) → ℕ∞ :=
  S6j.nextExitSchedule (fun _ => A)

/-- The event that the `k`-th gap of the successive exits is at least `b + 1` while `σ_k` is before the
exit time from `Y`. -/
def gapEvent (A : ℤ → Set ℤ) (Y : Set ℤ) (b k : ℕ) : Set (ℕ → ℤ) :=
  {x | succExit A k x < vExitTime Y x ∧ succExit A k x + ((b + 1 : ℕ) : ℕ∞) ≤ succExit A (k + 1) x}

/-- A walk random time is determined by the history: `τ x = j ↔ τ y = j` when `x` and `y` agree up to
time `j`. -/
lemma isWalkRandomTime_congr {τ : (ℕ → ℤ) → ℕ∞} (hτ : S6j.IsWalkRandomTime τ) {j : ℕ} {x y : ℕ → ℤ}
    (h : pathHist j x = pathHist j y) : τ x = (j : ℕ∞) ↔ τ y = (j : ℕ∞) := by
  have h1 : MeasurableSet[S6j.histSigma j] {x | τ x = (j : ℕ∞)} := hτ j
  unfold S6j.histSigma at h1
  obtain ⟨t, _, ht⟩ := MeasurableSpace.measurableSet_comap.1 h1
  have e : ∀ z : ℕ → ℤ, τ z = (j : ℕ∞) ↔ pathHist j z ∈ t := fun z => by
    have := congrArg (fun s : Set (ℕ → ℤ) => z ∈ s) ht
    simpa using this.symm
  rw [e x, e y, h]

/-- The set `{σ_k < τ_Y}` intersected with `{σ_k = j}` is determined by the history up to time `j`. -/
lemma exists_pathHist_gapStart (A : ℤ → Set ℤ) (Y : Set ℤ) (k j : ℕ) :
    ∃ F : Set (Fin (j + 1) → ℤ), MeasurableSet F ∧
      {x | succExit A k x < vExitTime Y x} ∩ {x | succExit A k x = (j : ℕ∞)} =
        {x | pathHist j x ∈ F} := by
  have hτ : S6j.IsWalkRandomTime (succExit A k) :=
    S6j.isWalkRandomTime_nextExitSchedule (fun _ => A) k
  obtain ⟨F, hF, hFe⟩ := NextExitStop.exists_pathHist_of_determinacy j
    (fun x => (succExit A k x < vExitTime Y x ∧ succExit A k x = (j : ℕ∞)))
    (by
      intro x y hxy
      have hyz : ∀ i ≤ j, x i = y i := fun i hi => SuccessiveExitStop.pathHist_apply_of_le hxy i hi
      have hlt : (j : ℕ∞) < vExitTime Y x ↔ (j : ℕ∞) < vExitTime Y y := by
        rw [natCast_lt_vExitTime_iff, natCast_lt_vExitTime_iff]
        exact ⟨fun h i hi => (hyz i hi) ▸ h i hi, fun h i hi => (hyz i hi).symm ▸ h i hi⟩
      have hσ := isWalkRandomTime_congr hτ hxy
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, hσ.1 h2⟩
        rw [hσ.1 h2]
        rw [h2] at h1
        exact hlt.1 h1
      · rintro ⟨h1, h2⟩
        have hx2 := hσ.2 h2
        refine ⟨?_, hx2⟩
        rw [hx2]
        rw [h2] at h1
        exact hlt.2 h1)
  exact ⟨F, hF, hFe⟩

/-- **Chebyshev for the exit time**: if `E_y τ_B ^ N ≤ M`, then `P_y [τ_B ≥ b + 1] ≤ M / (b + 1) ^ N`. -/
lemma srwLaw_exit_ge_le (m : ℤ → ℤ → ℕ) (B : Set ℤ) (y : ℤ) (N b : ℕ) {M : ℝ≥0∞}
    (hM : exitTimeMoment m B y N ≤ M) :
    srwLaw m y {z | ((b + 1 : ℕ) : ℕ∞) ≤ vExitTime B z} ≤ M / ((b + 1 : ℝ≥0∞) ^ N) := by
  have hb : (b + 1 : ℝ≥0∞) ≠ 0 := by simp
  have hb' : (b + 1 : ℝ≥0∞) ≠ ⊤ := by simp
  have hε0 : ((b + 1 : ℝ≥0∞) ^ N) ≠ 0 := pow_ne_zero N hb
  have hε : ((b + 1 : ℝ≥0∞) ^ N) ≠ ⊤ := ENNReal.pow_ne_top hb'
  have hsub : {z | ((b + 1 : ℕ) : ℕ∞) ≤ vExitTime B z} ⊆
      {z | (b + 1 : ℝ≥0∞) ^ N ≤ (vExitTime B z : ℝ≥0∞) ^ N} := by
    intro z hz
    have h1 : (((b + 1 : ℕ) : ℕ∞) : ℝ≥0∞) ≤ (vExitTime B z : ℝ≥0∞) := ENat.toENNReal_le.2 hz
    have h2 : (b + 1 : ℝ≥0∞) ≤ (vExitTime B z : ℝ≥0∞) := by simpa using h1
    exact pow_le_pow_left' h2 N
  refine (measure_mono hsub).trans ?_
  have hcheb := meas_ge_le_lintegral_div (μ := srwLaw m y)
    ((Tightness.measurable_vExitTime_coe B).pow_const N).aemeasurable hε0 hε
  refine hcheb.trans ?_
  exact ENNReal.div_le_div_right hM _

/-- **One gap**: the probability that the `k`-th gap of the successive exits is at least `b + 1` while
`σ_k` is before the exit time from `Y` is at most `M / (b + 1) ^ N`, if the `N`-th moment of the exit time
from `A y` is at most `M` for `y ∈ Y`. -/
theorem srwLaw_gapEvent_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (N b k : ℕ)
    {M : ℝ≥0∞} (hM : ∀ y ∈ Y, exitTimeMoment m (A y) y N ≤ M) :
    srwLaw m a (gapEvent A Y b k) ≤ M / ((b + 1 : ℝ≥0∞) ^ N) := by
  set G : ℤ → Set (ℕ → ℤ) := fun y => {z | ((b + 1 : ℕ) : ℕ∞) ≤ vExitTime (A y) z} with hG
  have hGm : ∀ y, MeasurableSet (G y) := fun y =>
    (measurable_vExitTime (A y)) (Set.to_countable {t : ℕ∞ | ((b + 1 : ℕ) : ℕ∞) ≤ t}).measurableSet
  have h := srwLaw_test_bound_random_time m a (succExit A k) G hGm
    (S := {x | succExit A k x < vExitTime Y x}) (fun j => exists_pathHist_gapStart A Y k j)
    (Y := Y) (c := M / ((b + 1 : ℝ≥0∞) ^ N))
    (fun y hy => srwLaw_exit_ge_le m (A y) y N b (hM y hy))
    (by
      intro x hx j hj
      have hx' : succExit A k x < vExitTime Y x := hx
      rw [hj] at hx'
      exact natCast_lt_vExitTime_iff.1 hx' j le_rfl)
  refine le_trans (measure_mono ?_) (h.trans ?_)
  · rintro x ⟨hlt, hle⟩
    refine ⟨hlt, ?_⟩
    have hne : succExit A k x ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hlt le_top)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
    refine ⟨j, hj.symm, ?_⟩
    have hnext : succExit A (k + 1) x = (j : ℕ∞) + vExitTime (A (x j)) (WalkPotential.pathShift j x) :=
      S6j.nextExit_of_eq_coe A (succExit A k) hj.symm
    rw [hnext, ← hj] at hle
    show ((b + 1 : ℕ) : ℕ∞) ≤ vExitTime (A (x j)) (WalkPotential.pathShift j x)
    generalize vExitTime (A (x j)) (WalkPotential.pathShift j x) = t at hle ⊢
    induction t using ENat.recTopCoe with
    | top => exact le_top
    | coe t =>
      have h1 : j + (b + 1) ≤ j + t := by exact_mod_cast hle
      exact_mod_cast Nat.le_of_add_le_add_left h1
  · calc M / ((b + 1 : ℝ≥0∞) ^ N) * srwLaw m a ({x | succExit A k x < vExitTime Y x} ∩
          {x | ∃ j : ℕ, succExit A k x = (j : ℕ∞)})
        ≤ M / ((b + 1 : ℝ≥0∞) ^ N) * 1 := mul_le_mul_of_nonneg_left prob_le_one (by simp)
      _ = _ := mul_one _

/-- **Union bound over the first `K` gaps** (BG20 (6.49)): the probability that some gap `σ_{k+1} - σ_k`,
`k < K`, is at least `b + 1` while `σ_k` is before the exit time from `Y`, is at most
`K M / (b + 1) ^ N`. -/
theorem srwLaw_exists_gapEvent_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (N b K : ℕ)
    {M : ℝ≥0∞} (hM : ∀ y ∈ Y, exitTimeMoment m (A y) y N ≤ M) :
    srwLaw m a {x | ∃ k < K, x ∈ gapEvent A Y b k} ≤ (K : ℝ≥0∞) * (M / ((b + 1 : ℝ≥0∞) ^ N)) := by
  have hU : {x | ∃ k < K, x ∈ gapEvent A Y b k} = ⋃ k ∈ Finset.range K, gapEvent A Y b k := by
    ext x
    simp
  calc srwLaw m a {x | ∃ k < K, x ∈ gapEvent A Y b k}
      ≤ ∑ k ∈ Finset.range K, srwLaw m a (gapEvent A Y b k) := by
        rw [hU]
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, M / ((b + 1 : ℝ≥0∞) ^ N) :=
        Finset.sum_le_sum fun k _ => srwLaw_gapEvent_le m a A Y N b k hM
    _ = _ := by simp

#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_exit_ge_le
#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_gapEvent_le
#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_exists_gapEvent_le

end SuccessiveExitGaps

end MatedCRT
