import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S4S6c.NextExitStop
import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.FirstPass.S4S6c.ExitNull68

/-!
# Almost sure finiteness of the successive window exits (input `hfin` of `hstep_concrete`)

For a finite set `W`, the path-out
bound `P_v(τ_W > kL) ≤ (1-q)^k`, so the finite-set exit times are almost surely finite) and line 845 (the successive
exit times are almost surely finite stopping times).

* `nextExitSchedule W j`: the successive exit times, `T_0 = 0` and `T_{j+1} = nextExit (W j) T_j`, i.e.
  `T_{j+1} = T_j + vExitTime (W j (X_{T_j})) (pathShift T_j X)` (write-up C1, eq (27)).
* `isWalkRandomTime_nextExitSchedule`: each `T_j` is a walk random time (`{T_j = k}` is `pathHist k`-measurable),
  by `NextExitStop.exists_pathHist_of_determinacy` and `NextExitStop.vExitTime_pathShift_congr`.
* `srwLaw_nextExit_top_null`: after a walk random time `τ`, the walk leaves the window `W (X_τ)` almost surely
  (fixed-time Markov property `srwLaw_markov_state` over the events `{τ = k}`).
* `ae_nextExitSchedule_lt_top`: induction on `j`.
* `ae_nextExitSchedule_lt_top_of_finite`: the null input of the induction is `ExitNull68.exit_null_of_finite`
  (locally finite multigraph, consecutive vertices adjacent, finite windows).
-/

namespace MatedCRT

open MeasureTheory Set Filter
open scoped ENNReal
open WalkPotential

namespace S6j

/-- The `F_k`-measurable sets, in terms of the history `pathHist k`. -/
lemma histSigma_measurableSet_iff (k : ℕ) (s : Set (ℕ → ℤ)) :
    MeasurableSet[histSigma k] s ↔
      ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧ pathHist k ⁻¹' F = s := by
  unfold histSigma
  exact MeasurableSpace.measurableSet_comap

/-- The successive exit schedule with window `W j` used after the `j`-th time: `T_0 = 0`,
`T_{j+1} = nextExit (W j) T_j` (`SuccessiveExitStop.nextExit`; `T_{j+1} = ⊤` once `T_j = ⊤`). -/
noncomputable def nextExitSchedule (W : ℕ → ℤ → Set ℤ) : ℕ → (ℕ → ℤ) → ℕ∞
  | 0 => fun _ => 0
  | j + 1 => SuccessiveExitStop.nextExit (W j) (nextExitSchedule W j)

/-- The next exit time after a finite time `i` is `i` plus the exit time of the shifted path. -/
lemma nextExit_of_eq_coe (W : ℤ → Set ℤ) (t : (ℕ → ℤ) → ℕ∞) {x : ℕ → ℤ} {i : ℕ} (h : t x = (i : ℕ∞)) :
    SuccessiveExitStop.nextExit W t x =
      (i : ℕ∞) + vExitTime (W (x i)) (WalkPotential.pathShift i x) := by
  simp [SuccessiveExitStop.nextExit, h]

/-- Determinacy of the next exit: if the previous time is determined by the path up to `k` (in the sense
`t x = i ↔ t y = i` for `i ≤ k`), then so is `{nextExit = k}`. -/
lemma nextExit_congr (W : ℤ → Set ℤ) (t : (ℕ → ℤ) → ℕ∞) (k : ℕ) {x y : ℕ → ℤ}
    (hxy : pathHist k x = pathHist k y)
    (hT : ∀ i ≤ k, t x = (i : ℕ∞) ↔ t y = (i : ℕ∞)) :
    SuccessiveExitStop.nextExit W t x = (k : ℕ∞) ↔ SuccessiveExitStop.nextExit W t y = (k : ℕ∞) := by
  have key : ∀ x y : ℕ → ℤ, pathHist k x = pathHist k y →
      (∀ i ≤ k, t x = (i : ℕ∞) ↔ t y = (i : ℕ∞)) →
      SuccessiveExitStop.nextExit W t x = (k : ℕ∞) → SuccessiveExitStop.nextExit W t y = (k : ℕ∞) := by
    intro x y hxy hT h
    obtain ⟨i, hi⟩ : ∃ i : ℕ, t x = (i : ℕ∞) := by
      cases hx : t x with
      | top => simp [SuccessiveExitStop.nextExit, hx] at h
      | coe i => exact ⟨i, rfl⟩
    rw [nextExit_of_eq_coe W t hi] at h
    have hvtop : vExitTime (W (x i)) (WalkPotential.pathShift i x) ≠ ⊤ := by
      intro ht
      rw [ht, add_top] at h
      exact ENat.natCast_ne_top k h.symm
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hvtop
    have hik : i + m = k := by
      rw [← hm] at h
      exact_mod_cast h
    have hik' : i ≤ k := by omega
    have hyi : t y = (i : ℕ∞) := (hT i hik').1 hi
    have hxi : x i = y i := by
      have := congrFun hxy ⟨i, by omega⟩
      simpa [pathHist] using this
    have hm' : vExitTime (W (x i)) (WalkPotential.pathShift i y) = (m : ℕ∞) :=
      (NextExitStop.vExitTime_pathShift_congr (W (x i)) (by omega : i + m ≤ k) hxy).1 hm.symm
    rw [hxi] at hm'
    rw [nextExit_of_eq_coe W t hyi, hm', ← Nat.cast_add, hik]
  exact ⟨key x y hxy hT, key y x hxy.symm (fun i hi => (hT i hi).symm)⟩

/-- A walk random time is determined by the path up to any time `i` at which it is evaluated. -/
lemma isWalkRandomTime_det {τ : (ℕ → ℤ) → ℕ∞} (hτ : IsWalkRandomTime τ) (i : ℕ) {x y : ℕ → ℤ}
    (h : pathHist i x = pathHist i y) : τ x = (i : ℕ∞) ↔ τ y = (i : ℕ∞) := by
  obtain ⟨G, -, hEq⟩ := (histSigma_measurableSet_iff i _).1 (hτ i)
  have hx := Set.ext_iff.1 hEq x
  have hy := Set.ext_iff.1 hEq y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx hy
  rw [← hx, ← hy, h]

lemma isWalkRandomTime_zero : IsWalkRandomTime (fun _ : ℕ → ℤ => (0 : ℕ∞)) := by
  intro k
  rw [histSigma_measurableSet_iff]
  by_cases hk : k = 0
  · subst hk
    exact ⟨Set.univ, MeasurableSet.univ, by ext x; simp⟩
  · exact ⟨∅, MeasurableSet.empty, by ext x; simp [hk, eq_comm]⟩

/-- Each successive exit time is a walk random time (`{T_j = k}` depends only on `pathHist k`). -/
theorem isWalkRandomTime_nextExitSchedule (W : ℕ → ℤ → Set ℤ) (j : ℕ) :
    IsWalkRandomTime (nextExitSchedule W j) := by
  induction j with
  | zero => exact isWalkRandomTime_zero
  | succ j ih =>
    intro k
    have hdet : ∀ x y : ℕ → ℤ, pathHist k x = pathHist k y →
        (SuccessiveExitStop.nextExit (W j) (nextExitSchedule W j) x = (k : ℕ∞) ↔
          SuccessiveExitStop.nextExit (W j) (nextExitSchedule W j) y = (k : ℕ∞)) :=
      fun x y hxy => nextExit_congr (W j) (nextExitSchedule W j) k hxy
        (fun i hi => isWalkRandomTime_det ih i (SuccessiveExitStop.pathHist_mono hi hxy))
    obtain ⟨F, hF, hEq⟩ := NextExitStop.exists_pathHist_of_determinacy k _ hdet
    exact (histSigma_measurableSet_iff k _).2 ⟨F, hF, hEq.symm⟩

/-- After a walk random time `τ`, the exit from the window `W (X_τ)` is almost surely finite (fixed-time Markov
property at each `{τ = k}`, `srwLaw_markov_state`, and the null input `hnull`). -/
theorem srwLaw_nextExit_top_null (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ)
    (hnull : ∀ y : ℤ, srwLaw m y {x | vExitTime (W y) x = ⊤} = 0) {τ : (ℕ → ℤ) → ℕ∞}
    (hτ : IsWalkRandomTime τ) :
    srwLaw m a {x | τ x < ⊤ ∧ SuccessiveExitStop.nextExit W τ x = ⊤} = 0 := by
  have hGm : ∀ y : ℤ, MeasurableSet {x : ℕ → ℤ | vExitTime (W y) x = ⊤} := by
    intro y
    have : {x : ℕ → ℤ | vExitTime (W y) x = ⊤} = ⋂ n : ℕ, (fun x : ℕ → ℤ => x n) ⁻¹' W y := by
      ext x
      simp [vExitTime_eq_top_iff]
    rw [this]
    exact MeasurableSet.iInter fun n =>
      (Set.to_countable (W y)).measurableSet.preimage (measurable_pi_apply n)
  have hsub : {x : ℕ → ℤ | τ x < ⊤ ∧ SuccessiveExitStop.nextExit W τ x = ⊤} ⊆
      ⋃ k : ℕ, {x | τ x = (k : ℕ∞) ∧
        WalkPotential.pathShift k x ∈ {z : ℕ → ℤ | vExitTime (W (x k)) z = ⊤}} := by
    rintro x ⟨hlt, htop⟩
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne
    have hv : vExitTime (W (x k)) (WalkPotential.pathShift k x) = ⊤ := by
      rw [nextExit_of_eq_coe W τ hk.symm] at htop
      rcases eq_or_ne (vExitTime (W (x k)) (WalkPotential.pathShift k x)) ⊤ with h | h
      · exact h
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
        rw [← hm, ← Nat.cast_add] at htop
        exact absurd htop (ENat.natCast_ne_top _)
    exact Set.mem_iUnion.2 ⟨k, ⟨hk.symm, hv⟩⟩
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  obtain ⟨F, hF, hEq⟩ := (histSigma_measurableSet_iff k _).1 (hτ k)
  have hmk := srwLaw_markov_state m a k (fun y => {z : ℕ → ℤ | vExitTime (W y) z = ⊤}) hGm hF
  have hzero : ∫⁻ x in {x : ℕ → ℤ | pathHist k x ∈ F},
      srwLaw m (x k) {z : ℕ → ℤ | vExitTime (W (x k)) z = ⊤} ∂srwLaw m a = 0 := by
    simp only [hnull, lintegral_zero]
  refine measure_mono_null ?_ (hmk.trans hzero)
  rintro x ⟨hx, hs⟩
  have hx' : x ∈ pathHist k ⁻¹' F := by
    rw [hEq]
    exact hx
  exact ⟨hx', hs⟩

/-- The successive exit times are almost surely finite: induction on `j`, the step being
`srwLaw_nextExit_top_null` applied to `T_j`. -/
theorem srwLaw_nextExitSchedule_top_null (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℕ → ℤ → Set ℤ)
    (hnull : ∀ (j : ℕ) (y : ℤ), srwLaw m y {x | vExitTime (W j y) x = ⊤} = 0) (j : ℕ) :
    srwLaw m a {x | nextExitSchedule W j x = ⊤} = 0 := by
  induction j with
  | zero =>
    have : {x : ℕ → ℤ | nextExitSchedule W 0 x = ⊤} = ∅ := by
      ext x
      simp [nextExitSchedule]
    rw [this, measure_empty]
  | succ j ih =>
    have hsub : {x : ℕ → ℤ | nextExitSchedule W (j + 1) x = ⊤} ⊆
        {x | nextExitSchedule W j x = ⊤} ∪
          {x | nextExitSchedule W j x < ⊤ ∧
            SuccessiveExitStop.nextExit (W j) (nextExitSchedule W j) x = ⊤} := by
      intro x hx
      by_cases h : nextExitSchedule W j x = ⊤
      · exact Or.inl h
      · exact Or.inr ⟨lt_top_iff_ne_top.2 h, hx⟩
    exact measure_mono_null hsub
      (measure_union_null ih
        (srwLaw_nextExit_top_null m a (W j) (hnull j) (isWalkRandomTime_nextExitSchedule W j)))

/-- Almost sure finiteness of every successive exit time, from the null input for each finite-window exit. -/
theorem ae_nextExitSchedule_lt_top (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℕ → ℤ → Set ℤ)
    (hnull : ∀ (j : ℕ) (y : ℤ), srwLaw m y {x | vExitTime (W j y) x = ⊤} = 0) (j : ℕ) :
    ∀ᵐ x ∂srwLaw m a, nextExitSchedule W j x < ⊤ := by
  rw [ae_iff]
  refine measure_mono_null ?_ (srwLaw_nextExitSchedule_top_null m a W hnull j)
  intro x hx
  simpa [lt_top_iff_ne_top] using hx

/-- The environment form: for a locally finite multigraph `m` whose consecutive vertices are adjacent, and finite
windows, every successive exit time is almost surely finite (`ExitNull68.exit_null_of_finite`). -/
theorem ae_nextExitSchedule_lt_top_of_finite (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℕ → ℤ → Set ℤ)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hW : ∀ (j : ℕ) (y : ℤ), (W j y).Finite)
    (j : ℕ) : ∀ᵐ x ∂srwLaw m a, nextExitSchedule W j x < ⊤ :=
  ae_nextExitSchedule_lt_top m a W
    (fun j y => ExitNull68.exit_null_of_finite hlf hcons (hW j y) y) j

/-- `hstep_concrete` with the successive exit schedule as the random times `τ j = T_j`: the finiteness input `hfin` is
discharged by `ae_nextExitSchedule_lt_top_of_finite`. The remaining inputs are `hq0`, `hq1` (`qStar ≤ 1`, the printed
constant of C15), `hR` (the test radius), and `hpt` (the per-state printed test bound at `X_{T_j}`, `printed_test_bound`). -/
theorem hstep_of_schedule (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℕ → ℤ → Set ℤ) (A : Set ℤ) (H : ℕ → Set (ℕ → ℤ))
    (R : ℕ → (ℕ → ℤ) → ℝ) {qStar : ℝ} (hq0 : 0 ≤ qStar) (hq1 : qStar ≤ 1)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hW : ∀ (j : ℕ) (y : ℤ), (W j y).Finite)
    (hR : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → 0 < R j x ∧ R j x ≤ 1)
    (hpt : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → nextExitSchedule W j x < ⊤ →
      srwLaw m (x (nextExitSchedule W j x).toNat)
          (TestBound68.stayIn (W j) A (x (nextExitSchedule W j x).toNat)) ≤
        ENNReal.ofReal (1 - qStar / (1 + Real.log (1 / R j x)) ^ 2)) (j : ℕ) :
    ∀ᵐ x ∂srwLaw m a, x ∈ H j → qStar / (1 + Real.log (1 / R j x)) ^ 2 ≤
      condExp (stoppedSigma (nextExitSchedule W j) (isWalkRandomTime_nextExitSchedule W j)) (srwLaw m a)
        ((walkTestEvent (nextExitSchedule W j) (fun y => testEvent (W j) A y)).indicator
          (fun _ => (1 : ℝ))) x := by
  have hfin : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → nextExitSchedule W j x < ⊤ := fun j =>
    (ae_nextExitSchedule_lt_top_of_finite m a W hlf hcons hW j).mono fun _ hx _ => hx
  exact hstep_concrete m a (nextExitSchedule W) (fun j => isWalkRandomTime_nextExitSchedule W j) W A H R
    hq0 hq1 hR hfin hpt j

end S6j

end MatedCRT
