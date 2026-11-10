import Mathlib
import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.Proofs.IDLA.Measurable

/-!
# FIRST PASS: the successive-exit route to the configuration bound of Lemma 6.8 (fp-S6h, z8)

Bridge note `notes/fp-gaps/CHATGPT-z9-6-8-bridge.md` §3 (Steps B–F) and the test schedule of the write-up C3
(`notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, lines 695–741): the successive exit times
`τ_{N+1} = nextExit W τ_N` are the test times `T_j` of (C3) when the window `W (X_{T_j})` is the cell interval of the
test disk. The passing events `S_N` of `SuccessiveExitStop` are the complements of the failure events `H_N`.

This route uses `SuccessiveExitStop.srwLaw_successive_exit_le_pow` (q2, proved): the strong Markov property at the
successive exit times is inside that theorem, so no conditional expectation, stopping σ-algebra or padding is needed.
Its inputs are: the per-state test bound `hc` (printed_test_bound in `FirstPass/S4S6c/PerTest68.lean`, the write-up
B18/C15 bound with the uniform constant), the start-state invariant `hSY` (the C6 invariant of the write-up), and the
almost-sure containment `hC12` (C12: `T_N < τ_U` almost surely), which are named inputs of this file. -/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Successive

/-- The successive exit times of the test chain: `τ_0 = 0` and `τ_{N+1} = nextExit W τ_N`, the next exit time after
`τ_N` from the window `W (X_{τ_N})` (write-up C3, (C3)). -/
noncomputable def exitSchedule (W : ℤ → Set ℤ) : ℕ → (ℕ → ℤ) → ℕ∞
  | 0 => fun _ => 0
  | N + 1 => SuccessiveExitStop.nextExit W (exitSchedule W N)

/-- `S_N`: the first `N` successive exit tests are all passed (`SuccessiveExitStop.srwLaw_successive_exit_le_pow`). -/
def passSet (W : ℤ → Set ℤ) (A : Set ℤ) : ℕ → Set (ℕ → ℤ)
  | 0 => univ
  | N + 1 => passSet W A N ∩ {x | ∃ k : ℕ, exitSchedule W N x = k ∧
      WalkPotential.pathShift k x ∈ SuccessiveExitStop.stayInRegion W A (x k)}

theorem exitSchedule_succ_of_eq {W : ℤ → Set ℤ} {N : ℕ} {x : ℕ → ℤ} {i : ℕ} (h : exitSchedule W N x = i) :
    exitSchedule W (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (WalkPotential.pathShift i x) := by
  simp [exitSchedule, SuccessiveExitStop.nextExit, h]

theorem exitSchedule_succ_top {W : ℤ → Set ℤ} {N : ℕ} {x : ℕ → ℤ} (h : exitSchedule W N x = ⊤) :
    exitSchedule W (N + 1) x = ⊤ := by
  simp [exitSchedule, SuccessiveExitStop.nextExit, h]

/-- The successive exit times are nondecreasing in the test index. -/
theorem exitSchedule_le_succ (W : ℤ → Set ℤ) (N : ℕ) (x : ℕ → ℤ) :
    exitSchedule W N x ≤ exitSchedule W (N + 1) x := by
  by_cases h : exitSchedule W N x = ⊤
  · rw [exitSchedule_succ_top h]; exact le_top
  · obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 h
    rw [exitSchedule_succ_of_eq hi.symm, ← hi]
    exact le_self_add

/-- On the event `T_N < τ_U` every exit-event path passes the first `N` tests. -/
theorem exitEvent_subset_passSet (W : ℤ → Set ℤ) (A U : Set ℤ) (N : ℕ) (x : ℕ → ℤ)
    (hx : exitSchedule W N x < vExitTime U x) (hB : x ∈ Lemma68Walk.exitEvent U A) :
    x ∈ passSet W A N := by
  induction N with
  | zero => simp [passSet]
  | succ N ih =>
    have hmono := exitSchedule_le_succ W N x
    have hNlt : exitSchedule W N x < vExitTime U x := lt_of_le_of_lt hmono hx
    have hfin : exitSchedule W (N + 1) x ≠ ⊤ := ne_top_of_lt hx
    have hNfin : exitSchedule W N x ≠ ⊤ := ne_top_of_le_ne_top hfin hmono
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hNfin
    refine ⟨ih hNlt, k, hk.symm, ?_⟩
    intro n hn
    have h1 : exitSchedule W (N + 1) x = (k : ℕ∞) + vExitTime (W (x k)) (WalkPotential.pathShift k x) :=
      exitSchedule_succ_of_eq hk.symm
    have h2 : ((k + n : ℕ) : ℕ∞) < vExitTime U x := by
      rw [Nat.cast_add]
      calc (k : ℕ∞) + n < (k : ℕ∞) + vExitTime (W (x k)) (WalkPotential.pathShift k x) :=
            (ENat.add_lt_add_iff_left (ENat.natCast_ne_top k)).2 hn
        _ = exitSchedule W (N + 1) x := h1.symm
        _ < vExitTime U x := hx
    have hB' : ∀ n : ℕ, (∀ j ≤ n, x j ∈ U) → x n ∈ A := hB
    show x (k + n) ∈ A
    exact hB' (k + n) (natCast_lt_vExitTime_iff.1 h2)

/-- (Step D, successive form) Almost surely `T_N < τ_U` implies that the exit event lies in `S_N`. -/
theorem exitEvent_ae_le_passSet {ν : Measure (ℕ → ℤ)} (W : ℤ → Set ℤ) (A U : Set ℤ) (N : ℕ)
    (hC12 : ∀ᵐ x ∂ν, exitSchedule W N x < vExitTime U x) :
    Lemma68Walk.exitEvent U A ≤ᵐ[ν] passSet W A N := by
  filter_upwards [hC12] with x hx
  exact fun hB => exitEvent_subset_passSet W A U N x hx hB

/-- **The configuration bound in ENNReal form** (write-up C12 with the successive-exit product bound): the quenched exit
probability of `U` for the walk from `a` is at most `c^N` when every state of the start set `Y` passes one test with
probability at most `c`, the start states of passed tests lie in `Y`, and C12 holds. -/
theorem srwLaw_exitEvent_le_pow (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ) (A U : Set ℤ) (N : ℕ)
    (hC12 : ∀ᵐ x ∂srwLaw m a, exitSchedule W N x < vExitTime U x)
    {Y : Set ℤ} {c : ℝ≥0∞} (hc : ∀ y ∈ Y, srwLaw m y (SuccessiveExitStop.stayInRegion W A y) ≤ c)
    (hSY : ∀ N, ∀ x ∈ passSet W A N, ∀ k : ℕ, exitSchedule W N x = k → x k ∈ Y) :
    srwLaw m a (Lemma68Walk.exitEvent U A) ≤ c ^ N := by
  have h1 := SuccessiveExitStop.srwLaw_successive_exit_le_pow m a W A (exitSchedule W) (passSet W A)
    (fun _ => rfl) (fun N x i h => exitSchedule_succ_of_eq h) (fun N x h => exitSchedule_succ_top h)
    rfl (fun N => rfl) hc hSY N
  exact (measure_mono_ae (exitEvent_ae_le_passSet W A U N hC12)).trans h1

/-- **The configuration bound in real form** (bridge note §3, display (10)): with the uniform per-test constant
`x0 = 1 - q0/(1+log(1/r))²`, the real quenched exit probability is at most `x0^N`. -/
theorem exitEvent_real_le_pow (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ) (A U : Set ℤ) (N : ℕ) {x0 : ℝ}
    (hx0 : 0 ≤ x0) (hC12 : ∀ᵐ x ∂srwLaw m a, exitSchedule W N x < vExitTime U x)
    {Y : Set ℤ} (hc : ∀ y ∈ Y, srwLaw m y (SuccessiveExitStop.stayInRegion W A y) ≤ ENNReal.ofReal x0)
    (hSY : ∀ N, ∀ x ∈ passSet W A N, ∀ k : ℕ, exitSchedule W N x = k → x k ∈ Y) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) ≤ x0 ^ N := by
  have h := srwLaw_exitEvent_le_pow m a W A U N hC12 hc hSY
  rw [← ENNReal.ofReal_pow hx0] at h
  rw [measureReal_def]
  calc ((srwLaw m a) (Lemma68Walk.exitEvent U A)).toReal
      ≤ (ENNReal.ofReal (x0 ^ N)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = x0 ^ N := ENNReal.toReal_ofReal (pow_nonneg hx0 N)

end Lemma68Successive

end MatedCRT
