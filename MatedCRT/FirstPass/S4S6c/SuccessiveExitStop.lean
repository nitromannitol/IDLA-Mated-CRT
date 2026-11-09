import MatedCRT.FirstPass.S4S6c.NextExitStop
import MatedCRT.FirstPass.S4S6c.SuccessiveTests

/-!
# Stopping property of successive exit-time tests (q2, task fp-S4S6c; LEMMA68 N3c, hstop)

`srwLaw_successive_tests_le_pow` needs, for every `N` and `k`, the shape `S N ∩ {τ N = k} = {pathHist k ∈ F}`.
Here the `N`-th test starts at the random time `τ N`, the tests are successive exit times
`τ (N+1) = τ N + vExitTime (W (x (τ N))) (pathShift (τ N) x)`, and the `N`-th test is passed when the walk stays in `A`
until it leaves the region `W (x (τ N))` (`stayInRegion`). `S (N+1) = S N ∩ {test N passed}`.
The induction `successive_stop_inv` shows that both `{τ N = j}` and `S N ∩ {τ N = j}` are determined by `pathHist j`;
`successive_stop_fin` is the `hstop` hypothesis, and `srwLaw_successive_exit_le_pow` combines it with the one-test bound.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

namespace SuccessiveExitStop

/-- One test of the successive exit-time tests: the walk stays in `A` at all times strictly before its exit from
`W y` (the walk is killed on leaving the region, Berestycki-Gwynne convention). -/
def stayInRegion (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) : Set (ℕ → ℤ) :=
  {w | ∀ n : ℕ, (n : ℕ∞) < vExitTime (W y) w → w n ∈ A}

/-- The next exit time after the (possibly infinite) time `t x`; it is `⊤` when `t x = ⊤`. -/
noncomputable def nextExit (W : ℤ → Set ℤ) (t : (ℕ → ℤ) → ℕ∞) (x : ℕ → ℤ) : ℕ∞ :=
  ENat.recTopCoe ⊤ (fun j : ℕ => (j : ℕ∞) + vExitTime (W (x j)) (pathShift j x)) (t x)

/-- The centre-dependent form of `stayInRegion`: the walk stays in `Aof y` at all times strictly before its exit from
`W y`. The gate of `TailBound68` uses it with `Aof y = ∅` for the centres that are not available. Constant regions are
`stayInRegionOf W (fun _ => A) = stayInRegion W A` by `rfl`. -/
def stayInRegionOf (W : ℤ → Set ℤ) (Aof : ℤ → Set ℤ) (y : ℤ) : Set (ℕ → ℤ) :=
  {w | ∀ n : ℕ, (n : ℕ∞) < vExitTime (W y) w → w n ∈ Aof y}

theorem measurableSet_stayInRegionOf (W : ℤ → Set ℤ) (Aof : ℤ → Set ℤ) (y : ℤ) :
    MeasurableSet (stayInRegionOf W Aof y) := by
  have h : stayInRegionOf W Aof y =
      ⋂ n : ℕ, ({w : ℕ → ℤ | (n : ℕ∞) < vExitTime (W y) w}ᶜ ∪ (fun w : ℕ → ℤ => w n) ⁻¹' Aof y) := by
    ext w
    simp only [stayInRegionOf, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_preimage, imp_iff_not_or]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    ((ConstantOrderDiv.measurableSet_lt_vExitTime (W y) n).compl).union
      ((measurable_pi_apply n) (Set.to_countable (Aof y)).measurableSet)

theorem measurableSet_stayInRegion (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) :
    MeasurableSet (stayInRegion W A y) := by
  have h : stayInRegion W A y =
      ⋂ n : ℕ, ({w : ℕ → ℤ | (n : ℕ∞) < vExitTime (W y) w}ᶜ ∪ (fun w : ℕ → ℤ => w n) ⁻¹' A) := by
    ext w
    simp only [stayInRegion, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_preimage, imp_iff_not_or]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    ((ConstantOrderDiv.measurableSet_lt_vExitTime (W y) n).compl).union
      ((measurable_pi_apply n) (Set.to_countable A).measurableSet)

theorem pathHist_apply_of_le {j : ℕ} {x y : ℕ → ℤ} (h : pathHist j x = pathHist j y) (t : ℕ) (ht : t ≤ j) :
    x t = y t :=
  congrFun h ⟨t, by omega⟩

theorem pathHist_mono {i j : ℕ} (hij : i ≤ j) {x y : ℕ → ℤ} (h : pathHist j x = pathHist j y) :
    pathHist i x = pathHist i y := by
  funext t
  show x t.1 = y t.1
  exact pathHist_apply_of_le h t.1 (by have := t.2; omega)

/-- The invariant of the induction: for every `N`, the event `{τ N = j}` and the event `S N ∩ {τ N = j}` depend only on
the path up to time `j`. -/
theorem successive_stop_inv (W : ℤ → Set ℤ) (Aof : ℤ → Set ℤ) (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ N x (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf W Aof (x k)})
    (N : ℕ) :
    (∀ j : ℕ, ∀ x y : ℕ → ℤ, pathHist j x = pathHist j y → (τ N x = j ↔ τ N y = j)) ∧
    (∀ j : ℕ, ∀ x y : ℕ → ℤ, pathHist j x = pathHist j y →
      ((x ∈ S N ∧ τ N x = j) ↔ (y ∈ S N ∧ τ N y = j))) := by
  induction N with
  | zero =>
    exact ⟨fun j x y _ => by simp [hτ0], fun j x y _ => by simp [hS0, hτ0]⟩
  | succ N ih =>
    obtain ⟨hT, hSd⟩ := ih
    -- a finite value of `τ (N+1)` is the end of a test that starts at some finite `i`
    have decomp : ∀ (j : ℕ) (x : ℕ → ℤ), τ (N + 1) x = (j : ℕ∞) →
        ∃ i m : ℕ, i + m = j ∧ τ N x = (i : ℕ∞) ∧ vExitTime (W (x i)) (pathShift i x) = (m : ℕ∞) := by
      intro j x hx
      have hne : τ N x ≠ ⊤ := fun htop => by
        rw [hτtop N x htop] at hx
        exact ENat.natCast_ne_top j hx.symm
      obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 hne
      have h1 := hτsucc N x i hi.symm
      have hV : vExitTime (W (x i)) (pathShift i x) ≠ ⊤ := by
        intro htop
        rw [h1, htop, add_top] at hx
        exact ENat.natCast_ne_top j hx.symm
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hV
      rw [h1, ← hm] at hx
      have hsum : i + m = j := by exact_mod_cast hx
      exact ⟨i, m, hsum, hi.symm, hm.symm⟩
    -- conversely, a test from `i` with exit time `m` ends at `i + m`
    have recomp : ∀ (i m : ℕ) (x : ℕ → ℤ), τ N x = (i : ℕ∞) →
        vExitTime (W (x i)) (pathShift i x) = (m : ℕ∞) → τ (N + 1) x = ((i + m : ℕ) : ℕ∞) := by
      intro i m x hi hm
      rw [hτsucc N x i hi, hm, Nat.cast_add]
    -- the exit time of the region from `i` is the same for `x` and `y` when the paths agree up to `j ≥ i + m`
    have vexit_transfer : ∀ (j i m : ℕ) (x y : ℕ → ℤ), pathHist j x = pathHist j y → i + m ≤ j →
        vExitTime (W (x i)) (pathShift i x) = (m : ℕ∞) → vExitTime (W (y i)) (pathShift i y) = (m : ℕ∞) := by
      intro j i m x y hxy hle hV
      have hxi : x i = y i := pathHist_apply_of_le hxy i (by omega)
      have hc := (NextExitStop.vExitTime_pathShift_congr (W (x i)) hle hxy).1 hV
      rw [hxi] at hc
      exact hc
    have fwdT : ∀ (j : ℕ) (x y : ℕ → ℤ), pathHist j x = pathHist j y →
        τ (N + 1) x = (j : ℕ∞) → τ (N + 1) y = (j : ℕ∞) := by
      intro j x y hxy hx
      obtain ⟨i, m, hsum, hi, hV⟩ := decomp j x hx
      have hiy : τ N y = (i : ℕ∞) := (hT i x y (pathHist_mono (by omega) hxy)).1 hi
      have hVy := vexit_transfer j i m x y hxy (by omega) hV
      rw [recomp i m y hiy hVy, hsum]
    have fwdS : ∀ (j : ℕ) (x y : ℕ → ℤ), pathHist j x = pathHist j y → x ∈ S (N + 1) →
        τ (N + 1) x = (j : ℕ∞) → y ∈ S (N + 1) := by
      intro j x y hxy hxS hx
      obtain ⟨i, m, hsum, hi, hV⟩ := decomp j x hx
      rw [hSsucc N] at hxS
      obtain ⟨hxS', hx2⟩ := hxS
      obtain ⟨k, hk, hpass⟩ := hx2
      have hkey : k = i := by
        have := hk.symm.trans hi
        exact_mod_cast this
      have hpx : pathShift i x ∈ stayInRegionOf W Aof (x i) := by
        rw [hkey] at hpass
        exact hpass
      have hyS : y ∈ S N := ((hSd i x y (pathHist_mono (by omega) hxy)).1 ⟨hxS', hi⟩).1
      have hiy : τ N y = (i : ℕ∞) := (hT i x y (pathHist_mono (by omega) hxy)).1 hi
      have hVy := vexit_transfer j i m x y hxy (by omega) hV
      rw [hSsucc N]
      refine ⟨hyS, ?_⟩
      refine ⟨i, hiy, ?_⟩
      intro n hn
      rw [hVy] at hn
      have hnm : n < m := by exact_mod_cast hn
      have hn' : (n : ℕ∞) < vExitTime (W (x i)) (pathShift i x) := by
        rw [hV]
        exact hn
      have hxa : x (i + n) ∈ Aof (x i) := hpx n hn'
      have hyx : x (i + n) = y (i + n) := pathHist_apply_of_le hxy (i + n) (by omega)
      have hxi : x i = y i := pathHist_apply_of_le hxy i (by omega)
      show y (i + n) ∈ Aof (y i)
      rw [← hyx, ← hxi]
      exact hxa
    refine ⟨fun j x y hxy => ⟨fun hx => fwdT j x y hxy hx, fun hy => fwdT j y x hxy.symm hy⟩,
      fun j x y hxy => ⟨fun h => ⟨fwdS j x y hxy h.1 h.2, fwdT j x y hxy h.2⟩,
        fun h => ⟨fwdS j y x hxy.symm h.1 h.2, fwdT j y x hxy.symm h.2⟩⟩⟩

/-- **The stopping property of the successive exit-time tests** (the `hstop` hypothesis of
`srwLaw_successive_tests_le_pow`, LEMMA68 N3c). -/
theorem successive_stop_fin (W : ℤ → Set ℤ) (Aof : ℤ → Set ℤ) (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ N x (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf W Aof (x k)}) :
    ∀ N k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S N ∩ {x | τ N x = k} = {x | pathHist k x ∈ F} := by
  intro N k
  obtain ⟨_, hSd⟩ := successive_stop_inv W Aof τ S hτ0 hτsucc hτtop hS0 hSsucc N
  obtain ⟨F, hF, hEq⟩ := NextExitStop.exists_pathHist_of_determinacy k
    (fun x => x ∈ S N ∧ τ N x = k) (fun x y hxy => hSd k x y hxy)
  refine ⟨F, hF, ?_⟩
  ext x
  have hx := Set.ext_iff.1 hEq x
  simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq] using hx

/-- **The first `N` successive exit-time tests are all passed with probability at most `c ^ N`** (LEMMA68 N3c with the
concrete stopping property above). The hypotheses `hc` (one-test bound from every state in `Y`) and `hSY` (the state at
the start of each test lies in `Y` on the event that the previous tests are passed) are the remaining inputs. -/
theorem srwLaw_successive_exit_le_pow_Of (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ) (Aof : ℤ → Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ N x (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf W Aof (x k)})
    {Y : Set ℤ} {c : ℝ≥0∞}
    (hc : ∀ y ∈ Y, srwLaw m y (stayInRegionOf W Aof y) ≤ c)
    (hSY : ∀ N, ∀ x ∈ S N, ∀ k : ℕ, τ N x = k → x k ∈ Y) (N : ℕ) :
    srwLaw m a (S N) ≤ c ^ N :=
  srwLaw_successive_tests_le_pow m a τ (fun _ y => stayInRegionOf W Aof y)
    (fun _ y => measurableSet_stayInRegionOf W Aof y) (fun _ y hy => hc y hy) S hS0 hSsucc
    (successive_stop_fin W Aof τ S hτ0 hτsucc hτtop hS0 hSsucc) hSY N

/-- The constant-region form: `stayInRegion W A` for every centre (the statement used by `TailBound68`). -/
theorem srwLaw_successive_exit_le_pow (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ) (A : Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ N x (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegion W A (x k)})
    {Y : Set ℤ} {c : ℝ≥0∞}
    (hc : ∀ y ∈ Y, srwLaw m y (stayInRegion W A y) ≤ c)
    (hSY : ∀ N, ∀ x ∈ S N, ∀ k : ℕ, τ N x = k → x k ∈ Y) (N : ℕ) :
    srwLaw m a (S N) ≤ c ^ N :=
  srwLaw_successive_exit_le_pow_Of m a W (fun _ => A) τ S hτ0 hτsucc hτtop hS0 hSsucc hc hSY N

#print axioms MatedCRT.SuccessiveExitStop.successive_stop_fin
#print axioms MatedCRT.SuccessiveExitStop.srwLaw_successive_exit_le_pow

end SuccessiveExitStop

end MatedCRT
