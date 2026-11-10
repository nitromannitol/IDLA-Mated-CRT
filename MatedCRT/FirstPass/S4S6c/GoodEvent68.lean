import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# The good event of the printed Lemma 6.8: legal walks with almost surely finite window exits
(q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C1-C2, the event `Good` of `ConfigBound68`)

For a walk `x` from `b`, the good event is: `x 0 = b`, every step is a stay or an edge, and every window exit
`vExitTime (W (x i)) (pathShift i x)` is finite, where `W y` is the inner test window of the vertex `y`.

* `visit_exit_null`: the Markov property at the fixed time `n` (`srwLaw_markov`): the event "the walk is at `y` at time
  `n` and the exit of `A` from the shifted path is infinite" is null, given the start-level null set `h0`.
* `ae_all_exit_ne_top`: a countable union over the times and the vertices gives: almost surely every window exit along
  the path is finite. The windows need not be restricted to a band, so the event does not depend on the cluster `Θ`
  or the scale `r`.
* `ae_good`, `good_compl_null`: the legality (`FrontierSeparation.ae_srwStep_legal`) and the start (`srwLaw_ae_start`)
  are added; `good_compl_null` is the form `srwLaw m b Goodᶜ = 0` used by `ConfigBound68`.

The start-level null sets `hW` are the finite-window exits (`ExitNull68.exit_null_of_finite` discharges them for finite
windows; the windows `Wt y` are finite by the properness of `η`). No further probability input.
-/

open MeasureTheory Set

namespace MatedCRT

namespace GoodEvent68

/-- **Markov property at a fixed time.** The event that the walk from `b` is at `y` at time `n` and the exit of `A`
from the shifted path is infinite is null, given that the exit from `A` is a.s. finite from `y`
(`srwLaw_markov`: conditionally on the history up to `n`, the shifted path is the walk from `x n`). -/
theorem visit_exit_null (m : ℤ → ℤ → ℕ) (A : Set ℤ) (b y : ℤ) (n : ℕ)
    (h0 : srwLaw m y {x | vExitTime A x = ⊤} = 0) :
    srwLaw m b {x | x n = y ∧ vExitTime A (WalkPotential.pathShift n x) = ⊤} = 0 := by
  have hE : MeasurableSet {z : ℕ → ℤ | vExitTime A z = ⊤} := by
    have hset : {z : ℕ → ℤ | vExitTime A z = ⊤} = ⋂ k : ℕ, {z : ℕ → ℤ | z k ∈ A} := by
      ext z
      simp only [Set.mem_ofPred_eq, mem_iInter]
      constructor
      · intro h k
        by_contra hk
        have hex : ∃ j, z j ∉ A := ⟨k, hk⟩
        simp [vExitTime, hex] at h
      · intro h
        have hnot : ¬ ∃ j, z j ∉ A := by
          rintro ⟨j, hj⟩
          exact hj (h j)
        simp [vExitTime, hnot]
    rw [hset]
    exact MeasurableSet.iInter fun k => (measurable_pi_apply k) (Set.to_countable A).measurableSet
  have hFm : MeasurableSet {h : Fin (n + 1) → ℤ | h (Fin.last n) = y} :=
    (Set.to_countable _).measurableSet
  have hS : MeasurableSet {x : ℕ → ℤ | pathHist n x ∈ {h : Fin (n + 1) → ℤ | h (Fin.last n) = y}} :=
    measurable_pathHist n hFm
  have hset : {x : ℕ → ℤ | x n = y ∧ vExitTime A (WalkPotential.pathShift n x) = ⊤} =
      {x | pathHist n x ∈ {h : Fin (n + 1) → ℤ | h (Fin.last n) = y} ∧
        WalkPotential.pathShift n x ∈ {z : ℕ → ℤ | vExitTime A z = ⊤}} := by
    ext x
    simp [pathHist]
  rw [hset, srwLaw_markov m b n _ hE]
  have hfun : ∀ x ∈ {x : ℕ → ℤ | pathHist n x ∈ {h : Fin (n + 1) → ℤ | h (Fin.last n) = y}},
      srwLaw m (x n) {z : ℕ → ℤ | vExitTime A z = ⊤} = 0 := by
    intro x hx
    have hxn : x n = y := by simpa [pathHist] using hx
    rw [hxn]
    exact h0
  rw [setLIntegral_congr_fun hS hfun]
  simp

/-- **Almost surely finite window exits along the walk.** If each window `W y` has an a.s. finite exit from its own
start (`hW`), then almost surely every exit `vExitTime (W (x i)) (pathShift i x)` is finite, for all times `i`. -/
theorem ae_all_exit_ne_top (m : ℤ → ℤ → ℕ) (W : ℤ → Set ℤ) (b : ℤ)
    (hW : ∀ y, srwLaw m y {x | vExitTime (W y) x = ⊤} = 0) :
    ∀ᵐ x ∂srwLaw m b, ∀ i : ℕ, vExitTime (W (x i)) (WalkPotential.pathShift i x) ≠ ⊤ := by
  have hnull : srwLaw m b {x | ∃ i : ℕ, vExitTime (W (x i)) (WalkPotential.pathShift i x) = ⊤} = 0 := by
    have hsub : {x : ℕ → ℤ | ∃ i : ℕ, vExitTime (W (x i)) (WalkPotential.pathShift i x) = ⊤} ⊆
        ⋃ i : ℕ, ⋃ y : ℤ, {x | x i = y ∧ vExitTime (W y) (WalkPotential.pathShift i x) = ⊤} := by
      rintro x ⟨i, hi⟩
      exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨x i, rfl, hi⟩⟩
    refine measure_mono_null hsub ?_
    exact measure_iUnion_null fun i => measure_iUnion_null fun y =>
      visit_exit_null m (W y) b y i (hW y)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx i
  intro hi
  exact hx ⟨i, hi⟩

/-- **Good event (LEMMA68 C1-C2).** For the walk from `b`, almost surely: `x 0 = b`, every step is a stay or an edge
(`FrontierSeparation.ae_srwStep_legal`), and every window exit along the path is finite. -/
theorem ae_good (m : ℤ → ℤ → ℕ) (W : ℤ → Set ℤ) (b : ℤ)
    (hW : ∀ y, srwLaw m y {x | vExitTime (W y) x = ⊤} = 0) :
    ∀ᵐ x ∂srwLaw m b, x 0 = b ∧ (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
      ∀ i : ℕ, vExitTime (W (x i)) (WalkPotential.pathShift i x) ≠ ⊤ := by
  filter_upwards [srwLaw_ae_start m b, FrontierSeparation.ae_srwStep_legal m b,
    ae_all_exit_ne_top m W b hW] with x h0 hl hf
  exact ⟨h0, hl, hf⟩

/-- The complement of the good event is null: the form `srwLaw m b Goodᶜ = 0` used by `ConfigBound68` (`hGood`). -/
theorem good_compl_null (m : ℤ → ℤ → ℕ) (W : ℤ → Set ℤ) (b : ℤ)
    (hW : ∀ y, srwLaw m y {x | vExitTime (W y) x = ⊤} = 0) :
    srwLaw m b {x | ¬ (x 0 = b ∧ (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
      ∀ i : ℕ, vExitTime (W (x i)) (WalkPotential.pathShift i x) ≠ ⊤)} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_good m W b hW] with x hx hbad
  exact hbad hx

end GoodEvent68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.GoodEvent68.visit_exit_null
#print axioms MatedCRT.GoodEvent68.ae_all_exit_ne_top
#print axioms MatedCRT.GoodEvent68.ae_good
#print axioms MatedCRT.GoodEvent68.good_compl_null
