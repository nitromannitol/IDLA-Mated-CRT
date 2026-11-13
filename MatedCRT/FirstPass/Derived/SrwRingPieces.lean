import MatedCRT.FirstPass.Derived.SrwAnnulusExit
import MatedCRT.FirstPass.S4S6c.TraceFrom68
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15ACore

/-!
# Pathwise pieces for the ring estimate: first circle before the barrier, and measurable disconnection events

Two pieces of the proof of Berestycki–Gwynne (2020), Lemma 3.10, used in the assembly of the walk event from two
strong Markov restarts.

* `ae_srwLaw_hitCircle_before`: simple random walk started at a vertex whose cell lies in the open annulus
  `a < ‖· - c‖ < b` (a finite set of such vertices) almost surely hits, at a finite time, a vertex whose cell meets the
  circle of radius `a` or `b`, and has not met a set `I` of vertices off both circles up to that time
  (the last visit uses `LatticeProb.LQG.exists_lt_index_meets_circle_of_mem`).
* `measurableSet_disconnectsBeforeHit_paths`: for a locally finite multigraph on a countable vertex type, the event
  that a vertex path hits `T` at a finite time `n` and its trace before `n` disconnects `S` from `T` is measurable
  on `ℕ → V` (a countable union over `n` of events determined by the first `n + 1` vertices).
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- **The first circle is met before the barrier.** Simple random walk from a vertex whose cell lies in the open
annulus `a < ‖· - c‖ < b` almost surely hits, at a finite time, the set `I₀` of vertices whose cell meets one of the two
circles, and meets no vertex of `I` up to that time, when every vertex of `I` has a cell inside the open disc of
radius `a` or outside the closed disc of radius `b`. -/
theorem ae_srwLaw_hitCircle_before {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {cell : ℤ → Set ℂ} (hJ : ∀ k, IsPreconnected (cell k))
    (hne : ∀ k, (cell k).Nonempty) (hmeet : ∀ j k, m j k ≠ 0 → (cell j ∩ cell k).Nonempty)
    {c : ℂ} {a b : ℝ} (hF : (LatticeProb.LQG.annulusCells cell c a b).Finite) {x : ℤ}
    (hx : x ∈ LatticeProb.LQG.annulusCells cell c a b) {I : Set ℤ}
    (hI : ∀ k ∈ I, (∀ y ∈ cell k, dist y c < a) ∨ (∀ y ∈ cell k, b < dist y c)) :
    ∀ᵐ ξ ∂srwLaw m x,
      vHitTime {k | ∃ p ∈ cell k, dist p c = a ∨ dist p c = b} ξ ≠ ⊤ ∧
        ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime {k | ∃ p ∈ cell k, dist p c = a ∨ dist p c = b} ξ → ξ i ∉ I := by
  filter_upwards [srwLaw_ae_start m x, FrontierSeparation.ae_srwStep_legal m x,
    ae_srwLaw_exists_meets_circle hlf hcons hJ hne hmeet hF hx] with ξ h0 hstep hmeets
  have hξ : ∀ i, (cell (ξ i) ∩ cell (ξ (i + 1))).Nonempty := by
    intro i
    rcases hstep i with h | h
    · rw [h, Set.inter_self]
      exact hne _
    · exact hmeet _ _ h
  have h0' : ξ 0 ∈ LatticeProb.LQG.annulusCells cell c a b := by
    rw [h0]
    exact hx
  obtain ⟨i₀, p₀, hp₀, hd₀⟩ := hmeets
  have hle := TraceFrom68.vHitTime_le_of_mem
    (F := {k | ∃ p ∈ cell k, dist p c = a ∨ dist p c = b}) (x := ξ) (n := i₀) ⟨p₀, hp₀, hd₀⟩
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top i₀) hle, fun i hi hiI => ?_⟩
  obtain ⟨j, hj, q, hq, hqd⟩ := LatticeProb.LQG.exists_lt_index_meets_circle_of_mem hJ hne hξ h0' hI hiI
  have hle' := TraceFrom68.vHitTime_le_of_mem
    (F := {k | ∃ p ∈ cell k, dist p c = a ∨ dist p c = b}) (x := ξ) (n := j) ⟨q, hq, hqd⟩
  have hlt : ((j : ℕ) : ℕ∞) < (i : ℕ∞) := by exact_mod_cast hj
  exact absurd (lt_of_le_of_lt hle' hlt) (not_lt.mpr hi)

end MatedCRT

namespace MatedCRTHarmonic.GMSMain.T15A

open MatedCRTHarmonic

variable {V E : Type*}

/-- **Measurability of the disconnection event on vertex paths.** For every multigraph `G` on a countable vertex type
with measurable singletons, the set of vertex paths `X` that hit `T` at a finite time `n` such that the vertices
visited before `n` disconnect `S` from `T` is measurable. -/
theorem measurableSet_disconnectsBeforeHit_paths [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (G : LFMultigraph V E) (S T : Set V) :
    MeasurableSet {X : ℕ → V | DisconnectsBeforeHit G S T X} := by
  have hset : {X : ℕ → V | DisconnectsBeforeHit G S T X} =
      ⋃ n : ℕ, {X | Markov.hitTime T X = n ∧ G.Disconnects {y | ∃ m < n, X m = y} S T} := by
    ext X
    simp only [DisconnectsBeforeHit, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion fun n => GoodScales.measurableSet_of_forall_eq_le n ?_
  rintro X X' hagree ⟨hn, hd⟩
  refine ⟨GoodScales.hitTime_eq_of_forall_eq hn hagree, ?_⟩
  have htr : {y | ∃ m < n, X' m = y} = {y | ∃ m < n, X m = y} := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, hagree m hm.le⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, (hagree m hm.le).symm⟩
  rw [htr]
  exact hd

/-- The walk event of (3.35) is a measurable set of vertex paths. -/
theorem measurableSet_lemma311Event_paths [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (G : LFMultigraph V E) (J : V → Set ℂ) (z : ℂ) (r : ℝ) :
    MeasurableSet {X : ℕ → V | Lemma311Event G J z r X} :=
  measurableSet_disconnectsBeforeHit_paths G _ _

end MatedCRTHarmonic.GMSMain.T15A

/-! ## Audit -/
#print axioms MatedCRT.ae_srwLaw_hitCircle_before
#print axioms MatedCRTHarmonic.GMSMain.T15A.measurableSet_disconnectsBeforeHit_paths
#print axioms MatedCRTHarmonic.GMSMain.T15A.measurableSet_lemma311Event_paths
