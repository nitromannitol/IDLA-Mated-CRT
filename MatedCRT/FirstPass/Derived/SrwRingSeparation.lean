import MatedCRT.FirstPass.Derived.SrwTwoRestart
import MatedCRT.FirstPass.Derived.HarnackSingleRing
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import LatticeProb.LQG.ChainAnnulusCrossing
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15ACore

/-!
# The two-restart event separates a vertex from the barrier

Pathwise step of the proof of Berestycki–Gwynne (2020), Lemma 3.10 (display (3.21)).  Fix a centre `w`, a radius
`r ≥ 0`, a set `B` of vertices whose cell comes within `2r` of `w`, and a barrier `I` of vertices having a cell point at
distance `≥ 2r` from `w`.  Let `E` be the walk event "hits `T = V(∂B_{2r}(w))` at a finite time `n` and the vertices
visited before `n` separate `S = V(∂B_{r/2}(w))` from `T`" (`sepBeforeHit`, the event of Lemma 3.11, display (3.35)).

If the walk hits `I₀` without meeting `I`, then hits `B` without meeting `I`, and then performs the event `E` (the
`twoRestartEvent`), and consecutive cells of the walk meet, then the trace of the walk before the first visit to `I`
separates every vertex `y` with a cell point in `B̄_{r/2}(w)` from `I`.  The cells visited by the third stage cannot
lie in `I`, since a chain of connected cells from a cell near `w` to a cell reaching distance `2r` meets `∂B_{2r}(w)`
before leaving it; the separation then follows from the separation by two spheres.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov
open WalkPotential

/-- **The walk event of display (3.35), for a graph on `ℤ`**: the path hits `T` at a finite time `n` and the vertices
visited strictly before `n` separate `S` from `T` in `Γ`. -/
def sepBeforeHit (Γ : SimpleGraph ℤ) (S T : Set ℤ) (X : ℕ → ℤ) : Prop :=
  ∃ n : ℕ, hitTime T X = n ∧ GraphSeparates Γ {y | ∃ m < n, X m = y} S T

/-- The disconnection event of a multigraph on `ℤ` is `sepBeforeHit` of its simple graph. -/
theorem disconnectsBeforeHit_iff_sepBeforeHit {E : Type*} (G : LFMultigraph ℤ E) (S T : Set ℤ) (X : ℕ → ℤ) :
    MatedCRTHarmonic.GMSMain.T15A.DisconnectsBeforeHit G S T X ↔ sepBeforeHit G.adj S T X :=
  Iff.rfl

/-- **Separation by the two-restart event** (pathwise). -/
theorem graphSeparates_of_mem_twoRestartEvent {Γ : SimpleGraph ℤ} {J : ℤ → Set ℂ}
    (hJ : ∀ k, IsPreconnected (J k)) (hΓ : ∀ j k, Γ.Adj j k → (J j ∩ J k).Nonempty)
    {w : ℂ} {r : ℝ} (hr : 0 ≤ r) {S T B I₀ I : Set ℤ}
    (hS : ∀ k, ∀ x ∈ J k, dist x w = r / 2 → k ∈ S) (hT : ∀ k, ∀ x ∈ J k, dist x w = 2 * r → k ∈ T)
    (hB : ∀ k ∈ B, ∃ x ∈ J k, dist x w ≤ 2 * r) {y : ℤ} (hy : ∃ x ∈ J y, dist x w ≤ r / 2)
    (hI : ∀ k ∈ I, ∃ x ∈ J k, 2 * r ≤ dist x w) {ξ : ℕ → ℤ}
    (hξ : ∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty)
    (hmem : ξ ∈ twoRestartEvent I₀ B I {X | sepBeforeHit Γ S T X}) :
    GraphSeparates Γ (traceBefore (id : ℤ → ℤ) I ξ) {y} I := by
  obtain ⟨k, -, hk, t, ht, htI, n, hn, hsep⟩ := hmem
  have hXeq : pathShift t (pathShift k ξ) = fun j => ξ (k + t + j) := by
    funext j
    simp only [pathShift]
    rw [add_assoc]
  simp only [hXeq] at hn hsep
  have hBt : ξ (k + t) ∈ B := by
    have h1 := ((TraceFrom68.vHitTime_eq_iff B t (pathShift k ξ)).1 ht).1
    simpa [pathShift] using h1
  have hpre : ∀ i ≤ k + t, ξ i ∉ I := by
    intro i hi
    by_cases hik : i ≤ k
    · exact hk i hik
    · have h' := htI (i - k) (by omega)
      have e : pathShift k ξ (i - k) = ξ i := by
        simp only [pathShift]
        congr 1
        omega
      rwa [e] at h'
  have hXc : ∀ i, (J (ξ (k + t + i)) ∩ J (ξ (k + t + (i + 1)))).Nonempty := fun i => hξ (k + t + i)
  have hnI : ∀ j < n, ξ (k + t + j) ∉ I := by
    intro j hj hmemI
    obtain ⟨x0, hx0J, hx0⟩ := hB _ hBt
    obtain ⟨x1, hx1J, hx1⟩ := hI _ hmemI
    obtain ⟨i, hi, x, hxJ, hxd⟩ := LatticeProb.LQG.exists_le_mem_eq_of_chain
      (f := fun x : ℂ => dist x w) (continuous_id.dist continuous_const) hJ j (fun i => ξ (k + t + i)) hXc
      (r := 2 * r) ⟨x0, by simpa using hx0J, hx0⟩ ⟨x1, hx1J, hx1⟩
    exact ((hitTime_eq_coe_iff).1 hn).2 i (by omega) (hT _ x hxJ hxd)
  have hall : ∀ j < k + t + n, ξ j ∉ I := by
    intro j hj
    by_cases hjN : j ≤ k + t
    · exact hpre j hjN
    · have := hnI (j - (k + t)) (by omega)
      rwa [show k + t + (j - (k + t)) = j by omega] at this
  have hsub : {v | ∃ m < n, ξ (k + t + m) = v} ⊆ traceBefore (id : ℤ → ℤ) I ξ := by
    rintro v ⟨m, hm, rfl⟩
    exact subset_traceBefore_of_forall_not_mem hall ⟨k + t + m, by omega, rfl⟩
  exact graphSeparates_of_two_spheres hJ hΓ (c := w) (r₁ := r / 2) (r₂ := 2 * r) (by linarith) hS hT hsub hy hI hsep

/-- **Probability of separation from the two restarts.** If `p` bounds from above the probability of the
`twoRestartEvent` for the simple random walk on `m`, then it bounds from above the probability that the trace before the
first visit to `I` separates `y` from `I`, when adjacent cells meet. -/
theorem srwLaw_graphSeparates_lower {m : ℤ → ℤ → ℕ} {J : ℤ → Set ℂ}
    (hJ : ∀ k, IsPreconnected (J k)) (hne : ∀ k, (J k).Nonempty)
    (hmeet : ∀ j k, m j k ≠ 0 → (J j ∩ J k).Nonempty)
    {w : ℂ} {r : ℝ} (hr : 0 ≤ r) {S T B I₀ I : Set ℤ}
    (hS : ∀ k, ∀ x ∈ J k, dist x w = r / 2 → k ∈ S) (hT : ∀ k, ∀ x ∈ J k, dist x w = 2 * r → k ∈ T)
    (hB : ∀ k ∈ B, ∃ x ∈ J k, dist x w ≤ 2 * r) {y : ℤ} (hy : ∃ x ∈ J y, dist x w ≤ r / 2)
    (hI : ∀ k ∈ I, ∃ x ∈ J k, 2 * r ≤ dist x w) {a : ℤ} {p : ℝ≥0∞}
    (hp : p ≤ srwLaw m a (twoRestartEvent I₀ B I {X | sepBeforeHit (srwGraph m) S T X})) :
    p ≤ srwLaw m a {ξ | GraphSeparates (srwGraph m) (traceBefore (id : ℤ → ℤ) I ξ) {y} I} := by
  refine hp.trans (measure_mono_ae ?_)
  filter_upwards [FrontierSeparation.ae_srwStep_legal m a] with ξ hstep hmem
  have hξ : ∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty := by
    intro i
    rcases hstep i with h | h
    · rw [h, Set.inter_self]
      exact hne _
    · exact hmeet _ _ h
  have hΓ : ∀ j k, (srwGraph m).Adj j k → (J j ∩ J k).Nonempty := by
    rintro j k ⟨-, h | h⟩
    · exact hmeet _ _ h
    · rw [Set.inter_comm]
      exact hmeet _ _ h
  exact graphSeparates_of_mem_twoRestartEvent hJ hΓ hr hS hT hB hy hI hξ hmem

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.disconnectsBeforeHit_iff_sepBeforeHit
#print axioms MatedCRT.graphSeparates_of_mem_twoRestartEvent
#print axioms MatedCRT.srwLaw_graphSeparates_lower
