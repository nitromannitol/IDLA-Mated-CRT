import MatedCRT.FirstPass.Derived.SrwChainBridge
import MatedCRT.Defs.Map
import MatedCRT.Defs.WalkDisconnection

/-!
# Hitting distributions of simple random walk from two starting points

For simple random walk on a multigraph `m`, a vertex set `I` and two vertices `x, y`, the hitting distributions of
`I` from `x` and from `y` differ in total variation by at most the probability that the walk started at `x` does
**not** disconnect `y` from `I` before its first hit of `I` [GMS21, Lemma 3.12] (Gwynne-Miller-Sheffield,
arXiv:1807.07515; [GMS19, Lemma 3.10] in arXiv:1807.07511). The proof is the maximum-principle argument of
Bonanno's `HarmonicInfinity.hitLaw_le_add` and `HarmonicInfinity.abs_hitLaw_sub_le` (no Wilson algorithm), applied to
the nearest-neighbour chain `isNNChain_srwKernel`.

* `hitTime_eq_vHitTime`, `traceBefore_id_eq`: Bonanno's hitting time and trace are `vHitTime` and
  `walkTraceBefore`;
* `adjGraph_eq_srwGraph`: the two simple graphs of a multigraph agree;
* `graphSeparates_singleton_iff`: `K` meets every walk from `y` to `A` iff `K` disconnects `y` from `A`;
* `hitLaw_srwKernel_eq`, `setOf_graphSeparates_eq`: the hitting law and the separation event in walk-law form;
* `srwLaw_hit_le_add` (one-sided, no recurrence needed) and `abs_srwLaw_hit_sub_le` (total-variation form when `I`
  is hit almost surely from both vertices).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity

/-- `⨅_{n : q n} n = Nat.find` for a predicate `q` equivalent to `p`; the decidability instance of `p` is an implicit
argument, so that the lemma applies to `Nat.find` with any instance. -/
theorem iInf₂_coe_eq_find {p q : ℕ → Prop} {dp : DecidablePred p} (hpq : ∀ n, q n ↔ p n) (h : ∃ n, p n) :
    (⨅ (n : ℕ) (_ : q n), (n : ℕ∞)) = (@Nat.find p dp h : ℕ∞) := by
  apply le_antisymm
  · exact iInf₂_le _ ((hpq _).2 (Nat.find_spec h))
  · exact le_iInf₂ fun n hn => by exact_mod_cast Nat.find_min' h ((hpq n).1 hn)

/-- Bonanno's hitting time `inf {n : x n ∈ I}` is `vHitTime I`. -/
theorem hitTime_eq_vHitTime (I : Set ℤ) (x : ℕ → ℤ) : Markov.hitTime I x = vHitTime I x := by
  unfold Markov.hitTime vHitTime vExitTime
  split_ifs with h
  · exact iInf₂_coe_eq_find (fun n => by simp) h
  · exact le_antisymm le_top (le_iInf₂ fun n hn => (h ⟨n, by simpa using hn⟩).elim)

/-- The vertices visited before the first hit of `I`, in Bonanno's and in this repository's notation. -/
theorem traceBefore_id_eq (I : Set ℤ) (x : ℕ → ℤ) :
    traceBefore (id : ℤ → ℤ) I x = walkTraceBefore x (vHitTime I x) := by
  ext v
  simp only [traceBefore, walkTraceBefore, Set.preimage_id, Set.mem_ofPred_eq, id_eq, hitTime_eq_vHitTime]

/-- The simple graph `adjGraph m` of a multigraph is `srwGraph m`. -/
theorem adjGraph_eq_srwGraph (m : ℤ → ℤ → ℕ) : adjGraph m = srwGraph m := by
  ext a b
  simp [adjGraph, srwGraph]

/-- `K` meets every walk from `y` to `A` iff `K` disconnects `y` from `A` (no path in the graph induced on `Kᶜ`). -/
theorem graphSeparates_singleton_iff {V : Type*} (G : SimpleGraph V) (K A : Set V) (y : V) :
    GraphSeparates G K {y} A ↔ graphDisconnects G K y A := by
  constructor
  · intro h hy a ha hak hreach
    obtain ⟨p⟩ := hreach
    obtain ⟨v, hv, hvK⟩ := h y (Set.mem_singleton y) a ha (p.map (SimpleGraph.Embedding.induce Kᶜ).toHom)
    have hv' : v ∈ (p.map (SimpleGraph.Embedding.induce Kᶜ).toHom).support := hv
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv'
    exact u.2 hvK
  · intro h b hb a ha w
    rw [Set.mem_singleton_iff] at hb
    subst hb
    by_contra hn
    have hw : ∀ v ∈ w.support, v ∈ Kᶜ := fun v hv hvK => hn ⟨v, hv, hvK⟩
    exact h (hw b w.start_mem_support) a ha (hw a w.end_mem_support) ⟨w.induce Kᶜ hw⟩

/-- Bonanno's hitting law of `I` for simple random walk: the probability that the walk hits `I` and its first visit
to `I` is in `W`. -/
theorem hitLaw_srwKernel_eq (m : ℤ → ℤ → ℕ) (I W : Set ℤ) (a : ℤ) :
    hitLaw (srwKernel m) id I W a =
      srwLaw m a {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W} := by
  rw [hitLaw, chainLaw_srwKernel]
  congr 1
  ext w
  simp only [hitEvent, Markov.stopState, Set.preimage_id, Set.mem_ofPred_eq, hitTime_eq_vHitTime]

/-- The separation event of Bonanno's bound is the event `walkDisconnectsBeforeHit m I y`. -/
theorem setOf_graphSeparates_eq (m : ℤ → ℤ → ℕ) (I : Set ℤ) (y : ℤ) :
    {w : ℕ → ℤ | GraphSeparates (srwGraph m) (traceBefore id I w) {y} I} =
      {w | walkDisconnectsBeforeHit m I y w} := by
  ext w
  simp only [Set.mem_ofPred_eq, walkDisconnectsBeforeHit, traceBefore_id_eq, graphSeparates_singleton_iff,
    adjGraph_eq_srwGraph]

/-- **[GMS21, Lemma 3.12], one-sided form.** For simple random walk on a multigraph, every vertex set `I`, every
`W` and all vertices `x, y`: `P^y(X_{τ_I} ∈ W) ≤ P^x(X_{τ_I} ∈ W) + (1 - P^x(D))`, where `τ_I` is the hitting
time of `I` and `D` is the event that the walk from `x` disconnects `y` from `I` strictly before `τ_I`. -/
theorem srwLaw_hit_le_add (m : ℤ → ℤ → ℕ) (I W : Set ℤ) (x y : ℤ) :
    srwLaw m y {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W} ≤
      srwLaw m x {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W} +
        (1 - srwLaw m x {w | walkDisconnectsBeforeHit m I y w}) := by
  have h := hitLaw_le_add (isNNChain_srwKernel m) I W x y
  simp only [id_eq] at h
  rwa [hitLaw_srwKernel_eq, hitLaw_srwKernel_eq, setOf_graphSeparates_eq, chainLaw_srwKernel] at h

/-- **[GMS21, Lemma 3.12], total-variation form.** If simple random walk on a multigraph hits `I` almost surely
from `x` and from `y`, then for every `W`,
`|P^x(X_{τ_I} ∈ W) - P^y(X_{τ_I} ∈ W)| ≤ 1 - P^x(D)`, where `D` is the event that the walk from `x` disconnects
`y` from `I` strictly before `τ_I`. -/
theorem abs_srwLaw_hit_sub_le (m : ℤ → ℤ → ℕ) (I W : Set ℤ) {x y : ℤ}
    (hx : srwLaw m x {w | vHitTime I w ≠ ⊤} = 1) (hy : srwLaw m y {w | vHitTime I w ≠ ⊤} = 1) :
    |(srwLaw m x {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal -
        (srwLaw m y {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal| ≤
      1 - (srwLaw m x {w | walkDisconnectsBeforeHit m I y w}).toReal := by
  have hset : {w : ℕ → ℤ | Markov.hitTime (id ⁻¹' I) w ≠ ⊤} = {w | vHitTime I w ≠ ⊤} := by
    ext w
    simp only [Set.preimage_id, Set.mem_ofPred_eq, hitTime_eq_vHitTime]
  have h := abs_hitLaw_sub_le (isNNChain_srwKernel m) I W (x := x) (y := y)
    (by simp only [id_eq]; rw [hset, chainLaw_srwKernel]; exact hx)
    (by simp only [id_eq]; rw [hset, chainLaw_srwKernel]; exact hy)
  simp only [id_eq] at h
  rwa [hitLaw_srwKernel_eq, hitLaw_srwKernel_eq, setOf_graphSeparates_eq, chainLaw_srwKernel] at h

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.hitTime_eq_vHitTime
#print axioms MatedCRT.graphSeparates_singleton_iff
#print axioms MatedCRT.srwLaw_hit_le_add
#print axioms MatedCRT.abs_srwLaw_hit_sub_le
