import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-!
# Finite exit data of finite vertex sets and of the interior cell vertices of a bounded domain

For the multigraph `m` of a mated-CRT map (locally finite, with the consecutive edges
`m k (k+1) ≠ 0`), every finite vertex set `A ⊆ ℤ` is a finite exit datum
(`MatedCRT.FirstPass36.FiniteExitData m A`): each vertex of `A` has positive degree, and the
walk `a, a+1, a+2, …` reaches the boundary `∂A` inside the closure `cl(A) = A ∪ ∂A` along
consecutive integers.  Since `V^ε(D)` is finite for a bounded domain `D` and a proper curve,
this supplies the finite exit data of the interior cell vertices `V^ε(D) \ V^ε(∂D)` and the
almost-sure finiteness of the exit time from `V^ε(D)` for every starting vertex.
-/

open Set Metric Filter Topology

namespace MatedCRT
namespace ExitFiniteData

open MatedCRT.FirstPass36 (FiniteExitData)

/-- Along the consecutive integers `a, a+1, …, a+n`, all of which lie in `S`, there is a path of
the multigraph `m` in `S` from `a` to `a + n`, as soon as `m k (k+1) ≠ 0` for every `k`. -/
theorem exists_isVPathIn_consecutive {m : ℤ → ℤ → ℕ} (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (S : Set ℤ) : ∀ (n : ℕ) (a : ℤ), (∀ i : ℕ, i ≤ n → a + (i : ℤ) ∈ S) →
      ∃ p : List ℤ, IsVPathIn m S p a (a + (n : ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro a h
    refine ⟨[a], by simp, by simp, ?_, by simp⟩
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    simpa using h 0 le_rfl
  | succ n ih =>
    intro a h
    obtain ⟨p, hh, hl, hmem, hch⟩ := ih (a + 1) (fun i hi => by
      have := h (i + 1) (by omega)
      have e : a + ((i + 1 : ℕ) : ℤ) = a + 1 + (i : ℤ) := by push_cast; ring
      rwa [e] at this)
    cases p with
    | nil => simp at hh
    | cons c l =>
      have hc : c = a + 1 := by simpa using hh
      subst hc
      refine ⟨a :: (a + 1) :: l, by simp, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons_cons, hl]
        congr 1
        push_cast
        ring
      · intro c hc'
        rcases List.mem_cons.1 hc' with rfl | hc''
        · simpa using h 0 (by omega)
        · exact hmem c hc''
      · exact List.isChain_cons_cons.2 ⟨hcons a, hch⟩

/-- **Finite exit datum**: every finite vertex set of a locally finite multigraph with the
consecutive edges `m k (k+1) ≠ 0` is a finite exit datum. -/
theorem finiteExitData_of_finite {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) : FiniteExitData m A := by
  classical
  refine ⟨hA, fun a _ => Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (hcons a)), ?_⟩
  intro a ha
  obtain ⟨M, hM⟩ := hA.bddAbove
  have hex : ∃ n : ℕ, a + (n : ℤ) ∉ A := by
    refine ⟨(M - a).toNat + 1, fun hmem => ?_⟩
    have h1 := hM hmem
    have h2 : M - a ≤ ((M - a).toNat : ℤ) := Int.self_le_toNat _
    push_cast at h1
    omega
  obtain ⟨n0, hn0, hmin⟩ : ∃ n0 : ℕ, a + (n0 : ℤ) ∉ A ∧ ∀ i : ℕ, i < n0 → a + (i : ℤ) ∈ A :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by simpa using Nat.find_min hex hi⟩
  cases n0 with
  | zero => exact (hn0 (by simpa using ha)).elim
  | succ k =>
    have e : a + ((k + 1 : ℕ) : ℤ) = (a + (k : ℤ)) + 1 := by push_cast; ring
    have hb : a + ((k + 1 : ℕ) : ℤ) ∈ vBoundary m A :=
      ⟨hn0, a + (k : ℤ), hmin k (Nat.lt_succ_self k), by rw [e]; exact hcons _⟩
    obtain ⟨p, hp⟩ := exists_isVPathIn_consecutive hcons (vClosure m A) (k + 1) a (fun i hi => by
      by_cases hik : i < k + 1
      · exact Or.inl (hmin i hik)
      · have : i = k + 1 := by omega
        subst this
        exact Or.inr hb)
    exact ⟨_, hb, p, hp⟩

/-- The interior cell vertices of a bounded domain are a finite exit datum. -/
theorem finiteExitData_interiorCellVertices {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {D : Set ℂ} (hD : Bornology.IsBounded D) :
    FiniteExitData m (interiorCellVertices ε η D) :=
  finiteExitData_of_finite hlf hcons
    ((Tightness.cellVertices_finite hη hp hε hD).subset fun _ h => h.1)

/-- The walk exits the cell vertices of a bounded domain almost surely, from every starting
vertex. -/
theorem srwLaw_vExitTime_eq_top_null_cellVertices {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {D : Set ℂ} (hD : Bornology.IsBounded D)
    (x : ℤ) : srwLaw m x {X | vExitTime (interiorCellVertices ε η D) X = ⊤} = 0 :=
  ExitNull68.exit_null_of_finite hlf hcons
    ((Tightness.cellVertices_finite hη hp hε hD).subset fun _ h => h.1) x

end ExitFiniteData
end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ExitFiniteData.finiteExitData_of_finite
#print axioms MatedCRT.ExitFiniteData.srwLaw_vExitTime_eq_top_null_cellVertices
