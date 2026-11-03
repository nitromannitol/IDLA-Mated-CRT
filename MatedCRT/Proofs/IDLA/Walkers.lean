import MatedCRT.Proofs.IDLA.Measurable

/-!
# The first `n` walkers of the IDLA walker sequence

`walkerSequenceLaw_map_fin`: under `walkerSequenceLaw m a` (independent walks from `a`), the first `n` walkers
`(xs 0, …, xs (n-1))` have the law `walkersLaw m (fun _ => a)` of `n` independent walks from `a`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem measurable_restrictFin (n : ℕ) :
    Measurable fun xs : ℕ → ℕ → ℤ => fun i : Fin n => xs i :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The first `n` walkers of the walker sequence are `n` independent walks. -/
theorem walkerSequenceLaw_map_fin (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) :
    (walkerSequenceLaw m a).map (fun xs : ℕ → ℕ → ℤ => fun i : Fin n => xs i) = walkersLaw m (fun _ => a) := by
  unfold walkersLaw walkerSequenceLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_restrictFin n) (MeasurableSet.univ_pi hs)]
  have hpre : (fun xs : ℕ → ℕ → ℤ => fun i : Fin n => xs i) ⁻¹' Set.univ.pi s =
      (↑(Finset.range n) : Set ℕ).pi (fun j => if h : j < n then s ⟨j, h⟩ else univ) := by
    ext xs
    simp only [mem_preimage, mem_pi, Finset.coe_range, mem_Iio]
    constructor
    · intro h j hj
      rw [dite_eq_left hj]
      exact h ⟨j, hj⟩ (mem_univ _)
    · intro h i _
      have h' := h i i.2
      rwa [dite_eq_left i.2] at h'
  have hmeas : ∀ j ∈ Finset.range n, MeasurableSet (if h : j < n then s ⟨j, h⟩ else (univ : Set (ℕ → ℤ))) := by
    intro j _
    split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre, Measure.infinitePi_pi _ hmeas,
    ← Fin.prod_univ_eq_prod_range (fun j => srwLaw m a (if h : j < n then s ⟨j, h⟩ else univ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [dite_eq_left i.2]

end MatedCRT
