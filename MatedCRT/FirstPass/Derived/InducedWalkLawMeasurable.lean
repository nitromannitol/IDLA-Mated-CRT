import MatedCRT.FirstPass.Derived.StoppedWalkLawMeasurable
import MatedCRT.Defs.Map

/-!
# Measurability of induced walk laws

Random induced multiplicities and the corresponding stopped walk laws are
measurable in the graph, inducing set, stopping set, and embedding.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal
open MatedCRT.ExitCouplingGlue

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- Each adjacency event of a random multiplicity graph is measurable. -/
theorem measurableSet_adjGraph_adj (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ u v, Measurable fun ω => M ω u v) (u v : ℤ) :
    MeasurableSet {ω | (adjGraph (M ω)).Adj u v} := by
  change MeasurableSet {ω | u ≠ v ∧ (M ω u v ≠ 0 ∨ M ω v u ≠ 0)}
  by_cases huv : u = v
  · subst v
    simp only [ne_eq, not_true_eq_false, false_and, Set.ofPred_false]
    exact MeasurableSet.empty
  · have hn (x y : ℤ) : MeasurableSet {ω | M ω x y ≠ 0} := by
      convert ((measurableSet_singleton (0 : ℕ)).preimage (hM x y)).compl using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, ne_eq]
    convert (hn u v).union (hn v u) using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, ne_eq, huv, not_false_eq_true, true_and]

open Classical in
/-- Each multiplicity of a random induced multigraph is measurable. -/
theorem measurable_induced_multiplicity (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ u v, Measurable fun ω => M ω u v) (A : Ω → Set ℤ)
    (hA : Measurable A) (u v : ℤ) :
    Measurable fun ω => if u ∈ A ω ∧ v ∈ A ω then M ω u v else 0 := by
  classical
  exact Measurable.ite ((measurableSet_setOfPred.2 ((measurable_set_mem u).comp hA)).inter
    (measurableSet_setOfPred.2 ((measurable_set_mem v).comp hA))) (hM u v) measurable_const

open Classical in
/-- The stopped interpolated law of a random induced walk is measurable. -/
theorem measurable_stoppedInterp_induced_srwLaw (V : Ω → Set ℤ) (hV : Measurable V)
    (v : Ω → ℤ → ℂ) (hv : Measurable v) (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ u w, Measurable fun ω => M ω u w) (A : Ω → Set ℤ)
    (hA : Measurable A) (m : ℝ≥0) (a : ℤ) :
    Measurable fun ω =>
      (srwLaw (fun u w => if u ∈ A ω ∧ w ∈ A ω then M ω u w else 0) a).map
        (stoppedInterp (v ω) m (V ω)) := by
  classical
  exact measurable_stoppedInterp_srwLaw V hV v hv
    (fun ω u w => if u ∈ A ω ∧ w ∈ A ω then M ω u w else 0)
    (measurable_induced_multiplicity M hM A hA) m a

end MatedCRT
