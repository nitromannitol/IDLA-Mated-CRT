import MatedCRT.FirstPass.S3f.Decomposition
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryStartingExit
import MatedCRT.FirstPass.Frozen.S3S4b

/-!
# First pass: the finite-domain Dirichlet representation as a theorem

`FrozenFiniteDomainDirichletRepresentation` (MatedCRT/FirstPass/Frozen/S3S4b.lean) is the random-walk fact of Lawler–Limic,
*Random Walk: A Modern Introduction* (Cambridge 2010), Corollary 6.2.4, used by the corrected Lemma 3.5. Its content is proved in
the Proofs tree: `eq_exitValue_sub_greenPotential` (Proofs/Sec3/DiscreteDirichletProblem/Decomposition.lean) gives the identity on
`A ∪ B`, and `ae_vExitPosition_mem` and `ae_vExitPosition_eq_start_of_not_mem` give the almost sure exit in `B`. This file proves
the frozen Prop, so the corrected Lemma 3.5 needs no frozen input for it.
-/

namespace MatedCRT.FirstPass37

open MeasureTheory Set

/-- The finite-domain Dirichlet representation (Lawler–Limic Corollary 6.2.4) as a theorem: the statement of
`FrozenFiniteDomainDirichletRepresentation`, with no frozen hypothesis. -/
theorem frozenFiniteDomainDirichletRepresentation_proved : FrozenFiniteDomainDirichletRepresentation := by
  unfold FrozenFiniteDomainDirichletRepresentation FiniteDomainDirichletRepresentation
  intro m hlf hcons A B hA hB hnb hexit F g hF a ha
  refine ⟨?_, MatedCRT.FirstPass37.eq_exitValue_sub_greenPotential hlf hcons hA hB hnb hexit F g hF ha⟩
  by_cases haA : a ∈ A
  · filter_upwards [MatedCRT.FirstPass37.ae_vExitPosition_mem hnb haA, hexit a haA] with x h1 h2
    exact h1 h2
  · have haB : a ∈ B := by
      rcases ha with h | h
      · exact absurd h haA
      · exact h
    filter_upwards [MatedCRT.ae_vExitPosition_eq_start_of_not_mem (m := m) haA] with x hx
    rw [hx]
    exact haB

end MatedCRT.FirstPass37

#print axioms MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved
