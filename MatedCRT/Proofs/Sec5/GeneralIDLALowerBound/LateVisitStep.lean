import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.LateVisit

/-!
# Lemma 5.2: `LateVisitUpperTailStep` (eq:strong-markov-reduction, line 2187)

The step is `lateVisitCount_upperTail` (MatedCRT/Proofs/Sec5/GeneralIDLALowerBound/LateVisit.lean).
-/

namespace MatedCRT

/-- **Step** `LateVisitUpperTailStep`. -/
theorem lateVisitUpperTailStep : LateVisitUpperTailStep := by
  intro m O a n l k hl hsum
  exact lateVisitCount_upperTail m O a n l k hl hsum

end MatedCRT
