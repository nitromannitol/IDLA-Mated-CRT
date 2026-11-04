import MatedCRT.Steps.Sec6.IterativeBound
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Lemma 6.10: the walk path property (`SrwPathStep`)

Simple random walk on any multigraph `m` on `ℤ` started at `a` is almost surely at `a` at time `0`
(`srwLaw_ae_start`, MatedCRT/Proofs/Infra/RandomWalk.lean) and moves along edges (`srwAeAdjacentStep`).
-/

namespace MatedCRT

open MeasureTheory

/-- `SrwPathStep` holds. -/
theorem srwPathStep : SrwPathStep := fun m a => by
  filter_upwards [srwLaw_ae_start m a, srwAeAdjacentStep m a] with x h1 h2 using ⟨h1, h2⟩

end MatedCRT
