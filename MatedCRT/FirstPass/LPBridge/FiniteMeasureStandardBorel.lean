import MatedCRT.FirstPass.Frozen.S5k
import LatticeProb.Prob.FiniteMeasureStandardBorel

/-!
# Bridge: finite measures on a closed disk form a standard Borel space

`MatedCRT.FrozenFiniteMeasureDiskStandardBorel` (FirstPass/Frozen/S5k.lean) is the standard Borel
structure of the finite measures on `ℂ` concentrated on a closed disk. It follows from the general
lattice-probability statements `LatticeProb.standardBorelSpace_finiteMeasure` (finite Borel measures
on a nonempty compact metric space) and `LatticeProb.standardBorelSpace_concentrated` (restriction to
a measurable set).
-/

namespace MatedCRT

open MeasureTheory

theorem frozenFiniteMeasureDiskStandardBorel_holds : FrozenFiniteMeasureDiskStandardBorel := by
  intro ρ hρ
  have hx : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := Metric.mem_closedBall_self hρ.le
  have hne : Nonempty (Metric.closedBall (0 : ℂ) ρ) := ⟨⟨0, hx⟩⟩
  have hcpt : CompactSpace (Metric.closedBall (0 : ℂ) ρ) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hsbs : StandardBorelSpace {μ : Measure (Metric.closedBall (0 : ℂ) ρ) // IsFiniteMeasure μ} :=
    LatticeProb.standardBorelSpace_finiteMeasure (⟨0, hx⟩ : Metric.closedBall (0 : ℂ) ρ)
  exact LatticeProb.standardBorelSpace_concentrated Metric.isClosed_closedBall.measurableSet

end MatedCRT
