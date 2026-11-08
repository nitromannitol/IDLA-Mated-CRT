import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Polish and Borel structure of the circle-process space `C((0,∞) × ℂ, ℝ)`

Source: env-steps.tex:112 (the positive-circle index `E = (0,∞) × ℂ`) and env-steps.tex:380 (`H = C(E,ℝ)` with the
compact-open topology), the ambient space of the all-start clock lemma `lem:allstarts` (env-steps.tex:380-446).

This file supplies the Polish and Borel instances that `MatedCRT/Proofs/Sec1/EnvironmentScaling/AllStartsClock.lean`
currently takes as binders (`[PolishSpace CircleFns]`, `[MeasurableSpace CircleFns] [BorelSpace CircleFns]`). It adds no
hypothesis. It uses only Mathlib declarations:
* `ContinuousMap.compactConvergenceUniformSpace` (Topology/UniformSpace/CompactConvergence.lean:169): a uniformity on
  `C(α,β)` whose topology is the compact-open topology (`replaceTopology`).
* its uniformity is countably generated when `α` is weakly locally compact and σ-compact (line 233), and complete when
  `α` is compactly coherent (line 432; `CompactlyCoherentSpace.of_weaklyLocallyCompactSpace`).
* `IsCompletelyMetrizableSpace.of_completeSpace_metrizable` (Topology/Metrizable/CompletelyMetrizable.lean:183) gives complete
  metrizability; `ContinuousMap.instSecondCountableTopology` (Topology/ContinuousMap/SecondCountableSpace.lean) gives second
  countability; `PolishSpace` is their conjunction (Topology/MetricSpace/Polish.lean:62).
* `ContinuousMap.measurableSpace` and `BorelSpace C(X,Y)` (MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean:51-53)
  give the Borel structure; `ContinuousMap.measurable_eval` and `ContinuousMap.measurable_iff_eval` give the measurable
  evaluation and the coordinate criterion for measurable maps into `H`.

The index space `E` is an open subset of `ℝ` times `ℂ`: it is locally compact, σ-compact and second countable.
-/

open MeasureTheory TopologicalSpace

namespace MatedCRT.CircleProcessSpace

/-- The positive-circle index set `E = (0,∞) × ℂ` (env-steps.tex:112). It is the same type as
`MatedCRT.AllStarts.PosCircle` in `AllStartsClock.lean`. -/
abbrev PosCircleIndex : Type := Set.Ioi (0 : ℝ) × ℂ

/-- The space `H = C(E, ℝ)` of continuous positive-circle functions with the compact-open topology
(env-steps.tex:380). It is the same type as `MatedCRT.AllStarts.CircleFns`. -/
abbrev PosCircleFns : Type := C(PosCircleIndex, ℝ)

/-! ### Domain instances on `E = (0,∞) × ℂ` -/

/-- `(0,∞)` is an open subset of `ℝ`, hence locally compact (Topology/Compactness/LocallyCompact.lean:224). -/
instance posRadius_locallyCompactSpace : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

instance posCircleIndex_locallyCompactSpace : LocallyCompactSpace PosCircleIndex := inferInstance

instance posCircleIndex_weaklyLocallyCompactSpace : WeaklyLocallyCompactSpace PosCircleIndex := inferInstance

instance posCircleIndex_sigmaCompactSpace : SigmaCompactSpace PosCircleIndex := inferInstance

instance posCircleIndex_secondCountableTopology : SecondCountableTopology PosCircleIndex := inferInstance

/-! ### Complete metrizability and the Polish structure on `H = C(E,ℝ)` -/

/-- `H = C(E,ℝ)` is completely metrizable for the compact-open topology: its compact-convergence uniformity is
countably generated and complete, and it is T0 (Hausdorff). -/
theorem posCircleFns_isCompletelyMetrizableSpace :
    IsCompletelyMetrizableSpace PosCircleFns :=
  IsCompletelyMetrizableSpace.of_completeSpace_metrizable

/-- The Polish structure on `H = C(E,ℝ)` with the compact-open topology (env-steps.tex:380). -/
instance posCircleFns_polishSpace : PolishSpace PosCircleFns where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := posCircleFns_isCompletelyMetrizableSpace

/-! ### Borel structure on `H` -/

/-- Evaluation at a positive-circle index is Borel measurable on `H`. -/
lemma measurable_posCircleFns_eval (p : PosCircleIndex) :
    Measurable fun f : PosCircleFns => f p :=
  ContinuousMap.measurable_eval p

/-- A map into `H` is Borel measurable iff every evaluation at a positive-circle index is measurable. -/
lemma measurable_iff_eval_posCircleFns {Z : Type*} [MeasurableSpace Z] {g : Z → PosCircleFns} :
    Measurable g ↔ ∀ p : PosCircleIndex, Measurable fun z => g z p :=
  ContinuousMap.measurable_iff_eval

end MatedCRT.CircleProcessSpace
