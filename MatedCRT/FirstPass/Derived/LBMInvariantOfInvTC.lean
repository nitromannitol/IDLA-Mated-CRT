import MatedCRT.FirstPass.Derived.MarkovTimeChange
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputs

/-!
# Invariance of the Liouville Brownian motion law family from invariance of the time change

Two transfer steps for the invariance half of Definition 7.3 of Berestycki–Gwynne (2020) for the field of laws of
the rescaled Liouville Brownian motion.

* `isInvariantFor_of_isInvTC`: let `G` be an `ℝ≥0`-valued version of a real clock `F` (almost surely
  `(G t b : ℝ) = F b t` for all `t`), with `F b` almost surely a time-change clock. If the time change of planar
  Brownian motion by `G` leaves `ν` invariant (`IsInvTC planarLaw G ν`), then `ν` is invariant
  (`IsInvariantFor`) for any family of path laws equal to the laws of the time-changed path
  `t ↦ b (F(b)⁻¹(t))` (`lbmContinuousPath F`). The two right inverses `inf {t | u < G t b}` (in `ℝ≥0`) and
  `inf {t | u < F b t}` (in `ℝ`) are equal.
* `IsInvariantFor.timeScaleLawField`, `IsInvariantFor.lbmPathLawField`: a linear time change `t ↦ m t` of every
  path law preserves invariant measures; in particular the rescaling of the law field by the median `m_γ`.
-/

namespace MatedCRT

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

/-- The right inverse `inf {t | u < G t b}` of an `ℝ≥0`-valued clock equals the right inverse
`inf {t | u < f t}` of a real clock `f` that agrees with it at all times. -/
theorem clockInverse_eq_of_coe_eq {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {f : ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} (h : ∀ t, (G t b : ℝ) = f t) (u : ℝ≥0) :
    MatedCRT.clockInverse G u b = _root_.HarmonicBalls.clockInverse f u := by
  refine congrArg sInf (Set.ext fun t => ?_)
  show u < G t b ↔ (u : ℝ) < f t
  rw [← h t, NNReal.coe_lt_coe]

/-- For a time-change clock `F b`, the Liouville Brownian motion path at time `u` is the Brownian path `b` at the
right inverse of any `ℝ≥0`-valued clock that agrees with `F b` at all times. -/
theorem lbmContinuousPath_apply_eq_clockInverse {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {b : ContinuousPath ℂ}
    (hT : _root_.HarmonicBalls.IsTimeChangeClock (F b)) (h : ∀ t, (G t b : ℝ) = F b t) (u : ℝ≥0) :
    lbmContinuousPath F b u = b (MatedCRT.clockInverse G u b) := by
  rw [lbmContinuousPath_of_isTimeChangeClock hT, clockInverse_eq_of_coe_eq h]
  rfl

/-- **Invariance passes from the time change of planar Brownian motion to the Liouville Brownian motion laws**
(Berestycki–Gwynne (2020), Definition 7.3). Let `G` be an `ℝ≥0`-valued version of the real clock `F`, that is,
for `ν`-almost every `z`, almost surely under planar Brownian motion from `z`, `F b` is a time-change clock and
`(G t b : ℝ) = F b t` for all `t`. If `ν` is invariant for the time change of planar Brownian motion by `G`, then
`ν` is invariant for every family of path laws `P` with `P z` the law of `t ↦ b (F(b)⁻¹(t))` for `ν`-almost every
`z`. -/
theorem isInvariantFor_of_isInvTC {P : PathLawFamily} {ν : Measure ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hP : ∀ᵐ z ∂ν, ∃ hg : AEMeasurable (lbmContinuousPath F) (_root_.HarmonicBalls.planarBrownianMotion z),
      P z = planarBrownianPathLaw z (lbmContinuousPath F) hg)
    (hT : ∀ᵐ z ∂ν, ∀ᵐ b ∂planarLaw z, _root_.HarmonicBalls.IsTimeChangeClock (F b))
    (hGF : ∀ᵐ z ∂ν, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    (hinv : IsInvTC planarLaw G ν) : IsInvariantFor P ν := by
  intro t A hA
  rw [← hinv t A hA]
  refine lintegral_congr_ae ?_
  filter_upwards [hP, hT, hGF] with z hPz hTz hGz
  obtain ⟨hg, hPz⟩ := hPz
  have hmeas : MeasurableSet {x : ContinuousPath ℂ | x t ∈ A} := (continuous_eval_const t).measurable hA
  rw [hPz]
  change (Measure.map (lbmContinuousPath F) (_root_.HarmonicBalls.planarBrownianMotion z))
    {x | x t ∈ A} = _
  rw [Measure.map_apply_of_aemeasurable hg hmeas]
  change planarLaw z _ = planarLaw z _
  refine measure_congr ?_
  filter_upwards [hTz, hGz] with b hb hbG
  change (lbmContinuousPath F b t ∈ A) = (b (MatedCRT.clockInverse G t b) ∈ A)
  rw [lbmContinuousPath_apply_eq_clockInverse hb hbG]

/-- **A linear time change preserves invariant measures** (Definition 7.3): if `μ` is invariant for the family `K`,
it is invariant for `z ↦ (q ↦ [t ↦ q(m t)])_* K(z)`. -/
theorem IsInvariantFor.timeScaleLawField {K : PathLawFamily} {μ : Measure ℂ} (h : IsInvariantFor K μ)
    (m : ℝ≥0) : IsInvariantFor (timeScaleLawField m K) μ := by
  intro t A hA
  rw [← h (m * t) A hA]
  have hmeas : MeasurableSet {x : ContinuousPath ℂ | x t ∈ A} := (continuous_eval_const t).measurable hA
  refine lintegral_congr fun z => ?_
  change (timeScaleLaw m (K z) : Measure (ContinuousPath ℂ)) {x | x t ∈ A} = _
  rw [coe_timeScaleLaw, Measure.map_apply (measurable_timeScalePath m) hmeas]
  rfl

/-- The rescaling of a field of path laws by the median `m_γ` preserves invariant measures. -/
theorem IsInvariantFor.rescaledLBMLawField {X : Type*}
    {Λ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} {m : ℝ → ℝ} {γ : ℝ} {x : X}
    {μ : Measure ℂ} (h : IsInvariantFor (Λ γ x) μ) :
    IsInvariantFor (rescaledLBMLawField Λ m γ x) μ :=
  h.timeScaleLawField _

/-- **Invariance for the field of laws of the rescaled Liouville Brownian motion** (Berestycki–Gwynne (2020),
(1.6)): an invariant measure of the selected law field `K_γ(x)` is invariant for `lbmPathLawField γ x`. -/
theorem IsInvariantFor.lbmPathLawField {γ : ℝ} {x : LQGMetric.CoordJ → ℝ} {μ : Measure ℂ}
    (h : IsInvariantFor (lbmLawFieldSelection γ coordCircleGood x) μ) :
    IsInvariantFor (lbmPathLawField γ x) μ :=
  h.rescaledLBMLawField (Λ := fun γ => lbmLawFieldSelection γ coordCircleGood)

end MatedCRT
