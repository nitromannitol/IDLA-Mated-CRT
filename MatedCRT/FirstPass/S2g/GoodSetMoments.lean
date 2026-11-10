import Mathlib

/-!
# Measurable moment vectors of locally finite measures (q1, fp-S2g)

Helper for the good-set step `ConeHalfBallGoodMeasureLawStep` (`S2g/HalfBallGood.lean`), route 5 of `notes/q1.md`:
the moment vector `ν ↦ (∫ φ_k dν)_k` of a countable test family is measurable on the space of measures `Measure ℂ`, and
the set of locally finite measures is measurable. Mathlib has no `measurable_integral` for `ν ↦ ∫ f dν`, so the integral is
written as the difference of two lintegrals (the Bochner formula `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`),
which is measurable in `ν` for every measurable `f`. The two agree on locally finite measures and continuous compactly
supported `f`, which is the only case used (the moments of the cone and source LQG measures, Duplantier-Sheffield 2011).

Terminology: Giry monad and the Borel structure on measures (Kallenberg), locally finite Radon measures on `ℂ`
(Bogachev, Mathlib `IsLocallyFiniteMeasure`).
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- The integral `∫ f dν` written with lintegrals, `(∫⁻ f⁺ dν).toReal - (∫⁻ f⁻ dν).toReal`; defined for every measure. -/
noncomputable def intG (f : ℂ → ℝ) (ν : Measure ℂ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-f x) ∂ν).toReal

/-- `ν ↦ intG f ν` is measurable on the space of measures, for every measurable `f`. -/
theorem measurable_intG {f : ℂ → ℝ} (hf : Measurable f) : Measurable (intG f) := by
  unfold intG
  exact ((Measure.measurable_lintegral hf.ennreal_ofReal).ennreal_toReal).sub
    ((Measure.measurable_lintegral hf.neg.ennreal_ofReal).ennreal_toReal)

/-- On a locally finite measure, `intG` is the Bochner integral of a continuous compactly supported `f`. -/
theorem intG_eq_integral {f : ℂ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (ν : Measure ℂ)
    [IsLocallyFiniteMeasure ν] : intG f ν = ∫ x, f x ∂ν :=
  (integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hf.integrable_of_hasCompactSupport hcs)).symm

/-- A measure on `ℂ` is locally finite iff it is finite on every closed disc of integer radius. -/
theorem isLocallyFiniteMeasure_iff_closedBall (ν : Measure ℂ) :
    IsLocallyFiniteMeasure ν ↔ ∀ n : ℕ, ν (closedBall (0 : ℂ) n) < ⊤ := by
  constructor
  · intro _ n
    exact (isCompact_closedBall _ _).measure_lt_top
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine ⟨ball (0 : ℂ) n, isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hn), ?_⟩
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (h n)

/-- The locally finite measures form a measurable set of measures. -/
theorem measurableSet_isLocallyFinite : MeasurableSet {ν : Measure ℂ | IsLocallyFiniteMeasure ν} := by
  have hset : {ν : Measure ℂ | IsLocallyFiniteMeasure ν} =
      ⋂ n : ℕ, {ν : Measure ℂ | ν (closedBall (0 : ℂ) n) < ⊤} := by
    ext ν
    simp only [Set.mem_ofPred_eq, mem_iInter, isLocallyFiniteMeasure_iff_closedBall]
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Measure.measurable_coe isClosed_closedBall.measurableSet) measurable_const

/-- The moment vector of a test family `φ : ℕ → ℂ → ℝ` (the frozen law's `fun ω k => ∫ φ k dμ ω`), for all measures. -/
noncomputable def momentVec (φ : ℕ → ℂ → ℝ) (ν : Measure ℂ) : ℕ → ℝ := fun k => intG (φ k) ν

/-- The moment vector is measurable from the space of measures to `ℕ → ℝ`, for measurable test functions. -/
theorem measurable_momentVec {φ : ℕ → ℂ → ℝ} (hφ : ∀ k, Measurable (φ k)) : Measurable (momentVec φ) :=
  Measurable.of_eval fun k => measurable_intG (hφ k)

/-- On locally finite measures the moment vector is the vector of Bochner integrals. -/
theorem momentVec_eq_integral {φ : ℕ → ℂ → ℝ} (hφ : ∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k))
    (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] : momentVec φ ν = fun k => ∫ x, φ k x ∂ν :=
  funext fun k => intG_eq_integral (hφ k).1 (hφ k).2 ν

/-- The shape of the good set of `ConeHalfBallGoodMeasureLawStep`: locally finite measures whose moment vector lies in a
Borel set `B` of `ℕ → ℝ`. -/
def lfMomentSet (φ : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)) : Set (Measure ℂ) :=
  {ν | IsLocallyFiniteMeasure ν} ∩ momentVec φ ⁻¹' B

/-- The good-set shape is a measurable set of measures when `B` is Borel. -/
theorem measurableSet_lfMomentSet {φ : ℕ → ℂ → ℝ} (hφ : ∀ k, Measurable (φ k)) {B : Set (ℕ → ℝ)}
    (hB : MeasurableSet B) : MeasurableSet (lfMomentSet φ B) :=
  measurableSet_isLocallyFinite.inter ((measurable_momentVec hφ) hB)

end MatedCRT
