import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianShiftLaw

/-! # Stationarity of Brownian unit-interval oscillations -/

namespace MatedCRT

open Filter Set MeasureTheory ProbabilityTheory MarkovProcess Topology
open scoped NNReal

/-- The unit-interval oscillation measured at a fixed countable dense set. -/
noncomputable def sampledUnitOscillation (f : ℝ≥0 → ℝ) : ℝ :=
  ⨆ m : ℕ, |f (unitIntervalSample 0 m) - f 0|

theorem measurable_sampledUnitOscillation : Measurable sampledUnitOscillation := by
  unfold sampledUnitOscillation
  exact Measurable.iSup fun m =>
    ((measurable_pi_apply (unitIntervalSample 0 m)).sub (measurable_pi_apply 0)).abs

theorem unitOscillationMax_le_iff (n : ℕ) (w : ContinuousPath ℝ) {r : ℝ} (hr : 0 ≤ r) :
    unitOscillationMax n w ≤ r ↔ ∀ t : ℝ≥0,
      (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 → |w t - w (n : ℝ≥0)| ≤ r := by
  constructor
  · intro h t hnt htn
    exact (le_unitOscillationMax n w t hnt htn).trans h
  · intro h
    let I : Set ℝ≥0 := Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)
    let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
    change ‖w.restrict I - ContinuousMap.const I (w (n : ℝ≥0))‖ ≤ r
    apply (ContinuousMap.norm_le _ hr).mpr
    intro t
    simpa [Real.norm_eq_abs] using h t.1 t.2.1 t.2.2

/-- On continuous paths, the countable samples attain the compact-interval
supremum in the sense of least upper bounds. -/
theorem sampledUnitOscillation_eq (w : ContinuousPath ℝ) :
    sampledUnitOscillation (fun t => w t) = unitOscillationMax 0 w := by
  let I : Set ℝ≥0 := Icc ((0 : ℕ) : ℝ≥0) (((0 : ℕ) : ℝ≥0) + 1)
  let _ : Nonempty I := ⟨⟨(0 : ℕ), le_rfl, by simp⟩⟩
  have hsample (m : ℕ) : unitIntervalSample 0 m ∈ I := by
    change (TopologicalSpace.denseSeq I m).1 ∈ I
    exact (TopologicalSpace.denseSeq I m).2
  have hbdd : BddAbove (range (fun m : ℕ => |w (unitIntervalSample 0 m) - w 0|)) := by
    refine ⟨unitOscillationMax 0 w, ?_⟩
    rintro _ ⟨m, rfl⟩
    simpa only [Nat.cast_zero] using le_unitOscillationMax 0 w _ (hsample m).1 (hsample m).2
  have hsamp (m : ℕ) : |w (unitIntervalSample 0 m) - w 0| ≤
      sampledUnitOscillation (fun t => w t) := le_ciSup hbdd m
  apply le_antisymm
  · apply ciSup_le
    intro m
    simpa only [Nat.cast_zero] using le_unitOscillationMax 0 w _ (hsample m).1 (hsample m).2
  · have hn : 0 ≤ sampledUnitOscillation (fun t => w t) :=
      (abs_nonneg _).trans (hsamp 0)
    apply (unitOscillationMax_le_iff 0 w hn).2
    intro t _ ht
    let x : I := ⟨t, by simpa only [Nat.cast_zero] using (zero_le : (0 : ℝ≥0) ≤ t), ht⟩
    have hc : IsClosed {x : I | |w x.1 - w 0| ≤ sampledUnitOscillation (fun t => w t)} :=
      isClosed_le (((w.continuous.comp continuous_subtype_val).sub continuous_const).abs)
        continuous_const
    have hx := (TopologicalSpace.denseRange_denseSeq I).induction_on
      (p := fun x : I => |w x.1 - w 0| ≤ sampledUnitOscillation (fun t => w t)) x hc ?_
    · simpa only [Nat.cast_zero] using hx
    · intro m
      exact hsamp m

/-- Shifting and recentering a path moves its unit-interval maximum to time zero. -/
theorem unitOscillationMax_centered_shift (n : ℕ) (w : ContinuousPath ℝ) :
    let v := ContinuousPath.shift (n : ℝ≥0) w -
      ContinuousMap.const ℝ≥0 (w (n : ℝ≥0))
    unitOscillationMax 0 v = unitOscillationMax n w := by
  let v : ContinuousPath ℝ := ContinuousPath.shift (n : ℝ≥0) w -
    ContinuousMap.const ℝ≥0 (w (n : ℝ≥0))
  change unitOscillationMax 0 v = unitOscillationMax n w
  apply le_antisymm
  · apply (unitOscillationMax_le_iff 0 v (unitOscillationMax_nonneg n w)).2
    intro t _ ht
    have ht1 : t ≤ 1 := by simpa using ht
    have hupper : (n : ℝ≥0) + t ≤ (n : ℝ≥0) + 1 := by
      simpa [add_comm] using add_le_add_left ht1 (n : ℝ≥0)
    have h := le_unitOscillationMax n w ((n : ℝ≥0) + t)
      (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)) hupper
    simpa [v, ContinuousPath.shift_apply, Nat.cast_zero] using h
  · apply (unitOscillationMax_le_iff n w (unitOscillationMax_nonneg 0 v)).2
    intro t hnt htn
    have ht1 : t - (n : ℝ≥0) ≤ 1 := by
      rw [tsub_le_iff_right]
      simpa [add_comm] using htn
    have h := le_unitOscillationMax 0 v (t - (n : ℝ≥0))
      (by simp) (by simpa using ht1)
    simpa [v, ContinuousPath.shift_apply, Nat.cast_zero, add_tsub_cancel_of_le hnt] using h

/-- Brownian unit-interval maxima have a common distribution. -/
theorem unitOscillationMax_identDistrib (n : ℕ) :
    IdentDistrib (unitOscillationMax n) (unitOscillationMax 0)
      (brownianMotion 0) (brownianMotion 0) := by
  have h := (brownian_centered_shift_identDistrib (n : ℝ≥0)).comp
    measurable_sampledUnitOscillation
  convert h using 1
  · funext w
    dsimp only [Function.comp_apply]
    let v : ContinuousPath ℝ := ContinuousPath.shift (n : ℝ≥0) w -
      ContinuousMap.const ℝ≥0 (w (n : ℝ≥0))
    have heq : (fun t : ℝ≥0 => w ((n : ℝ≥0) + t) - w (n : ℝ≥0)) = fun t => v t := by
      funext t
      simp [v, ContinuousPath.shift_apply]
    rw [heq, sampledUnitOscillation_eq]
    exact (unitOscillationMax_centered_shift n w).symm
  · funext w
    dsimp only [Function.comp_apply]
    exact (sampledUnitOscillation_eq w).symm

/-- The only remaining Brownian input for the event-measurability reduction
is integrability of the maximum on the initial unit interval. -/
theorem convergenceDivisibleEventMeasurable_of_brownian_unit_max_integrable
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hint : Integrable (unitOscillationMax 0) (brownianMotion 0)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_unitOscillationMax 𝒮 h27 hscale hpos
    hint unitOscillationMax_identDistrib

end MatedCRT
