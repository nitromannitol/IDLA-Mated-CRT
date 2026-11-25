import MatedCRT.FirstPass.Derived.KilledOccupationMaximal
import MatedCRT.FirstPass.Derived.DiscTimeChangeLaw

/-!
# Exit-rate clocks as occupation functionals of the killed path

For an open set `D`, a rate `ρ ≥ 0` on `D` and a path `W`, the exit-rate clock `σ ↦ ∫_0^σ (exit rate)` (rate
`ρ(W_r)` before the exit time of `W` from `D`, unit rate afterwards) is the occupation functional of `ρ` along the
path killed at its exit from `D`, read at the time `σ`, plus the time spent after the exit, provided the occupation
functional is finite (`exitRateClock_eq`). Hence the gap of the exit-rate clocks of two rates is the gap of their
occupation functionals (`exitRateClock_sub_exitRateClock_eq`).

Stopping a path at its exit from `D` changes neither its exit time (`exitTime_stopAtExitTime`) nor its occupation
functionals (`killedOccupationGapUpTo_stopAtExitTime`). So, for a random path `T` with the law of Brownian motion from
`0` stopped at its exit from the unit disc, the probability that the exit-rate clocks of two rates along `T` differ by
more than `η` at some time, with finite occupation functionals, is at most the probability that the occupation
functionals of Brownian motion from `0` killed on exiting the unit disc differ by more than `η` at some time
(`measure_exists_lt_abs_exitRateClock_sub_le`): the event is read off the dyadic times.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

variable {D : Set ℂ}

/-! ### Stopping at the exit time -/

/-- Stopping a path at its exit time from an open set does not change the exit time. -/
theorem exitTime_stopAtExitTime (hD : IsOpen D) (W : ContinuousPath ℂ) :
    ContinuousPath.exitTime D (stopAtExitTime D W) = ContinuousPath.exitTime D W := by
  by_cases hτ : ContinuousPath.exitTime D W = ⊤
  · have hW : stopAtExitTime D W = W := by
      ext t
      simp only [stopAtExitTime, ContinuousMap.comp_apply, exitClamp_apply, hτ, ↓reduceIte]
    rw [hW]
  have happ : ∀ t : ℝ≥0, stopAtExitTime D W t = W (min t (ContinuousPath.exitTime D W).toNNReal) := by
    intro t
    simp only [stopAtExitTime, ContinuousMap.comp_apply, exitClamp_apply, hτ, ↓reduceIte]
  have hτeq : ContinuousPath.exitTime D W = ((ContinuousPath.exitTime D W).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hτ).symm
  have hexit : W (ContinuousPath.exitTime D W).toNNReal ∉ D := by
    by_cases h0 : W 0 ∈ D
    · have hfr := ContinuousPath.coordinate_exitTime_mem_frontier D hD W h0 hτ
      rw [hD.frontier_eq] at hfr
      exact hfr.2
    · have hle : ContinuousPath.exitTime D W ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
        ContinuousPath.exitTime_le_of_notMem D W 0 h0
      have h0' : (ContinuousPath.exitTime D W).toNNReal = 0 := by
        rw [hτeq] at hle
        exact le_antisymm (by exact_mod_cast hle) zero_le
      rw [h0']
      exact h0
  apply le_antisymm
  · rw [hτeq]
    refine ContinuousPath.exitTime_le_of_notMem D _ _ ?_
    rw [happ, min_self]
    exact hexit
  · rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    rw [happ] at ht
    rw [hτeq]
    by_contra hlt
    have hlt' : t < (ContinuousPath.exitTime D W).toNNReal := by exact_mod_cast not_le.1 hlt
    rw [min_eq_left hlt'.le] at ht
    refine ht (ContinuousPath.mem_of_lt_exitTime D W t ?_)
    rw [hτeq]
    exact_mod_cast hlt'

theorem killedTimes_stopAtExitTime (hD : IsOpen D) (W : ContinuousPath ℂ) :
    killedTimes D (stopAtExitTime D W) = killedTimes D W := by
  unfold killedTimes
  rw [exitTime_stopAtExitTime hD W]

theorem killedRate_stopAtExitTime (hD : IsOpen D) (f : ℂ → ℝ≥0∞) (W : ContinuousPath ℂ) (s : ℝ) :
    killedRate D f (stopAtExitTime D W) s = killedRate D f W s := by
  unfold killedRate
  rw [killedTimes_stopAtExitTime hD W]
  by_cases hs : s ∈ killedTimes D W
  · rw [indicator_of_mem hs, indicator_of_mem hs]
    have hW : stopAtExitTime D W s.toNNReal = W s.toNNReal := by
      simp only [stopAtExitTime, ContinuousMap.comp_apply, exitClamp_apply]
      split_ifs with hτ
      · rfl
      · have h2 : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ((ContinuousPath.exitTime D W).toNNReal : ℝ≥0∞) := by
          rw [ENNReal.coe_toNNReal hτ]
          exact hs.2
        rw [min_eq_left (ENNReal.coe_lt_coe.1 h2).le]
    rw [hW]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs]

/-- Stopping a path at its exit time from an open set does not change its occupation functionals. -/
theorem killedOccupationUpTo_stopAtExitTime (hD : IsOpen D) (f : ℂ → ℝ≥0∞) (W : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationUpTo D f (stopAtExitTime D W) t = killedOccupationUpTo D f W t := by
  have h : killedRate D f (stopAtExitTime D W) = killedRate D f W := funext (killedRate_stopAtExitTime hD f W)
  unfold killedOccupationUpTo
  rw [h]

theorem killedOccupationGapUpTo_stopAtExitTime (hD : IsOpen D) (f g : ℂ → ℝ≥0∞) (W : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationGapUpTo D f g (stopAtExitTime D W) t = killedOccupationGapUpTo D f g W t := by
  unfold killedOccupationGapUpTo
  rw [killedOccupationUpTo_stopAtExitTime hD, killedOccupationUpTo_stopAtExitTime hD]

/-! ### Exit-rate clocks and occupation functionals -/

theorem measurableSet_killedTimes (W : ContinuousPath ℂ) : MeasurableSet (killedTimes D W) :=
  measurableSet_Ioi.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

/-- **The exit-rate clock is the occupation functional plus the time after the exit.** For a Borel rate `ρ ≥ 0` on
the open set `D` whose occupation functional along `W` up to `σ` is finite,
`∫_0^σ (exit rate) = A^ρ_σ + |{0 < r ≤ σ : r ∉ (0, τ_D)}|`. -/
theorem exitRateClock_eq {ρ : ℂ → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ v ∈ D, 0 ≤ ρ v) {W : ContinuousPath ℂ}
    (σ : ℝ≥0) (hfin : killedOccupationUpTo D (fun v => ENNReal.ofReal (ρ v)) W σ ≠ ⊤) :
    exitRateClock D ρ W σ = (killedOccupationUpTo D (fun v => ENNReal.ofReal (ρ v)) W σ).toReal +
      ∫ r in Ioc (0 : ℝ) σ, (killedTimes D W)ᶜ.indicator (fun _ => (1 : ℝ)) r := by
  have hkT := measurableSet_killedTimes (D := D) W
  set φ : ℝ → ℝ := (killedTimes D W).indicator (fun s => ρ (W s.toNNReal)) with hφ
  have hφm : Measurable φ :=
    (hρ.comp (W.continuous.comp continuous_real_toNNReal).measurable).indicator hkT
  have hφ0 : ∀ s, 0 ≤ φ s := by
    intro s
    by_cases hs : s ∈ killedTimes D W
    · rw [hφ, indicator_of_mem hs]
      exact hρ0 _ (ContinuousPath.mem_of_lt_exitTime D W _ hs.2)
    · rw [hφ, indicator_of_notMem hs]
  have hpt : ∀ s, (Iic (σ : ℝ)).indicator (killedRate D (fun v => ENNReal.ofReal (ρ v)) W) s =
      (Ioc (0 : ℝ) σ).indicator (fun s => ENNReal.ofReal (φ s)) s := by
    intro s
    by_cases h1 : s ∈ Iic (σ : ℝ)
    · rw [indicator_of_mem h1]
      unfold killedRate
      by_cases hs : s ∈ killedTimes D W
      · rw [indicator_of_mem hs, indicator_of_mem (show s ∈ Ioc (0 : ℝ) σ from ⟨hs.1, h1⟩), hφ,
          indicator_of_mem hs]
      · have hφs : φ s = 0 := by rw [hφ, indicator_of_notMem hs]
        rw [indicator_of_notMem hs]
        simp [Set.indicator_apply, hφs]
    · rw [indicator_of_notMem h1, indicator_of_notMem (fun h : s ∈ Ioc (0 : ℝ) σ => h1 h.2)]
  have hkO : killedOccupationUpTo D (fun v => ENNReal.ofReal (ρ v)) W σ =
      ∫⁻ s in Ioc (0 : ℝ) σ, ENNReal.ofReal (φ s) := by
    unfold killedOccupationUpTo
    rw [← lintegral_indicator measurableSet_Ioc]
    exact lintegral_congr hpt
  have hφi : IntegrableOn φ (Ioc (0 : ℝ) σ) :=
    (lintegral_ofReal_ne_top_iff_integrable hφm.aestronglyMeasurable (ae_of_all _ hφ0)).1 (by rw [← hkO]; exact hfin)
  have hψi : IntegrableOn ((killedTimes D W)ᶜ.indicator (fun _ => (1 : ℝ))) (Ioc (0 : ℝ) σ) :=
    (intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := (σ : ℝ)) (c := (1 : ℝ))).1.indicator hkT.compl
  have hcongr : EqOn (exitRate D ρ W)
      (fun r => φ r + (killedTimes D W)ᶜ.indicator (fun _ => (1 : ℝ)) r) (Ioc (0 : ℝ) σ) := by
    intro r hr
    by_cases hs : r ∈ killedTimes D W
    · simp only [hφ, indicator_of_mem hs,
        indicator_of_notMem (show r ∉ (killedTimes D W)ᶜ from not_not_intro hs), add_zero]
      exact exitRate_of_lt_exitTime hs.2
    · have hle : ContinuousPath.exitTime D W ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        by_contra hlt
        exact hs ⟨hr.1, not_le.1 hlt⟩
      simp only [hφ, indicator_of_notMem hs, indicator_of_mem (show r ∈ (killedTimes D W)ᶜ from hs), zero_add]
      exact exitRate_of_exitTime_le hle
  unfold exitRateClock
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg σ), setIntegral_congr_fun measurableSet_Ioc hcongr,
    integral_add hφi hψi, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hφ0) hφm.aestronglyMeasurable, hkO]

/-- **The gap of two exit-rate clocks is the gap of the occupation functionals.** -/
theorem exitRateClock_sub_exitRateClock_eq {ρ ρ' : ℂ → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ0 : ∀ v ∈ D, 0 ≤ ρ v) (hρ0' : ∀ v ∈ D, 0 ≤ ρ' v) {W : ContinuousPath ℂ} (σ : ℝ≥0)
    (hfin : killedOccupationUpTo D (fun v => ENNReal.ofReal (ρ v)) W σ ≠ ⊤)
    (hfin' : killedOccupationUpTo D (fun v => ENNReal.ofReal (ρ' v)) W σ ≠ ⊤) :
    exitRateClock D ρ W σ - exitRateClock D ρ' W σ =
      killedOccupationGapUpTo D (fun v => ENNReal.ofReal (ρ v)) (fun v => ENNReal.ofReal (ρ' v)) W σ := by
  rw [exitRateClock_eq hρ hρ0 σ hfin, exitRateClock_eq hρ' hρ0' σ hfin']
  unfold killedOccupationGapUpTo
  ring

/-! ### Transfer to Brownian motion killed on exiting the unit disc -/

/-- **Gaps of exit-rate clocks along a path with the law of stopped disc Brownian motion.** Let `T` be a random path
with the law of Brownian motion from `0` stopped at its exit from the unit disc, and `ρ, ρ' ≥ 0` Borel rates on the
disc. The probability that the occupation functionals of `ρ, ρ'` along `T` are finite and the exit-rate clocks of
`ρ, ρ'` along `T` differ by more than `η` at some time is at most the probability that the occupation functionals of
`ρ, ρ'` along Brownian motion from `0` killed on exiting the disc differ by more than `η` at some time. -/
theorem measure_exists_lt_abs_exitRateClock_sub_le {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {T : Ω' → ContinuousPath ℂ} (hT : AEMeasurable T P)
    (hTmap : P.map T = (planarBrownianMotion 0).map (stopAtExitTime (ball (0 : ℂ) 1)))
    {ρ ρ' : ℂ → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hρ0 : ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ ρ v)
    (hρ0' : ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ ρ' v) (η : ℝ) :
    P {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ v)) (T ω) ≠ ⊤ ∧
        killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ' v)) (T ω) ≠ ⊤ ∧
        ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) ρ (T ω) σ - exitRateClock (ball 0 1) ρ' (T ω) σ|} ≤
      planarBrownianMotion 0 {W | ∃ t : ℝ, η < |killedOccupationGapUpTo (ball 0 1)
        (fun v => ENNReal.ofReal (ρ v)) (fun v => ENNReal.ofReal (ρ' v)) W t|} := by
  have hf : Measurable fun v => ENNReal.ofReal (ρ v) := ENNReal.measurable_ofReal.comp hρ
  have hf' : Measurable fun v => ENNReal.ofReal (ρ' v) := ENNReal.measurable_ofReal.comp hρ'
  have hgapm : ∀ t : ℝ, Measurable fun W => killedOccupationGapUpTo (ball (0 : ℂ) 1)
      (fun v => ENNReal.ofReal (ρ v)) (fun v => ENNReal.ofReal (ρ' v)) W t := by
    intro t
    have h1 : Measurable fun W : ContinuousPath ℂ =>
        killedOccupationUpTo (ball (0 : ℂ) 1) (fun v => ENNReal.ofReal (ρ v)) W t :=
      (measurable_killedOccupationUpTo isOpen_ball hf).comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable fun W : ContinuousPath ℂ =>
        killedOccupationUpTo (ball (0 : ℂ) 1) (fun v => ENNReal.ofReal (ρ' v)) W t :=
      (measurable_killedOccupationUpTo isOpen_ball hf').comp (measurable_id.prodMk measurable_const)
    exact h1.ennreal_toReal.sub h2.ennreal_toReal
  set S : Set (ContinuousPath ℂ) := ⋃ m : ℕ, ⋃ j : ℕ, {W | η < |killedOccupationGapUpTo (ball (0 : ℂ) 1)
    (fun v => ENNReal.ofReal (ρ v)) (fun v => ENNReal.ofReal (ρ' v)) W ((j : ℝ) / 2 ^ m)|} with hSdef
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun j =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hgapm _))
  have hsub : {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ v)) (T ω) ≠ ⊤ ∧
      killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ' v)) (T ω) ≠ ⊤ ∧
      ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) ρ (T ω) σ - exitRateClock (ball 0 1) ρ' (T ω) σ|} ⊆
      T ⁻¹' S := by
    rintro ω ⟨hfin, hfin', σ, hσ⟩
    have hfσ : killedOccupationUpTo (ball (0 : ℂ) 1) (fun v => ENNReal.ofReal (ρ v)) (T ω) σ ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (killedOccupationUpTo_le_killedOccupation _ _ _)
    have hfσ' : killedOccupationUpTo (ball (0 : ℂ) 1) (fun v => ENNReal.ofReal (ρ' v)) (T ω) σ ≠ ⊤ :=
      ne_top_of_le_ne_top hfin' (killedOccupationUpTo_le_killedOccupation _ _ _)
    rw [exitRateClock_sub_exitRateClock_eq hρ hρ' hρ0 hρ0' σ hfσ hfσ'] at hσ
    have hlim := (tendsto_killedOccupationGapUpTo_dyadicFloor isOpen_ball hf hf' hfin hfin'
      (NNReal.coe_nonneg σ)).abs
    obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hσ)).exists
    rw [coe_dyadicFloor] at hm
    exact mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨⌊(σ : ℝ) * 2 ^ m⌋₊, hm⟩⟩
  calc P {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ v)) (T ω) ≠ ⊤ ∧
        killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (ρ' v)) (T ω) ≠ ⊤ ∧
        ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) ρ (T ω) σ - exitRateClock (ball 0 1) ρ' (T ω) σ|}
      ≤ P (T ⁻¹' S) := measure_mono hsub
    _ = P.map T S := (Measure.map_apply_of_aemeasurable hT hS).symm
    _ = planarBrownianMotion 0 (stopAtExitTime (ball (0 : ℂ) 1) ⁻¹' S) := by
        rw [hTmap, Measure.map_apply (measurable_stopAtExitTime _ isOpen_ball) hS]
    _ ≤ _ := by
        refine measure_mono fun W hW => ?_
        obtain ⟨m, hm⟩ := mem_iUnion.1 hW
        obtain ⟨j, hj⟩ := mem_iUnion.1 hm
        refine ⟨(j : ℝ) / 2 ^ m, ?_⟩
        have hj' : η < |killedOccupationGapUpTo (ball (0 : ℂ) 1) (fun v => ENNReal.ofReal (ρ v))
            (fun v => ENNReal.ofReal (ρ' v)) (stopAtExitTime (ball (0 : ℂ) 1) W) ((j : ℝ) / 2 ^ m)| := hj
        rwa [killedOccupationGapUpTo_stopAtExitTime isOpen_ball] at hj'

end MatedCRT
