import MatedCRT.Steps.Sec4.ConvergenceDivisible

/-! Positive exit times under strictly increasing time changes. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter
open scoped ENNReal NNReal

/-- A clock inverse is at most any time whose clock value exceeds the target. -/
theorem clockInverse_le_of_lt {f : ℝ≥0 → ℝ} {t r : ℝ≥0} (h : (t : ℝ) < f r) :
    clockInverse f t ≤ r := by
  unfold clockInverse
  exact csInf_le' h

/-- A strictly increasing clock is inverted at each of its values. -/
theorem clockInverse_clockValue {f : ℝ≥0 → ℝ} (hzero : f 0 = 0)
    (hmono : StrictMono f) (r : ℝ≥0) :
    clockInverse f (Real.toNNReal (f r)) = r := by
  have hfr : 0 ≤ f r := by simpa [hzero] using hmono.monotone (show 0 ≤ r from bot_le)
  have hcoe : (Real.toNNReal (f r) : ℝ) = f r := Real.coe_toNNReal _ hfr
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro s hrs
    apply clockInverse_le_of_lt
    rw [hcoe]
    exact hmono hrs
  · unfold clockInverse
    apply le_csInf
    · refine ⟨r + 1, ?_⟩
      rw [hcoe]
      exact hmono (by simp)
    · intro s hs
      rw [hcoe] at hs
      exact (hmono.lt_iff_lt.mp hs).le

/-- A path which leaves a set still leaves it at a finite time after a strictly
increasing time change. -/
theorem lbmExitTime_lt_top_of_exists_exit {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {U : Set ℂ} (hF : IsTimeChangeClock (F b))
    (hexit : ∃ r : ℝ≥0, b r ∉ U) : lbmExitTime F U b < ⊤ := by
  obtain ⟨r, hr⟩ := hexit
  let q := Real.toNNReal (F b r)
  have hbound : lbmExitTime F U b ≤ (q : ℝ≥0∞) := by
    unfold lbmExitTime pathExitTime
    apply sInf_le
    refine ⟨q, rfl, ?_⟩
    change b (clockInverse (F b) q) ∉ U
    rw [clockInverse_clockValue hF.map_zero hF.strictMono r]
    exact hr
  exact lt_of_le_of_lt hbound ENNReal.coe_lt_top

/-- If a path stays in the domain through Brownian time `r`, its time-changed path
cannot leave before the clock reaches its value at `r`. -/
theorem clockValue_le_lbmExitTime_of_stays {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {U : Set ℂ} (hF : IsTimeChangeClock (F b)) (r : ℝ≥0)
    (hstays : ∀ s ≤ r, b s ∈ U) :
    (Real.toNNReal (F b r) : ℝ≥0∞) ≤ lbmExitTime F U b := by
  have hnonneg : 0 ≤ F b r := by
    simpa [hF.map_zero] using hF.strictMono.monotone (show 0 ≤ r from bot_le)
  unfold lbmExitTime pathExitTime
  apply le_sInf
  rintro _ ⟨t, rfl, ht⟩
  rw [ENNReal.coe_le_coe]
  by_contra h
  have ht' : (t : ℝ) < F b r := by
    have := lt_of_not_ge h
    simpa [Real.coe_toNNReal _ hnonneg] using (show (t : ℝ) < Real.toNNReal (F b r) by exact_mod_cast this)
  exact ht (hstays _ (clockInverse_le_of_lt ht'))

/-- An exit by Brownian time `r` occurs by the corresponding clock time after the
time change. -/
theorem lbmExitTime_le_clockValue_of_exit {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {U : Set ℂ} (hF : IsTimeChangeClock (F b)) (r : ℝ≥0)
    (hexit : ∃ s ≤ r, b s ∉ U) :
    lbmExitTime F U b ≤ (Real.toNNReal (F b r) : ℝ≥0∞) := by
  obtain ⟨s, hsr, hs⟩ := hexit
  calc
    lbmExitTime F U b ≤ (Real.toNNReal (F b s) : ℝ≥0∞) := by
      unfold lbmExitTime pathExitTime
      apply sInf_le
      refine ⟨Real.toNNReal (F b s), rfl, ?_⟩
      change b (clockInverse (F b) (Real.toNNReal (F b s))) ∉ U
      rw [clockInverse_clockValue hF.map_zero hF.strictMono s]
      exact hs
    _ ≤ (Real.toNNReal (F b r) : ℝ≥0∞) := by
      exact_mod_cast Real.toNNReal_le_toNNReal (hF.strictMono.monotone hsr)

/-- An early time-changed exit requires either an invalid clock, a small clock value,
or a Brownian exit by the chosen deterministic time. -/
theorem lbmExitTime_event_subset {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {U : Set ℂ} (r q : ℝ≥0) :
    {b | lbmExitTime F U b ≤ (q : ℝ≥0∞)} ⊆
      {b | ¬ IsTimeChangeClock (F b)} ∪
        {b | Real.toNNReal (F b r) ≤ q} ∪
        {b | ∃ s ≤ r, b s ∉ U} := by
  intro b hb
  by_cases hc : IsTimeChangeClock (F b)
  · by_cases hs : ∀ s ≤ r, b s ∈ U
    · left
      right
      exact ENNReal.coe_le_coe.mp ((clockValue_le_lbmExitTime_of_stays hc r hs).trans hb)
    · right
      push Not at hs
      exact hs
  · exact Or.inl (Or.inl hc)

/-- A late time-changed exit requires either an invalid clock, a large clock value,
or a Brownian path which has stayed in the domain through the chosen time. -/
theorem lbmExitTime_late_event_subset {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {U : Set ℂ} (r q : ℝ≥0) :
    {b | (q : ℝ≥0∞) < lbmExitTime F U b} ⊆
      {b | ¬ IsTimeChangeClock (F b)} ∪
        {b | q < Real.toNNReal (F b r)} ∪
        {b | ∀ s ≤ r, b s ∈ U} := by
  intro b hb
  by_cases hc : IsTimeChangeClock (F b)
  · by_cases hs : ∃ s ≤ r, b s ∉ U
    · left
      right
      exact ENNReal.coe_lt_coe.mp (hb.trans_le (lbmExitTime_le_clockValue_of_exit hc r hs))
    · right
      push Not at hs
      exact hs
  · exact Or.inl (Or.inl hc)

/-- Time changing a continuous path by a strictly increasing clock preserves positive
exit time from any open set containing the initial point. -/
theorem lbmExitTime_pos_of_mem {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {U : Set ℂ} (hU : IsOpen U) (hb : b 0 ∈ U)
    (hF : IsTimeChangeClock (F b)) : 0 < lbmExitTime F U b := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (b 0) hb
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.mp b.continuous 0 ε hε
  let r : ℝ≥0 := Real.toNNReal (δ / 2)
  have hr : 0 < r := by simp [r, hδ]
  have hrδ : (r : ℝ) < δ := by simp only [r, Real.coe_toNNReal _ (by positivity : 0 ≤ δ / 2)]; linarith
  have hFr : 0 < F b r := by simpa [hF.map_zero] using hF.strictMono hr
  let q : ℝ≥0 := ⟨F b r, hFr.le⟩
  have hq : (0 : ℝ≥0∞) < (q : ℝ≥0∞) := by exact_mod_cast hFr
  refine lt_of_lt_of_le hq ?_
  unfold lbmExitTime pathExitTime
  apply le_sInf
  rintro s ⟨t, rfl, ht⟩
  rw [ENNReal.coe_le_coe]
  by_contra h
  have htq : t < q := lt_of_not_ge h
  have hinv : clockInverse (F b) t ≤ r := clockInverse_le_of_lt (by exact_mod_cast htq)
  apply ht
  apply hball
  apply hcont
  rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact lt_of_le_of_lt (by exact_mod_cast hinv) hrδ

/-- For a valid environment, the Liouville Brownian exit time from a ball around
its starting point is positive for almost every environment and Brownian path. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_pos {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      0 < lbmExitTime (S.clock ω) (ball 0 r) b := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock 0).2, ae_planarBrownianMotion_eval_zero 0] with b hb hstart
  apply lbmExitTime_pos_of_mem isOpen_ball _ hb
  simpa [hstart] using (mem_ball_self hr : (0 : ℂ) ∈ ball 0 r)

/-- Almost-sure finiteness of Brownian exit implies the same for its LQG time change. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_lt_top_of_ae_brownianExitTime_lt_top
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) {U : Set ℂ}
    (hBM : ∀ᵐ b ∂planarBrownianMotion 0, ContinuousPath.exitTime U b < ⊤) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0, lbmExitTime (S.clock ω) U b < ⊤ := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock 0).2, hBM] with b hb hfinite
  exact lbmExitTime_lt_top_of_exists_exit hb ((ContinuousPath.exitTime_lt_top_iff U b).mp hfinite)

end MatedCRT
