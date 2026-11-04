import MatedCRT.Proofs.LBM.ExitPosition

/-! Exit times under the LQG clock. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The LBM exit time is the clock value at the Brownian exit time. -/
theorem lbmExitTime_eq_clockValue {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : IsTimeChangeClock (F b))
    (h0 : b 0 ∈ U) (hfin : ContinuousPath.exitTime U b < ⊤) :
    lbmExitTime F U b =
      (Real.toNNReal (F b (ContinuousPath.exitTime U b).toNNReal) : ℝ≥0∞) := by
  let τ := (ContinuousPath.exitTime U b).toNNReal
  let q := Real.toNNReal (F b τ)
  have htau : (τ : ℝ≥0∞) = ContinuousPath.exitTime U b :=
    ENNReal.coe_toNNReal (ne_of_lt hfin)
  have hboundary : b τ ∈ frontier U :=
    ContinuousPath.coordinate_exitTime_mem_frontier U hU b h0 (ne_of_lt hfin)
  have hout : b τ ∉ U := by
    intro h
    exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hU) hboundary) h
  have hinv : clockInverse (F b) q = τ :=
    clockInverse_clockValue hF.map_zero hF.strictMono τ
  have hle : lbmExitTime F U b ≤ (q : ℝ≥0∞) := by
    unfold lbmExitTime pathExitTime
    apply sInf_le
    refine ⟨q, rfl, ?_⟩
    change b (clockInverse (F b) q) ∉ U
    simpa only [hinv] using hout
  have hge : (q : ℝ≥0∞) ≤ lbmExitTime F U b := by
    unfold lbmExitTime pathExitTime
    apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    rw [ENNReal.coe_le_coe]
    by_contra hn
    have hlt : t < q := lt_of_not_ge hn
    have hinvlt : clockInverse (F b) t < τ := by
      rw [← hinv]
      exact IsTimeChangeClock.strictMono_clockInverse hF hlt
    apply ht
    change b (clockInverse (F b) t) ∈ U
    apply ContinuousPath.mem_of_lt_exitTime
    rw [← htau, ENNReal.coe_lt_coe]
    exact hinvlt
  exact le_antisymm hle hge

/-- Brownian motion and its LQG time change leave at the same spatial position. -/
theorem lbmExitPosition_eq_brownianExitPosition
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : IsTimeChangeClock (F b)) (h0 : b 0 ∈ U)
    (hfin : ContinuousPath.exitTime U b < ⊤) :
    pathExitPosition U (liouvilleBrownianPath F b) =
      b (ContinuousPath.exitTime U b).toNNReal := by
  change b (clockInverse (F b) ((lbmExitTime F U b).untopD 0)) = _
  rw [lbmExitTime_eq_clockValue hU hF h0 hfin]
  change b (clockInverse (F b) (Real.toNNReal (F b (ContinuousPath.exitTime U b).toNNReal))) = _
  exact congrArg b (clockInverse_clockValue hF.map_zero hF.strictMono _)

/-- Immediate crossing of the closure after Brownian exit is preserved by an LQG clock. -/
theorem lbm_frequently_outside_closure_after_exit
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : IsTimeChangeClock (F b)) (h0 : b 0 ∈ U)
    (hfin : ContinuousPath.exitTime U b < ⊤)
    (hregular : ∃ᶠ s in 𝓝[>] (ContinuousPath.exitTime U b).toNNReal, b s ∉ closure U) :
    ∃ᶠ t in 𝓝[>] (lbmExitTime F U b).toNNReal,
      liouvilleBrownianPath F b t ∉ closure U := by
  let τ := (ContinuousPath.exitTime U b).toNNReal
  let q : ℝ≥0 → ℝ≥0 := fun s => Real.toNNReal (F b s)
  have hq : StrictMono q := by
    intro s t hst
    apply (IsTimeChangeClock.strictMono_clockInverse hF).lt_iff_lt.mp
    simpa only [q, clockInverse_clockValue hF.map_zero hF.strictMono] using hst
  have hqcont : Continuous q := continuous_real_toNNReal.comp hF.continuous
  have hqtend : Tendsto q (𝓝[>] τ) (𝓝[>] (q τ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (hqcont.tendsto τ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hq hs
  have hcross : ∃ᶠ t in 𝓝[>] (q τ), liouvilleBrownianPath F b t ∉ closure U := by
    apply hqtend.frequently
    simpa only [liouvilleBrownianPath, q, clockInverse_clockValue hF.map_zero hF.strictMono]
      using hregular
  rw [lbmExitTime_eq_clockValue hU hF h0 hfin]
  change ∃ᶠ t in 𝓝[>] (q τ), liouvilleBrownianPath F b t ∉ closure U
  exact hcross

/-- A positive linear time rescaling divides a finite exit time by its rate. -/
theorem pathExitTime_mul_eq {U : Set ℂ} (hU : IsOpen U) (p : ContinuousPath ℂ)
    (h0 : p 0 ∈ U) (hfin : ContinuousPath.exitTime U p < ⊤)
    {c : ℝ≥0} (hc : 0 < c) :
    pathExitTime U (fun t => p (c * t)) =
      (((ContinuousPath.exitTime U p).toNNReal / c : ℝ≥0) : ℝ≥0∞) := by
  let τ := (ContinuousPath.exitTime U p).toNNReal
  have htau : (τ : ℝ≥0∞) = ContinuousPath.exitTime U p :=
    ENNReal.coe_toNNReal (ne_of_lt hfin)
  have hb : p τ ∈ frontier U :=
    ContinuousPath.coordinate_exitTime_mem_frontier U hU p h0 (ne_of_lt hfin)
  have hout : p τ ∉ U := fun h =>
    (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hU) hb) h
  apply le_antisymm
  · unfold pathExitTime
    apply sInf_le
    refine ⟨τ / c, rfl, ?_⟩
    simpa only [mul_div_cancel₀ τ (ne_of_gt hc)] using hout
  · unfold pathExitTime
    apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    rw [ENNReal.coe_le_coe]
    by_contra hn
    have hlt : c * t < τ := by
      have := (lt_div_iff₀ hc).mp (lt_of_not_ge hn)
      simpa only [mul_comm] using this
    apply ht
    apply ContinuousPath.mem_of_lt_exitTime
    rw [← htau, ENNReal.coe_lt_coe]
    exact hlt

/-- Immediate crossing is also preserved by a positive linear time rescaling. -/
theorem frequently_outside_closure_after_linear_time_change
    {U : Set ℂ} (hU : IsOpen U) (p : ContinuousPath ℂ) (h0 : p 0 ∈ U)
    (hfin : ContinuousPath.exitTime U p < ⊤) {c : ℝ≥0} (hc : 0 < c)
    (hregular : ∃ᶠ s in 𝓝[>] (ContinuousPath.exitTime U p).toNNReal,
      p s ∉ closure U) :
    ∃ᶠ t in 𝓝[>] (pathExitTime U (fun t => p (c * t))).toNNReal,
      p (c * t) ∉ closure U := by
  let τ := (ContinuousPath.exitTime U p).toNNReal
  let q : ℝ≥0 → ℝ≥0 := fun s => s / c
  have hq : StrictMono q := fun _ _ h => (div_lt_div_iff_of_pos_right hc).2 h
  have hqcont : Continuous q := continuous_id.div_const c
  have hqtend : Tendsto q (𝓝[>] τ) (𝓝[>] (q τ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (hqcont.tendsto τ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hq hs
  have hcross : ∃ᶠ t in 𝓝[>] (q τ), p (c * t) ∉ closure U := by
    apply hqtend.frequently
    simpa only [q, mul_div_cancel₀ _ (ne_of_gt hc)] using hregular
  rw [pathExitTime_mul_eq hU p h0 hfin hc]
  exact hcross

/-- The normalized LBM exit time is the Brownian exit clock value divided by the rate. -/
theorem rescaledLBMExitTime_eq_clockValue_div
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : IsTimeChangeClock (F b)) (h0 : b 0 ∈ U)
    (hfin : ContinuousPath.exitTime U b < ⊤) {m : ℝ} (hm : 0 < m) :
    pathExitTime U (rescaledLBMPath F m b) =
      ((Real.toNNReal (F b (ContinuousPath.exitTime U b).toNNReal) /
        Real.toNNReal m : ℝ≥0) : ℝ≥0∞) := by
  let p : ContinuousPath ℂ := ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath hF⟩
  have hinv0 : clockInverse (F b) 0 = 0 := by
    have h := clockInverse_clockValue hF.map_zero hF.strictMono 0
    simpa only [hF.map_zero, Real.toNNReal_zero] using h
  have hp0 : p 0 ∈ U := by
    change b (clockInverse (F b) 0) ∈ U
    simpa only [hinv0] using h0
  have hpfin : ContinuousPath.exitTime U p < ⊤ := by
    change lbmExitTime F U b < ⊤
    rw [lbmExitTime_eq_clockValue hU hF h0 hfin]
    exact ENNReal.coe_lt_top
  have h := pathExitTime_mul_eq hU p hp0 hpfin (Real.toNNReal_pos.mpr hm)
  change pathExitTime U (rescaledLBMPath F m b) =
    (((lbmExitTime F U b).toNNReal / Real.toNNReal m : ℝ≥0) : ℝ≥0∞) at h
  rw [lbmExitTime_eq_clockValue hU hF h0 hfin] at h
  exact h

/-- Brownian immediate crossing transfers to normalized Liouville Brownian motion. -/
theorem rescaledLBM_frequently_outside_closure_after_exit
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : IsTimeChangeClock (F b)) (h0 : b 0 ∈ U)
    (hfin : ContinuousPath.exitTime U b < ⊤) {m : ℝ} (hm : 0 < m)
    (hregular : ∃ᶠ s in 𝓝[>] (ContinuousPath.exitTime U b).toNNReal,
      b s ∉ closure U) :
    ∃ᶠ t in 𝓝[>] (pathExitTime U (rescaledLBMPath F m b)).toNNReal,
      rescaledLBMPath F m b t ∉ closure U := by
  let p : ContinuousPath ℂ := ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath hF⟩
  have hinv0 : clockInverse (F b) 0 = 0 := by
    have h := clockInverse_clockValue hF.map_zero hF.strictMono 0
    simpa only [hF.map_zero, Real.toNNReal_zero] using h
  have hp0 : p 0 ∈ U := by
    change b (clockInverse (F b) 0) ∈ U
    simpa only [hinv0] using h0
  have hpfin : ContinuousPath.exitTime U p < ⊤ := by
    change lbmExitTime F U b < ⊤
    rw [lbmExitTime_eq_clockValue hU hF h0 hfin]
    exact ENNReal.coe_lt_top
  have hpregular : ∃ᶠ s in 𝓝[>] (ContinuousPath.exitTime U p).toNNReal,
      p s ∉ closure U := lbm_frequently_outside_closure_after_exit hU hF h0 hfin hregular
  exact frequently_outside_closure_after_linear_time_change hU p hp0 hpfin
    (Real.toNNReal_pos.mpr hm) hpregular

end MatedCRT
