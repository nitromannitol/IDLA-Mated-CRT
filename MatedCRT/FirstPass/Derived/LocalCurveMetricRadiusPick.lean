import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import MatedCRT.Proposed.StoppedPoleReconstruction2026

/-!
# The local curve metric controls the curves stopped at some disc of a radius interval

For curves `β₁ β₂ : ℝ≥0 → ℂ` the local metric of Gwynne, Miller and Sheffield (arXiv:1807.07515, (1.7)-(1.8), p. 43;
the same metric is (2.2) of arXiv:1705.11161) is
`d^loc_CMP(β₁, β₂) = ∫₀^∞ e^{-r} (1 ∧ d_CMP(β₁|[0,T_{β₁,r}], β₂|[0,T_{β₂,r}])) dr`, where `T_{β,r}` is the exit time of
`β` from `B_r(0)`.

* `exitTime_eq_pathExitTime`: `T_{β,r}` is the first exit time `pathExitTime (ball 0 r) β`.
* `cmpEDist_stopAtExit_le_dCMP`: the distance modulo parametrization of the two curves stopped at their exit times
  from a set `U` is at most `d_CMP` of their restrictions to `[0, T₁]` and `[0, T₂]`: an increasing homeomorphism
  `φ : [0, T₁] → [0, T₂]` extends to one of `[0, ∞)` by the shift `t ↦ T₂ + (t - T₁)` after `T₁`
  (`extendIccOrderIso`).
* `exists_dCMP_lt_of_dLoc_lt`: if `d^loc_CMP(β₁, β₂) < e^{-b} s (b - a)` with `0 ≤ a < b` and `0 ≤ s ≤ 1`, then some
  radius `r ∈ (a, b)` has `d_CMP < s` (otherwise the integrand is at least `e^{-b} s` on `(a, b)`).
* `exists_cmpEDist_stopAtExit_lt_of_dLoc_lt`: the two combined, for the curves stopped at their exit from `B_r(0)`.

No measurability of the integrand is used: the lower bound is a pointwise comparison of lower Lebesgue integrals.
-/

namespace MatedCRT.LocalCurveMetricPick

open MeasureTheory Metric Set HarmonicBalls
open scoped ENNReal NNReal

/-- The exit time of (1.8) from `B_r(0)` is the first exit time of the path from the open ball. -/
theorem exitTime_eq_pathExitTime (β : ℝ≥0 → ℂ) (r : ℝ) :
    StoppedPoleReconstruction.exitTime β r = pathExitTime (ball (0 : ℂ) r) β := by
  have hmem : ∀ t : ℝ≥0, β t ∉ ball (0 : ℂ) r ↔ r ≤ ‖β t‖ := fun t => by
    rw [mem_ball, dist_zero_right, not_lt]
  unfold StoppedPoleReconstruction.exitTime
  split_ifs with h
  · refine le_antisymm (zero_le) ?_
    have h0 : pathExitTime (ball (0 : ℂ) r) β ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by
      unfold pathExitTime
      exact sInf_le ⟨0, rfl, (hmem 0).2 h⟩
    simpa using h0
  · refine le_antisymm ?_ ?_
    · unfold pathExitTime
      refine le_sInf ?_
      rintro _ ⟨t, rfl, ht⟩
      exact iInf₂_le t ((hmem t).1 ht)
    · refine le_iInf₂ fun t ht => ?_
      unfold pathExitTime
      exact sInf_le ⟨t, rfl, (hmem t).2 ht⟩

section Extension

variable {T₁ T₂ : ℝ≥0}

/-- The point `min t T₁` of `[0, T₁]`. -/
def clipIcc (T₁ : ℝ≥0) (t : ℝ≥0) : Icc (0 : ℝ≥0) T₁ :=
  ⟨min t T₁, zero_le, min_le_right _ _⟩

/-- An increasing homeomorphism `φ : [0, T₁] → [0, T₂]` continued after `T₁` by the shift `t ↦ T₂ + (t - T₁)`. -/
noncomputable def extendIccFun (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) : ℝ≥0 :=
  (φ (clipIcc T₁ t) : ℝ≥0) + (t - T₁)

/-- An order isomorphism of `[0, T₁]` onto `[0, T₂]` sends `T₁` to `T₂`. -/
theorem orderIso_Icc_right (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) :
    (φ ⟨T₁, zero_le, le_rfl⟩ : ℝ≥0) = T₂ := by
  obtain ⟨x, hx⟩ := φ.surjective ⟨T₂, zero_le, le_rfl⟩
  refine le_antisymm (φ ⟨T₁, zero_le, le_rfl⟩).2.2 ?_
  have hle : φ x ≤ φ ⟨T₁, zero_le, le_rfl⟩ := φ.monotone (show x ≤ ⟨T₁, zero_le, le_rfl⟩ from x.2.2)
  rw [hx] at hle
  exact hle

theorem orderIso_clipIcc_of_le (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) {t : ℝ≥0} (ht : T₁ ≤ t) :
    (φ (clipIcc T₁ t) : ℝ≥0) = T₂ := by
  have hc : clipIcc T₁ t = ⟨T₁, zero_le, le_rfl⟩ := Subtype.ext (min_eq_right ht)
  rw [hc, orderIso_Icc_right]

theorem extendIccFun_strictMono (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) : StrictMono (extendIccFun φ) := by
  have hg : Monotone fun t : ℝ≥0 => (φ (clipIcc T₁ t) : ℝ≥0) := fun t t' htt' =>
    φ.monotone (show clipIcc T₁ t ≤ clipIcc T₁ t' from min_le_min htt' le_rfl)
  intro t t' htt'
  rcases le_or_gt t' T₁ with h' | h'
  · have ht : t ≤ T₁ := htt'.le.trans h'
    have hlt : clipIcc T₁ t < clipIcc T₁ t' := by
      show min t T₁ < min t' T₁
      rw [min_eq_left ht, min_eq_left h']
      exact htt'
    have h1 : (φ (clipIcc T₁ t) : ℝ≥0) < φ (clipIcc T₁ t') := φ.strictMono hlt
    simp only [extendIccFun, tsub_eq_zero_of_le ht, tsub_eq_zero_of_le h', add_zero]
    exact h1
  · have h1 : t - T₁ < t' - T₁ := by
      rcases le_total T₁ t with ht | ht
      · exact tsub_lt_tsub_right_of_le ht htt'
      · rw [tsub_eq_zero_of_le ht]
        exact tsub_pos_of_lt h'
    exact add_lt_add_of_le_of_lt (hg htt'.le) h1

theorem extendIccFun_surjective (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) :
    Function.Surjective (extendIccFun φ) := by
  intro y
  rcases le_or_gt y T₂ with hy | hy
  · obtain ⟨x, hx⟩ := φ.surjective ⟨y, zero_le, hy⟩
    refine ⟨x.1, ?_⟩
    have hc : clipIcc T₁ x.1 = x := Subtype.ext (min_eq_left x.2.2)
    rw [extendIccFun, hc, tsub_eq_zero_of_le x.2.2, add_zero, hx]
  · refine ⟨T₁ + (y - T₂), ?_⟩
    simp only [extendIccFun, orderIso_clipIcc_of_le φ (le_self_add : T₁ ≤ T₁ + (y - T₂)), add_tsub_cancel_left]
    exact add_tsub_cancel_of_le hy.le

/-- The extension `extendIccFun φ` as an order isomorphism of `[0, ∞)`. -/
noncomputable def extendIccOrderIso (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (extendIccFun φ) (extendIccFun_strictMono φ) (extendIccFun_surjective φ)

theorem extendIccOrderIso_apply (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) :
    extendIccOrderIso φ t = extendIccFun φ t := rfl

/-- After the extension, clipping at `T₂` is the image of the clip at `T₁`. -/
theorem min_extendIccFun (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) :
    min (extendIccFun φ t) T₂ = (φ (clipIcc T₁ t) : ℝ≥0) := by
  rcases le_total t T₁ with ht | ht
  · simp only [extendIccFun, tsub_eq_zero_of_le ht, add_zero]
    exact min_eq_left (φ (clipIcc T₁ t)).2.2
  · rw [orderIso_clipIcc_of_le φ ht]
    exact min_eq_right (by simp only [extendIccFun, orderIso_clipIcc_of_le φ ht]; exact le_self_add)

end Extension

open scoped Classical in
/-- The distance modulo parametrization of two curves stopped at their exit times from `U` is at most the metric
`d_CMP` of (1.7) between their restrictions to the exit-time intervals. -/
theorem cmpEDist_stopAtExit_le_dCMP (U : Set ℂ) (β₁ β₂ : ℝ≥0 → ℂ) :
    cmpEDist (stopAtExit U β₁) (stopAtExit U β₂) ≤
      StoppedPoleReconstruction.dCMP β₁ β₂ (pathExitTime U β₁) (pathExitTime U β₂) := by
  unfold StoppedPoleReconstruction.dCMP
  split_ifs with hT
  · exact le_top
  obtain ⟨h₁, h₂⟩ := not_or.1 hT
  refine le_iInf fun φ => ?_
  refine iInf_le_of_le (extendIccOrderIso φ) (iSup_le fun t => ?_)
  have hs₁ : stopAtExit U β₁ t = β₁ (clipIcc (pathExitTime U β₁).toNNReal t) := by
    simp [stopAtExit, h₁, clipIcc]
  have hs₂ : stopAtExit U β₂ (extendIccOrderIso φ t) = β₂ (φ (clipIcc (pathExitTime U β₁).toNNReal t)) := by
    simp only [stopAtExit, h₂, ite_false, extendIccOrderIso_apply, min_extendIccFun]
  rw [hs₁, hs₂, edist_dist, dist_eq_norm]
  exact le_iSup (fun x : Icc (0 : ℝ≥0) (pathExitTime U β₁).toNNReal => ENNReal.ofReal ‖β₁ x.1 - β₂ (φ x).1‖)
    (clipIcc (pathExitTime U β₁).toNNReal t)

/-- **Radius pick.** If `d^loc_CMP(β₁, β₂) < e^{-b} s (b - a)` with `0 ≤ a < b` and `0 ≤ s ≤ 1`, then some radius
`r ∈ (a, b)` has `d_CMP(β₁|[0,T_{β₁,r}], β₂|[0,T_{β₂,r}]) < s`. -/
theorem exists_dCMP_lt_of_dLoc_lt {β₁ β₂ : ℝ≥0 → ℂ} {a b s : ℝ} (ha : 0 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : StoppedPoleReconstruction.dLoc β₁ β₂ < ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, StoppedPoleReconstruction.dCMP β₁ β₂ (StoppedPoleReconstruction.exitTime β₁ r)
      (StoppedPoleReconstruction.exitTime β₂ r) < ENNReal.ofReal s := by
  by_contra hcon
  have hge : ∀ r ∈ Ioo a b, ENNReal.ofReal s ≤ StoppedPoleReconstruction.dCMP β₁ β₂
      (StoppedPoleReconstruction.exitTime β₁ r) (StoppedPoleReconstruction.exitTime β₂ r) :=
    fun r hr => not_lt.1 fun hlt => hcon ⟨r, hr, hlt⟩
  have hes : 0 ≤ Real.exp (-b) * s := mul_nonneg (Real.exp_pos _).le hs0
  refine (not_le.2 h) ?_
  unfold StoppedPoleReconstruction.dLoc
  calc ENNReal.ofReal (Real.exp (-b) * s * (b - a))
      = ENNReal.ofReal (Real.exp (-b) * s) * volume (Ioo a b) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hes]
    _ = ∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.exp (-b) * s) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal (Real.exp (-r)) * min 1 (StoppedPoleReconstruction.dCMP β₁ β₂
          (StoppedPoleReconstruction.exitTime β₁ r) (StoppedPoleReconstruction.exitTime β₂ r)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hr.2]))) ?_
        exact le_min (ENNReal.ofReal_le_one.2 hs1) (hge r hr)
    _ ≤ _ := lintegral_mono_set fun r hr => lt_of_le_of_lt ha hr.1

/-- **Small local metric gives a disc with close stopped curves.** If `d^loc_CMP(β₁, β₂) < e^{-b} s (b - a)` with
`0 ≤ a < b` and `0 ≤ s ≤ 1`, then for some `r ∈ (a, b)` the curves stopped at their exit from `B_r(0)` are within
`s` modulo parametrization. -/
theorem exists_cmpEDist_stopAtExit_lt_of_dLoc_lt {β₁ β₂ : ℝ≥0 → ℂ} {a b s : ℝ} (ha : 0 ≤ a) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (h : StoppedPoleReconstruction.dLoc β₁ β₂ < ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, cmpEDist (stopAtExit (ball (0 : ℂ) r) β₁) (stopAtExit (ball (0 : ℂ) r) β₂) <
      ENNReal.ofReal s := by
  obtain ⟨r, hr, hlt⟩ := exists_dCMP_lt_of_dLoc_lt ha hs0 hs1 h
  refine ⟨r, hr, lt_of_le_of_lt ?_ hlt⟩
  rw [exitTime_eq_pathExitTime, exitTime_eq_pathExitTime]
  exact cmpEDist_stopAtExit_le_dCMP _ _ _

end MatedCRT.LocalCurveMetricPick
