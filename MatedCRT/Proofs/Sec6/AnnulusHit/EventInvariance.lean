import MatedCRT.Proofs.Sec6.AnnulusHit.Geometry

/-!
# Deterministic invariances of the good annulus event (proof of Lemma 6.5, lines 2343-2368)

The good annulus event `E_r(z; C)` of eq:good-annulus-event (with the scale-invariant integrand of CORRECTION [C5]) is
a deterministic property of the measure. The proof of Lemma 6.5 uses three of its invariances:

* `isGoodAnnulusEvent_smul_iff`: multiplying the measure by a constant `c ∈ (0, ∞)` does not change whether `E_r(z)`
  occurs (Weyl scaling by additive constants, line 2367 and line 2389);
* `isGoodAnnulusEvent_map_iff`: `E_r(z)` for `μ` is `E_1(0)` for the image of `μ` under the affine chart
  `x ↦ (x - z)/r` (the LQG coordinate change, line 2367);
* `isGoodAnnulusEvent_withDensity_norm_rpow`: replacing `μ` by `|x|^{-t} μ` on an admissible region of dependence
  turns `E_r(z; C)` into `E_r(z; 601^{2t} C)` (Step 1, the log singularity `-γ log |·|` of the cone field, with
  `t = γ²`, lines 2353-2363).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- `E_r(z; C)` is monotone in the constant `C`. -/
theorem IsGoodAnnulusEvent.mono_const {μ : Measure ℂ} {c₀ C C' r : ℝ} {z : ℂ} (hCC : C ≤ C')
    (h : IsGoodAnnulusEvent μ c₀ C r z) : IsGoodAnnulusEvent μ c₀ C' r z := by
  unfold IsGoodAnnulusEvent at h ⊢
  exact h.trans (by gcongr)

/-- Cancellation of a factor `a ∈ (0, ∞)` in `[0, ∞]`. -/
theorem ennreal_le_of_mul_le_mul_left {a b c : ℝ≥0∞} (h0 : a ≠ 0) (ht : a ≠ ∞) (h : a * b ≤ a * c) :
    b ≤ c := by
  calc b = a⁻¹ * (a * b) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ a⁻¹ * (a * c) := by gcongr a⁻¹ * ?_
    _ = c := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- **Constant multiples.** For `c ∈ (0, ∞)`, `E_r(z)` occurs for `c μ` iff it occurs for `μ`. -/
theorem isGoodAnnulusEvent_smul_iff {μ : Measure ℂ} {c₀ C r : ℝ} {z : ℂ} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) : IsGoodAnnulusEvent (c • μ) c₀ C r z ↔ IsGoodAnnulusEvent μ c₀ C r z := by
  unfold IsGoodAnnulusEvent
  have hL : (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(c • μ)) =
      c * ⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂μ := by
    simp only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ENNReal.mul_iSup]
  have hR : (⨅ w ∈ annulus z r (2 * r), (c • μ) (ball w (c₀ * r))) =
      c * ⨅ w ∈ annulus z r (2 * r), μ (ball w (c₀ * r)) := by
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.mul_iInf_of_ne hc0 hc]
  rw [hL, hR, mul_left_comm]
  exact ⟨ennreal_le_of_mul_le_mul_left hc0 hc, fun h => by gcongr⟩

/-- The affine chart `x ↦ (x - z)/r` of `ℂ`, sending `𝔸_{r,2r}(z)` to `𝔸_{1,2}(0)`, as a measurable equivalence. -/
noncomputable def annulusChart (z : ℂ) (r : ℝ) (hr : r ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun x := (x - z) / r
  invFun y := r * y + z
  left_inv x := by
    have h : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
    show (r : ℂ) * ((x - z) / r) + z = x
    rw [mul_div_assoc', mul_div_cancel_left₀ (x - z) h, sub_add_cancel]
  right_inv y := by
    have h : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
    show ((r : ℂ) * y + z - z) / r = y
    rw [add_sub_cancel_right, mul_div_cancel_left₀ y h]
  measurable_toFun := ((continuous_id.sub continuous_const).div_const (r : ℂ)).measurable
  measurable_invFun := ((continuous_const.mul continuous_id).add continuous_const).measurable

/-- **Affine coordinate change.** `E_r(z; C)` occurs for `μ` iff `E_1(0; C)` occurs for the image of `μ` under
`x ↦ (x - z)/r`; this uses the scale-invariant integrand `log (r/|u - v|) + 1` of CORRECTION [C5]. -/
theorem isGoodAnnulusEvent_map_iff {μ : Measure ℂ} {c₀ C r : ℝ} {z : ℂ} (hr : 0 < r) :
    IsGoodAnnulusEvent μ c₀ C r z ↔
      IsGoodAnnulusEvent (μ.map fun x => (x - z) / (r : ℂ)) c₀ C 1 0 := by
  set T := annulusChart z r hr.ne'
  have hTfun : (fun x : ℂ => (x - z) / (r : ℂ)) = ⇑T := rfl
  have hT : ∀ x, T x = (x - z) / r := fun x => rfl
  have hnorm : ∀ x y, ‖T x - T y‖ = ‖x - y‖ / r := by
    intro x y
    rw [hT, hT, ← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  have hmemA : ∀ v, T v ∈ annulus 0 1 (2 * 1) ↔ v ∈ annulus z r (2 * r) := by
    intro v
    rw [mem_annulus_iff_norm, mem_annulus_iff_norm, hT, sub_zero, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, lt_div_iff₀ hr, div_lt_iff₀ hr]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hpreA : T ⁻¹' annulus 0 1 (2 * 1) = annulus z r (2 * r) := Set.ext hmemA
  have hpreB : ∀ w, T ⁻¹' ball (T w) (c₀ * 1) = ball w (c₀ * r) := by
    intro w
    ext x
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hnorm, div_lt_iff₀ hr, mul_one]
  have hI : ∀ v, ∫⁻ u in annulus 0 1 (2 * 1), ENNReal.ofReal (Real.log (1 / ‖u - T v‖) + 1) ∂(μ.map T) =
      ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂μ := by
    intro v
    rw [T.restrict_map, T.measurableEmbedding.lintegral_map, hpreA]
    refine lintegral_congr fun u => ?_
    rw [hnorm u v, one_div_div]
  have hB : ∀ w, (μ.map T) (ball (T w) (c₀ * 1)) = μ (ball w (c₀ * r)) := by
    intro w
    rw [T.map_apply, hpreB]
  have hL : (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
        ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂(μ.map T)) =
      ⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂μ := by
    refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun v hv => ?_)
    · obtain ⟨v', rfl⟩ := T.surjective v
      rw [hI v']
      exact le_iSup₂_of_le v' ((hmemA v').1 hv) le_rfl
    · rw [← hI v]
      exact le_iSup₂_of_le (T v) ((hmemA v).2 hv) le_rfl
  have hR : (⨅ w ∈ annulus 0 1 (2 * 1), (μ.map T) (ball w (c₀ * 1))) =
      ⨅ w ∈ annulus z r (2 * r), μ (ball w (c₀ * r)) := by
    refine le_antisymm (le_iInf₂ fun w hw => ?_) (le_iInf₂ fun w hw => ?_)
    · rw [← hB w]
      exact iInf₂_le_of_le (T w) ((hmemA w).2 hw) le_rfl
    · obtain ⟨w', rfl⟩ := T.surjective w
      rw [hB w']
      exact iInf₂_le_of_le w' ((hmemA w').1 hw) le_rfl
  unfold IsGoodAnnulusEvent
  rw [hTfun, hL, hR]

/-- **Comparison of measures on the region of dependence.** If `ν' ≤ M ν` and `m ν ≤ ν'` on `𝔸_{r/3,3r}(z)` and
`M ≤ A m`, then `E_r(z; C)` for `ν` implies `E_r(z; A C)` for `ν'`. -/
theorem isGoodAnnulusEvent_of_restrict_le {ν ν' : Measure ℂ} {c₀ C r A m M : ℝ} {z : ℂ}
    (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (hC : 0 ≤ C) (hm : 0 ≤ m) (hMA : M ≤ A * m)
    (hup : ν'.restrict (annulus z (r / 3) (3 * r)) ≤
      ENNReal.ofReal M • ν.restrict (annulus z (r / 3) (3 * r)))
    (hlow : ENNReal.ofReal m • ν.restrict (annulus z (r / 3) (3 * r)) ≤
      ν'.restrict (annulus z (r / 3) (3 * r)))
    (hE : IsGoodAnnulusEvent ν c₀ C r z) : IsGoodAnnulusEvent ν' c₀ (A * C) r z := by
  unfold IsGoodAnnulusEvent at hE ⊢
  have hA0 : annulus z r (2 * r) ⊆ annulus z (r / 3) (3 * r) := annulus_subset_region hr
  have hint : ∀ v, ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν' ≤
      ENNReal.ofReal M * ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν := by
    intro v
    have hle : ν'.restrict (annulus z r (2 * r)) ≤ ENNReal.ofReal M • ν.restrict (annulus z r (2 * r)) := by
      rw [← Measure.restrict_restrict_of_subset (μ := ν') hA0,
        ← Measure.restrict_restrict_of_subset (μ := ν) hA0, ← Measure.restrict_smul]
      exact Measure.restrict_mono subset_rfl hup
    calc ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν'
        ≤ ∫⁻ u, ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(ENNReal.ofReal M • ν.restrict (annulus z r (2 * r))) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal M * ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν := by
          simp only [lintegral_smul_measure, smul_eq_mul]
  have hball : ENNReal.ofReal m * ⨅ w ∈ annulus z r (2 * r), ν (ball w (c₀ * r)) ≤
      ⨅ w ∈ annulus z r (2 * r), ν' (ball w (c₀ * r)) := by
    refine le_iInf₂ fun w hw => ?_
    have hsub := ball_subset_region hr hc₀ hw
    have h := Measure.le_iff'.1 hlow (ball w (c₀ * r))
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_eq_self (μ := ν) hsub,
      Measure.restrict_eq_self (μ := ν') hsub] at h
    refine le_trans ?_ h
    gcongr ENNReal.ofReal m * ?_
    exact iInf₂_le w hw
  calc (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν')
      ≤ ⨆ v ∈ annulus z r (2 * r), ENNReal.ofReal M * ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν := iSup₂_mono fun v _ => hint v
    _ = ENNReal.ofReal M * ⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν := by simp only [ENNReal.mul_iSup]
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C * ⨅ w ∈ annulus z r (2 * r), ν (ball w (c₀ * r))) := by
        gcongr ENNReal.ofReal M * ?_
    _ = ENNReal.ofReal (M * C) * ⨅ w ∈ annulus z r (2 * r), ν (ball w (c₀ * r)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul' hC]
    _ ≤ ENNReal.ofReal (A * C * m) * ⨅ w ∈ annulus z r (2 * r), ν (ball w (c₀ * r)) := by
        gcongr ENNReal.ofReal ?_ * _
        nlinarith [mul_le_mul_of_nonneg_right hMA hC]
    _ = ENNReal.ofReal (A * C) * (ENNReal.ofReal m * ⨅ w ∈ annulus z r (2 * r), ν (ball w (c₀ * r))) := by
        rw [ENNReal.ofReal_mul' hm, mul_assoc]
    _ ≤ ENNReal.ofReal (A * C) * ⨅ w ∈ annulus z r (2 * r), ν' (ball w (c₀ * r)) := by
        gcongr ENNReal.ofReal (A * C) * ?_

/-- A density bounded above by `M` on a measurable set `s` gives `ν'|_s ≤ M ν|_s`. -/
theorem withDensity_restrict_le_smul {ν : Measure ℂ} {g : ℂ → ℝ} {s : Set ℂ} {M : ℝ}
    (hs : MeasurableSet s) (hg : ∀ x ∈ s, g x ≤ M) :
    (ν.withDensity fun x => ENNReal.ofReal (g x)).restrict s ≤ ENNReal.ofReal M • ν.restrict s := by
  refine Measure.le_iff.2 fun t ht => ?_
  rw [Measure.restrict_apply ht, withDensity_apply _ (ht.inter hs), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply ht, ← setLIntegral_const (t ∩ s) (ENNReal.ofReal M)]
  exact setLIntegral_mono' (ht.inter hs) fun x hx => ENNReal.ofReal_le_ofReal (hg x hx.2)

/-- A density bounded below by `m` on a measurable set `s` gives `m ν|_s ≤ ν'|_s`. -/
theorem smul_restrict_le_withDensity_restrict {ν : Measure ℂ} {g : ℂ → ℝ} {s : Set ℂ} {m : ℝ}
    (hs : MeasurableSet s) (hg : ∀ x ∈ s, m ≤ g x) :
    ENNReal.ofReal m • ν.restrict s ≤ (ν.withDensity fun x => ENNReal.ofReal (g x)).restrict s := by
  refine Measure.le_iff.2 fun t ht => ?_
  rw [Measure.restrict_apply ht, withDensity_apply _ (ht.inter hs), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply ht, ← setLIntegral_const (t ∩ s) (ENNReal.ofReal m)]
  exact setLIntegral_mono' (ht.inter hs) fun x hx => ENNReal.ofReal_le_ofReal (hg x hx.2)

/-- `y^{-t} ≤ x^{-t}` for `0 < x ≤ y` and `t ≥ 0`. -/
theorem rpow_neg_le_rpow_neg {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y) (ht : 0 ≤ t) :
    y ^ (-t) ≤ x ^ (-t) := by
  rw [Real.rpow_neg (hx.le.trans hxy), Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx t) (Real.rpow_le_rpow hx.le hxy ht)

/-- **Weyl scaling by `|x|^{-t}` on an admissible region** (Step 1 of the proof of Lemma 6.5, lines 2353-2363). If
`dist(𝔸_{r/3,3r}(z), 0) ≥ r/100`, then `E_r(z; C)` for `ν` implies `E_r(z; 601^{2t} C)` for `|x|^{-t} ν`. -/
theorem isGoodAnnulusEvent_withDensity_norm_rpow {ν : Measure ℂ} {c₀ C r t : ℝ} {z : ℂ}
    (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r))) (hE : IsGoodAnnulusEvent ν c₀ C r z) :
    IsGoodAnnulusEvent (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-t))) c₀
      (((601 : ℝ) ^ t) ^ 2 * C) r z := by
  have hy₀ := add_mem_region (z := z) hr
  have ha : r / 100 ≤ ‖z + (r : ℂ)‖ := (norm_le_mul_norm_of_mem_region hdist hy₀ hy₀).2
  have ha0 : 0 < ‖z + (r : ℂ)‖ := by linarith
  have hbounds : ∀ x ∈ annulus z (r / 3) (3 * r),
      ‖z + (r : ℂ)‖ / 601 ≤ ‖x‖ ∧ ‖x‖ ≤ 601 * ‖z + (r : ℂ)‖ := by
    intro x hx
    have h1 := (norm_le_mul_norm_of_mem_region hdist hx hy₀).1
    have h2 := (norm_le_mul_norm_of_mem_region hdist hy₀ hx).1
    refine ⟨?_, h1⟩
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have h601 : (0 : ℝ) < 601 ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hat : 0 < ‖z + (r : ℂ)‖ ^ t := Real.rpow_pos_of_pos ha0 t
  have h601' : (601 : ℝ) ^ t ≠ 0 := h601.ne'
  have hat' : ‖z + (r : ℂ)‖ ^ t ≠ 0 := hat.ne'
  refine isGoodAnnulusEvent_of_restrict_le (m := (601 * ‖z + (r : ℂ)‖) ^ (-t))
    (M := (‖z + (r : ℂ)‖ / 601) ^ (-t)) hr hc₀ hC (Real.rpow_nonneg (by positivity) _) ?_ ?_ ?_ hE
  · have e1 : (‖z + (r : ℂ)‖ / 601) ^ (-t) = ((‖z + (r : ℂ)‖ / 601) ^ t)⁻¹ :=
      Real.rpow_neg (by positivity) t
    have e2 : (601 * ‖z + (r : ℂ)‖) ^ (-t) = ((601 * ‖z + (r : ℂ)‖) ^ t)⁻¹ :=
      Real.rpow_neg (by positivity) t
    rw [e1, e2, Real.div_rpow ha0.le (by norm_num : (0 : ℝ) ≤ 601),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 601) ha0.le]
    apply le_of_eq
    field_simp
  · exact withDensity_restrict_le_smul (measurableSet_annulus' z (r / 3) (3 * r)) fun x hx =>
      rpow_neg_le_rpow_neg (div_pos ha0 (by norm_num)) (hbounds x hx).1 ht
  · refine smul_restrict_le_withDensity_restrict (measurableSet_annulus' z (r / 3) (3 * r)) fun x hx => ?_
    have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (div_pos ha0 (by norm_num)) (hbounds x hx).1
    exact rpow_neg_le_rpow_neg hx0 (hbounds x hx).2 ht

end MatedCRT
