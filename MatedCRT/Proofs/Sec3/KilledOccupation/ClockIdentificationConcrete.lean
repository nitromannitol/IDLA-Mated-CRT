import Mathlib
import MarkovProcess.Path.Basic
import HarmonicBalls.Defs.GFF
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentification
import MatedCRT.Proofs.Sec3.KilledOccupation.OriginTails

/-!
# Concrete identification of the regularized clock (Appendix B, step S6)

Source: `paper/appendix-occupation-C16.tex`, proof of Theorem thm:occ-main, "Identification of the clock
of the main text" (lines 370-425), with the regularized density identity eq:occ-regweight (lines 313-315).

Notation. `hc ω r z` are the circle averages of the whole-plane GFF (as in `OriginTails.lean`);
`regDensity γ ε (hc ω) x = ε^{γ²/2} e^{γ h_ε(x)}` (tex:296); `nuDensity γ ε (hc ω) x = ε^{γ²/2} e^{γ g_ε(x)}`
(the density of `ν_ε`, tex:127-129). The regularized clock `φ_ε` (eq:occ-clock, tex:38-39) is `regClock`; the
weighted clock `Φ` (tex:275) is `weightedClock` (`WeightedClock.lean`). Time is `timeLeb` (Lebesgue on `[0,∞)`).

Proved here:
* `regDensity_eq_weight`: `μ_ε(dx) = (|x| ∨ ε)^{-γ²} ν_ε(dx)` (eq:occ-regweight, tex:313-314), from the circle
  average `circleAverage (log ‖· - 0‖) x ε = log (|x| ∨ ε)` (Mathlib, `PosLogEqCircleAverage`);
* the pathwise splitting `φ_ε = (χ_a-part) + (removed part)` and `Φ = (χ_a-part) + (removed part)` (tex:370-405),
  the removed parts being bounded by `R_{ε,a}` and by `removedWeightedClock`; the `χ_a`-part of `φ_ε` is the clock
  form `cutApproxClock` for `0 < ε < a` (tex:373-374);
* `regClock_identification`: `sup_s |φ_ε - Φ| → 0` in probability (tex:413-414). Its inputs `hE` (tex:377-385) and
  `hR` (tex:386-400) are explicit hypotheses (see the docstring); `hQ` (tex:402-405) and the pathwise
  splitting are proved.

The distance on `ℝ≥0∞` is `ennDist a b = (a - b) + (b - a)` (equal to `|a - b|`; Mathlib gives no `EMetric` here).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The distance `|a - b| = (a - b) + (b - a)` on `ℝ≥0∞`. -/
def ennDist (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) + (b - a)

lemma tsub_add_tsub_le' (x y z w : ℝ≥0∞) : x + y - (z + w) ≤ (x - z) + (y - w) := by
  rw [tsub_le_iff_right]
  have h1 : x ≤ (x - z) + z := tsub_le_iff_right.1 le_rfl
  have h2 : y ≤ (y - w) + w := tsub_le_iff_right.1 le_rfl
  calc x + y ≤ ((x - z) + z) + ((y - w) + w) := add_le_add h1 h2
    _ = (x - z) + (y - w) + (z + w) := by ring

lemma ennDist_add_add_le (c₁ c₂ r q : ℝ≥0∞) :
    ennDist (c₁ + r) (c₂ + q) ≤ ennDist c₁ c₂ + (r + q) := by
  unfold ennDist
  calc (c₁ + r - (c₂ + q)) + (c₂ + q - (c₁ + r))
      ≤ ((c₁ - c₂) + (r - q)) + ((c₂ - c₁) + (q - r)) :=
        add_le_add (tsub_add_tsub_le' _ _ _ _) (tsub_add_tsub_le' _ _ _ _)
    _ = ((c₁ - c₂) + (c₂ - c₁)) + ((r - q) + (q - r)) := by ring
    _ ≤ ((c₁ - c₂) + (c₂ - c₁)) + (r + q) :=
        add_le_add le_rfl (add_le_add tsub_le_self tsub_le_self)

/-- The density `ν_ε(x) = ε^{γ²/2} e^{γ g_ε(x)}` of the nonsingular circle-average clock (tex:127-129); here
`g_ε = hc ε` is the circle average of the whole-plane GFF. -/
def nuDensity (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ε x))

/-- The cutoff `χ_a` of tex:370-372, with values in `[0,1]`: `0` on `‖x‖ ≤ a` and `1` on `‖x‖ ≥ 2a`. -/
def cutoffWeight (a : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (max 0 (‖x‖ / a - 1)))

lemma measurable_cutoffWeight (a : ℝ) : Measurable (cutoffWeight a) := by
  unfold cutoffWeight
  exact (ENNReal.continuous_ofReal.comp
    (by fun_prop : Continuous fun x : ℂ => min 1 (max 0 (‖x‖ / a - 1)))).measurable

lemma cutoffWeight_le_one (a : ℝ) (x : ℂ) : cutoffWeight a x ≤ 1 := by
  unfold cutoffWeight
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

lemma cutoffWeight_eq_zero {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ‖x‖ ≤ a) :
    cutoffWeight a x = 0 := by
  have h1 : ‖x‖ / a - 1 ≤ 0 := by
    have := (div_le_one ha).2 hx
    linarith
  unfold cutoffWeight
  rw [max_eq_left h1, min_eq_right zero_le_one, ENNReal.ofReal_zero]

lemma cutoffWeight_eq_one {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : 2 * a ≤ ‖x‖) :
    cutoffWeight a x = 1 := by
  have h2 : 2 ≤ ‖x‖ / a := by
    rw [le_div_iff₀ ha]
    linarith
  have h1 : 1 ≤ ‖x‖ / a - 1 := by linarith
  have h0 : 0 ≤ ‖x‖ / a - 1 := by linarith
  unfold cutoffWeight
  rw [max_eq_right h0, min_eq_left h1, ENNReal.ofReal_one]

/-- The circle average of `log ‖·‖` over the circle of radius `ε` centred at `x` is `log (max ‖x‖ ε)`
(Mathlib's `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). -/
lemma circleAverage_log_norm_eq {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y‖) x ε = Real.log (max ‖x‖ ε) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := x) (R := ε)
    hε.ne'
  simp only [sub_zero] at h
  rw [h]
  unfold Real.posLog
  rcases le_total ‖x‖ ε with hx | hx
  · rw [max_eq_right hx]
    have hle : ε⁻¹ * ‖x‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hε]
      linarith
    rw [max_eq_left (Real.log_nonpos (by positivity) hle), add_zero]
  · rw [max_eq_left hx]
    have h1 : 1 ≤ ε⁻¹ * ‖x‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hε]
      linarith
    rw [max_eq_right (Real.log_nonneg h1), ← Real.log_mul hε.ne' (by positivity)]
    congr 1
    field_simp

/-- `h_ε(x) = hc ε x - γ log (max ‖x‖ ε)`: the circle average of the cone field `h = h^ℂ - γ log|·|`. -/
lemma fieldCircleAverage_eq_log (γ : ℝ) {ε : ℝ} (hc : ℝ → ℂ → ℝ) (hε : 0 < ε) (x : ℂ) :
    HarmonicBalls.fieldCircleAverage γ hc ε x = hc ε x - γ * Real.log (max ‖x‖ ε) := by
  unfold HarmonicBalls.fieldCircleAverage
  rw [circleAverage_log_norm_eq hε x]

/-- **eq:occ-regweight** (tex:313-314): `μ_ε(dx) = (|x| ∨ ε)^{-γ²} ν_ε(dx)`, pointwise in `x`
(the circle mean-value formula, including at `x = 0`). -/
lemma regDensity_eq_weight {γ ε : ℝ} (hc : ℝ → ℂ → ℝ) (hε : 0 < ε) (x : ℂ) :
    regDensity γ ε hc x = ENNReal.ofReal ((max ‖x‖ ε) ^ (-(γ ^ 2))) * nuDensity γ ε hc x := by
  have hm : 0 < max ‖x‖ ε := lt_max_of_lt_right hε
  unfold regDensity nuDensity
  rw [fieldCircleAverage_eq_log γ hc hε x, ← ENNReal.ofReal_mul (Real.rpow_nonneg hm.le _)]
  congr 1
  rw [Real.rpow_def_of_pos hm, show γ * (hc ε x - γ * Real.log (max ‖x‖ ε))
      = γ * hc ε x + Real.log (max ‖x‖ ε) * (-(γ ^ 2)) by ring, Real.exp_add]
  ring

/-- Lebesgue measure on the time half-line `[0, ∞)`, as a measure on `ℝ≥0` (the push-forward of
`volume.restrict (Ici 0)` under `Real.toNNReal`; Mathlib has no `MeasureSpace ℝ≥0` instance). -/
def timeLeb : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Ici (0 : ℝ)))

/-- The regularized clock `φ_ε(s) = ∫_0^{s∧σ} ε^{γ²/2} e^{γ h_ε(B_u)} du` (eq:occ-clock, tex:38-39). -/
def regClock (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (min s σ), regDensity γ ε hc (B u) ∂timeLeb

/-- The `χ_a`-part of `φ_ε` in the clock form of the printed display (tex:373-376): the integral of
`χ_a(B_u) |B_u|^{-γ²}` against the approximating clock `dA_ε(du) = ν_ε(B_u) du`. -/
def cutApproxClock (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (a : ℝ) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (min s σ), cutoffWeight a (B u) * gammaWeight γ (B u)
    ∂(timeLeb.withDensity fun v => nuDensity γ ε hc (B v))

/-- The `χ_a`-part of `Φ`: `∫_0^{s∧σ} χ_a(B_u) |B_u|^{-γ²} dA(u)` (tex:370-376). -/
def cutWeightedClock (γ : ℝ) (dA : Measure ℝ≥0) (a : ℝ) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (min s σ), cutoffWeight a (B u) * gammaWeight γ (B u) ∂dA

/-- For `0 < ε < a`, the `χ_a`-part of `φ_ε` equals the printed clock form (tex:373-374): on the support of `χ_a`
one has `|x| ≥ a > ε`, so `μ_ε(dx) = |x|^{-γ²} ν_ε(dx)` there (eq:occ-regweight). -/
lemma cut_regDensity_eq {γ ε a : ℝ} (hc : ℝ → ℂ → ℝ) (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hν : Measurable (nuDensity γ ε hc)) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (hB : Continuous B) (s : ℝ≥0) :
    ∫⁻ u in Icc 0 (min s σ), cutoffWeight a (B u) * regDensity γ ε hc (B u) ∂timeLeb =
      cutApproxClock γ ε hc a σ B s := by
  have hpt : ∀ u, cutoffWeight a (B u) * regDensity γ ε hc (B u) =
      cutoffWeight a (B u) * gammaWeight γ (B u) * nuDensity γ ε hc (B u) := by
    intro u
    by_cases hB' : ‖B u‖ ≤ a
    · rw [cutoffWeight_eq_zero ha hB']
      simp
    · rw [not_le] at hB'
      have hmax : max ‖B u‖ ε = ‖B u‖ := max_eq_left (by linarith)
      rw [regDensity_eq_weight hc hε, hmax]
      unfold gammaWeight
      ring
  have hint : Measurable fun u => cutoffWeight a (B u) * gammaWeight γ (B u) :=
    ((measurable_cutoffWeight a).comp hB.measurable).mul ((measurable_gammaWeight γ).comp hB.measurable)
  have hdens : Measurable fun v => nuDensity γ ε hc (B v) := hν.comp hB.measurable
  unfold cutApproxClock
  rw [MeasureTheory.restrict_withDensity measurableSet_Icc,
    lintegral_withDensity_eq_lintegral_mul _ hdens hint]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply]
  rw [hpt u]
  ring

/-- Splitting of the regularized clock at the cutoff `χ_a` (tex:370-372):
`φ_ε(s) = (χ_a-part) + ∫_0^{s∧σ} (1 - χ_a(B_u)) μ_ε(dB_u)`. -/
lemma regClock_eq_cut_add {γ ε : ℝ} (hc : ℝ → ℂ → ℝ) (a : ℝ) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (hB : Continuous B)
    (hreg : Measurable (regDensity γ ε hc)) (s : ℝ≥0) :
    regClock γ ε hc σ B s =
      (∫⁻ u in Icc 0 (min s σ), cutoffWeight a (B u) * regDensity γ ε hc (B u) ∂timeLeb) +
        ∫⁻ u in Icc 0 (min s σ), (1 - cutoffWeight a (B u)) * regDensity γ ε hc (B u) ∂timeLeb := by
  have hf : Measurable fun u => cutoffWeight a (B u) * regDensity γ ε hc (B u) :=
    ((measurable_cutoffWeight a).comp hB.measurable).mul (hreg.comp hB.measurable)
  unfold regClock
  rw [← lintegral_add_left hf]
  refine lintegral_congr fun u => ?_
  rw [← add_mul, add_tsub_cancel_of_le (cutoffWeight_le_one a _), one_mul]

/-- The splitting of `Φ` at the cutoff `χ_a`: `Φ(s) = (χ_a-part) + ∫_0^{s∧σ} (1 - χ_a(B_u)) |B_u|^{-γ²} dA(u)`. -/
lemma weightedClock_eq_cut_add (γ : ℝ) (dA : Measure ℝ≥0) (a : ℝ) (σ : ℝ≥0) (B : ℝ≥0 → ℂ)
    (hB : Continuous B) (s : ℝ≥0) :
    weightedClock dA (fun u => gammaWeight γ (B u)) σ s =
      cutWeightedClock γ dA a σ B s +
        ∫⁻ u in Icc 0 (min s σ), (1 - cutoffWeight a (B u)) * gammaWeight γ (B u) ∂dA := by
  have hf : Measurable fun u => cutoffWeight a (B u) * gammaWeight γ (B u) :=
    ((measurable_cutoffWeight a).comp hB.measurable).mul ((measurable_gammaWeight γ).comp hB.measurable)
  unfold weightedClock cutWeightedClock
  dsimp only
  rw [← lintegral_add_left hf]
  refine lintegral_congr fun u => ?_
  rw [← add_mul, add_tsub_cancel_of_le (cutoffWeight_le_one a _), one_mul]

/-- The removed regularized part is bounded by `R_{ε,a}` (tex:386-391): `1 - χ_a ≤ 1_{B_{2a}}`. -/
lemma removed_regClock_le {γ ε a : ℝ} (hc : ℝ → ℂ → ℝ) (ha : 0 < a) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (s : ℝ≥0) :
    (∫⁻ u in Icc 0 (min s σ), (1 - cutoffWeight a (B u)) * regDensity γ ε hc (B u) ∂timeLeb) ≤
      ∫⁻ u in Icc 0 σ, (if ‖B u‖ < 2 * a then regDensity γ ε hc (B u) else 0) ∂timeLeb := by
  have hsub : Icc (0 : ℝ≥0) (min s σ) ⊆ Icc 0 σ := Icc_subset_Icc le_rfl (min_le_right _ _)
  calc _ ≤ ∫⁻ u in Icc 0 (min s σ), (if ‖B u‖ < 2 * a then regDensity γ ε hc (B u) else 0) ∂timeLeb := by
        refine lintegral_mono fun u => ?_
        by_cases h : ‖B u‖ < 2 * a
        · simp only [h, ↓reduceIte]
          exact mul_le_of_le_one_left zero_le tsub_le_self
        · simp only [h, ↓reduceIte]
          rw [cutoffWeight_eq_one ha (not_lt.1 h), tsub_self, zero_mul]
    _ ≤ _ := lintegral_mono_set hsub

/-- The removed weighted part is bounded by `Q_a` (tex:402-405, `removedWeightedClock`). -/
lemma removed_weight_le (γ : ℝ) (dA : Measure ℝ≥0) {a : ℝ} (ha : 0 < a) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (s : ℝ≥0) :
    (∫⁻ u in Icc 0 (min s σ), (1 - cutoffWeight a (B u)) * gammaWeight γ (B u) ∂dA) ≤
      removedWeightedClock γ dA σ a B σ := by
  have hsub : Icc (0 : ℝ≥0) (min s σ) ⊆ Icc 0 (min σ σ) :=
    Icc_subset_Icc le_rfl (by rw [min_self]; exact min_le_right _ _)
  unfold removedWeightedClock
  calc _ ≤ ∫⁻ u in Icc 0 (min s σ), (if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) ∂dA := by
        refine lintegral_mono fun u => ?_
        by_cases h : ‖B u‖ < 2 * a
        · simp only [h, ↓reduceIte]
          exact mul_le_of_le_one_left zero_le tsub_le_self
        · simp only [h, ↓reduceIte]
          rw [cutoffWeight_eq_one ha (not_lt.1 h), tsub_self, zero_mul]
    _ ≤ _ := lintegral_mono_set hsub

/-- `Q_a(s)` is nondecreasing in `a` (the indicator `1_{|B_u| < 2a}` increases with `a`). -/
lemma removedWeightedClock_mono (γ : ℝ) (dA : Measure ℝ≥0) (σ : ℝ≥0) (B : ℝ≥0 → ℂ) {i j : ℝ}
    (hij : i ≤ j) (s : ℝ≥0) :
    removedWeightedClock γ dA σ i B s ≤ removedWeightedClock γ dA σ j B s := by
  unfold removedWeightedClock
  refine lintegral_mono fun u => ?_
  by_cases h1 : ‖B u‖ < 2 * i
  · have h2 : ‖B u‖ < 2 * j := lt_of_lt_of_le h1 (by linarith)
    simp only [h1, h2, ↓reduceIte, le_refl]
  · simp only [h1, ↓reduceIte, zero_le]

/-- The pathwise splitting for one time `s` (for `0 < ε < a`): the `χ_a`-parts and the removed parts. -/
lemma ennDist_regClock_le {γ ε a : ℝ} (hc : ℝ → ℂ → ℝ) (dA : Measure ℝ≥0) (ha : 0 < a) (hε : 0 < ε)
    (hεa : ε < a) (hν : Measurable (nuDensity γ ε hc)) (hreg : Measurable (regDensity γ ε hc))
    (σ : ℝ≥0) (B : ℝ≥0 → ℂ) (hB : Continuous B) (s : ℝ≥0) :
    ennDist (regClock γ ε hc σ B s) (weightedClock dA (fun u => gammaWeight γ (B u)) σ s) ≤
      ennDist (cutApproxClock γ ε hc a σ B s) (cutWeightedClock γ dA a σ B s) +
        ((∫⁻ u in Icc 0 σ, (if ‖B u‖ < 2 * a then regDensity γ ε hc (B u) else 0) ∂timeLeb) +
          removedWeightedClock γ dA σ a B σ) := by
  rw [regClock_eq_cut_add hc a σ B hB hreg s, weightedClock_eq_cut_add γ dA a σ B hB s,
    cut_regDensity_eq hc ha hε hεa hν σ B hB s]
  exact (ennDist_add_add_le _ _ _ _).trans (add_le_add le_rfl
    (add_le_add (removed_regClock_le hc ha σ B s) (removed_weight_le γ dA ha σ B s)))

/-- Convergence in probability of a family which is monotone in the parameter `a` and converges almost surely as
`a ↓ 0`: continuity of measures along the monotone sets `{η < Q_a}` (`tendsto_measure_biInter_gt`). -/
lemma tendsto_measure_of_mono_ae {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q : ℝ → X → ℝ≥0∞) (hQm : ∀ a, Measurable (Q a))
    (hmono : ∀ x, ∀ i j : ℝ, 0 < i → i ≤ j → Q i x ≤ Q j x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun a => Q a x) (𝓝[>] (0 : ℝ)) (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun a => μ {x | ENNReal.ofReal η < Q a x}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmeas : ∀ r > (0 : ℝ), NullMeasurableSet {x | ENNReal.ofReal η < Q r x} μ := fun r _ =>
    (measurableSet_lt measurable_const (hQm r)).nullMeasurableSet
  have hsub : ∀ i j : ℝ, 0 < i → i ≤ j →
      {x | ENNReal.ofReal η < Q i x} ⊆ {x | ENNReal.ofReal η < Q j x} :=
    fun i j hi hij x hx => lt_of_lt_of_le hx (hmono x i j hi hij)
  have h := tendsto_measure_biInter_gt (μ := μ) (a := (0 : ℝ))
    (s := fun r => {x | ENNReal.ofReal η < Q r x})
    hmeas (fun i j hi hij => hsub i j hi hij) ⟨1, one_pos, measure_ne_top _ _⟩
  have hnull : μ (⋂ r > (0 : ℝ), {x | ENNReal.ofReal η < Q r x}) = 0 := by
    refine measure_mono_null (t := {x | ¬ Tendsto (fun a => Q a x) (𝓝[>] (0 : ℝ)) (𝓝 0)}) ?_
      (ae_iff.1 hlim)
    intro x hx htend
    have hev := htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))
    obtain ⟨a, ha1, ha2⟩ := (hev.and self_mem_nhdsWithin).exists
    have hxa : ENNReal.ofReal η < Q a x := mem_iInter₂.1 hx a (mem_Ioi.1 ha2)
    exact lt_asymm hxa ha1
  rw [hnull] at h
  exact h

/-- The sup-distance `D_ε(x) = sup_s |φ_ε(s) - Φ(s)|` on the product of field and Brownian path (tex:413-414). -/
def clockDistD {Ω : Type*} (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (σ : ContinuousPath ℂ → ℝ≥0) (ε : ℝ) (x : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ s : ℝ≥0, ennDist (regClock γ ε (hc x.1) (σ x.2) ⇑x.2 s)
    (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s)

/-- The sup-distance of the `χ_a`-parts (the clock form of tex:373-376). -/
def clockDistE {Ω : Type*} (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (σ : ContinuousPath ℂ → ℝ≥0) (ε a : ℝ) (x : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ s : ℝ≥0, ennDist (cutApproxClock γ ε (hc x.1) a (σ x.2) ⇑x.2 s)
    (cutWeightedClock γ (dA x.1 x.2) a (σ x.2) ⇑x.2 s)

/-- The removed `φ`-part `R_{ε,a}` (tex:386-391). -/
def clockDistR {Ω : Type*} (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (ε a : ℝ)
    (x : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (σ x.2), (if ‖x.2 u‖ < 2 * a then regDensity γ ε (hc x.1) (x.2 u) else 0) ∂timeLeb

/-- The removed `Φ`-part `Q_a` (tex:402-405). -/
def clockDistQ {Ω : Type*} (γ : ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (σ : ContinuousPath ℂ → ℝ≥0) (a : ℝ) (x : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
  removedWeightedClock γ (dA x.1 x.2) (σ x.2) a ⇑x.2 (σ x.2)

/-- **Identification of the clock, concrete form** (tex:370-414): `sup_s |φ_ε - Φ| → 0` in probability as `ε ↓ 0`.
Inputs:
* `hreg`, `hνm`: measurability in `x` of the regularized and approximating densities (joint measurability, implicit
  in the paper; `hc ω` is a circle-average family);
* `hQm`: measurability of the removed weighted clock `Q_a` on the product (implicit in the paper);
* `hfin`: `Φ(σ) < ∞` almost surely (the finiteness of the removed mass, tex:396-398, from eq:occ-weightedmean and
  eq:occ-potential, S3/S4 of `WeightedClock.lean` and `Potential.lean`);
* `hE` (printed tex:377-385): for fixed `a > 0`, the `χ_a`-parts converge in probability, uniformly in `s`
  (from lem:occ-base, the clock convergence `A_ε → A` of `BaseClock.lean`, by Stieltjes continuity);
* `hR` (printed tex:386-400): the removed `φ`-parts are small in probability, uniformly in small `ε`, as `a → 0`
  (from lem:occ-tails `origin_tail_moment` of `OriginTails.lean`, the ordinary Brownian occupation identity
  and the Green bound; see the docstring of `removed_tail_small` when it is proved). -/
theorem regClock_identification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PB : Measure (ContinuousPath ℂ)) [IsProbabilityMeasure PB]
    {γ : ℝ} (hγ : γ ≠ 0) (hc : Ω → ℝ → ℂ → ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (σ : ContinuousPath ℂ → ℝ≥0)
    (hreg : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (hc ω)))
    (hνm : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (nuDensity γ ε (hc ω)))
    (hQm : ∀ a : ℝ, Measurable (clockDistQ γ dA σ a))
    (hfin : ∀ᵐ x ∂(P.prod PB),
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod PB) {x | ENNReal.ofReal η < clockDistE γ hc dA σ ε a x})
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hR : ∀ η : ℝ, 0 < η → ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (P.prod PB) {x | ENNReal.ofReal η < clockDistR γ hc σ ε a x} ≤ δ) :
    ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod PB) {x | ENNReal.ofReal η < clockDistD γ hc dA σ ε x})
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hQ : ∀ η : ℝ, 0 < η →
      Tendsto (fun a => (P.prod PB) {x | ENNReal.ofReal η < clockDistQ γ dA σ a x})
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro η hη
    refine tendsto_measure_of_mono_ae (P.prod PB) (fun a x => clockDistQ γ dA σ a x) hQm
      (fun x i j _hi hij => removedWeightedClock_mono γ (dA x.1 x.2) (σ x.2) ⇑x.2 hij (σ x.2)) ?_ hη
    exact hfin.mono fun x hx =>
      removedWeightedClock_tendsto_zero hγ (dA x.1 x.2) (σ x.2) ⇑x.2 x.2.continuous hx
  have hsplit : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂(P.prod PB),
      clockDistD γ hc dA σ ε x ≤
        clockDistE γ hc dA σ ε a x + clockDistR γ hc σ ε a x + clockDistQ γ dA σ a x := by
    refine eventually_mem_nhdsWithin.mono fun a ha => ?_
    have hI : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 a := Ioo_mem_nhdsGT (mem_Ioi.1 ha)
    refine hI.mono fun ε hε => ?_
    refine ae_of_all _ fun x => ?_
    have hD : ∀ s : ℝ≥0, ennDist (regClock γ ε (hc x.1) (σ x.2) ⇑x.2 s)
        (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s) ≤
        clockDistE γ hc dA σ ε a x + (clockDistR γ hc σ ε a x + clockDistQ γ dA σ a x) := by
      intro s
      refine (ennDist_regClock_le (hc x.1) (dA x.1 x.2) (mem_Ioi.1 ha) hε.1 hε.2 (hνm x.1 ε hε.1)
        (hreg x.1 ε hε.1) (σ x.2) ⇑x.2 x.2.continuous s).trans (add_le_add ?_ le_rfl)
      exact le_iSup (fun s : ℝ≥0 => ennDist (cutApproxClock γ ε (hc x.1) a (σ x.2) ⇑x.2 s)
        (cutWeightedClock γ (dA x.1 x.2) a (σ x.2) ⇑x.2 s)) s
    exact ((iSup_le hD).trans_eq (add_assoc _ _ _).symm)
  exact clock_identification_of_split (P.prod PB) (clockDistD γ hc dA σ)
    (clockDistE γ hc dA σ) (clockDistR γ hc σ) (fun a x => clockDistQ γ dA σ a x) hE hR hQ hsplit

end MatedCRT.KilledOccupation
