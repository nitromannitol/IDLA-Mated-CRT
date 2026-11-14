import MatedCRT.FirstPass.Derived.GmcTiltedAnnulusMass
import HarmonicBalls.Steps.Sec11.ExponentialCircleAverageTail

/-!
# Almost-sure summability of the LQG masses of `e`-adic annuli about a log singularity

Let `h^ℂ` be a whole-plane GFF, `0 < γ < 2`, and let `Γ` be the cut-off γ-LQG measure of `h = h^ℂ - γ log |·|`.
For `c ≥ 0` let `τ_n = e^{-(c + n)}` and let `A_n = {τ_n / (2e) ≤ |x| ≤ τ_n / 2}` be the `e`-adic annuli about the
origin (`eAdicAnnulus c n`); they cover the punctured disc `0 < |x| ≤ τ_0 / 2`. Then almost surely
`∑_n (n + 1) Γ(A_n) < ∞` (`ae_tsum_succ_mul_gmcLimit_eAdicAnnulus_lt_top`).

The proof uses only first moments. With `κ = 2 - γ²/2 > 0` and `δ = κ / 4`:
* the tilted first moment `E[e^{-γ h^ℂ_{τ_n}(0)} Γ(A_n)] ≤ π (4e)^{γ²} τ_n^{κ}`
  (`lintegral_exp_neg_centredCircle_mul_gmcLimit_annulus_le`), so the series
  `∑_n (n + 1) e^{γ δ n} e^{-γ h^ℂ_{τ_n}(0)} Γ(A_n)` has finite expectation, since `γ δ < κ`;
* by the Borel-Cantelli lemma along exponential radii
  (`HarmonicBalls.IsWholePlaneGFF.tsum_circleAverage_exp_upper_lt_top`), almost surely `h^ℂ_{τ_n}(0) ≤ δ n` for all
  large `n`, hence `h^ℂ_{τ_n}(0) ≤ δ n + D` for all `n` with a finite random `D`, and
  `(n + 1) Γ(A_n) ≤ e^{γ D} (n + 1) e^{γ δ n} e^{-γ h^ℂ_{τ_n}(0)} Γ(A_n)`.
This is the first-moment argument for the LQG mass near a `γ`-log singularity (Duplantier-Sheffield 2011, Section 3).
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The `e`-adic annulus `{e^{-(c+n)} / (2e) ≤ |x| ≤ e^{-(c+n)} / 2}` about the origin. -/
def eAdicAnnulus (c : ℝ) (n : ℕ) : Set ℂ :=
  {x | Real.exp (-(c + n)) / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (-(c + n)) / 2}

lemma measurableSet_eAdicAnnulus (c : ℝ) (n : ℕ) : MeasurableSet (eAdicAnnulus c n) :=
  (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)

/-- The tilted first-moment bound of an annulus of radius `τ` is `π (4e)^{γ²} τ^{2 - γ²/2}`. -/
lemma annulusMomentBound_eq (γ : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    τ ^ (γ ^ 2 / 2) * (τ / (2 * Real.exp 1) / 2) ^ (-γ ^ 2) * (Real.pi * τ ^ 2) =
      Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * τ ^ (2 - γ ^ 2 / 2) := by
  have h4 : 0 < 4 * Real.exp 1 := by positivity
  rw [show τ / (2 * Real.exp 1) / 2 = τ / (4 * Real.exp 1) by ring, Real.div_rpow hτ.le h4.le,
    Real.rpow_neg h4.le, ← Real.rpow_two τ, show (2 : ℝ) - γ ^ 2 / 2 = γ ^ 2 / 2 + -γ ^ 2 + 2 by ring,
    Real.rpow_add hτ, Real.rpow_add hτ, div_inv_eq_mul]
  ring

/-- **Almost-sure summability of the LQG masses of the `e`-adic annuli about the origin.** For a whole-plane GFF
`h^ℂ`, `0 < γ < 2`, `ρ < ρ₂ < 1` and `c ≥ 0`, with `Γ` the cut-off γ-LQG measure of `h^ℂ - γ log |·|`: almost
surely `∑_n (n + 1) Γ(A_n) < ∞`, where `A_n = eAdicAnnulus c n`. -/
theorem ae_tsum_succ_mul_gmcLimit_eAdicAnnulus_lt_top {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂)
    (hρ₂ : ρ₂ < 1) {c : ℝ} (hc0 : 0 ≤ c) :
    ∀ᵐ ω' ∂P', ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) + 1) *
      gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n) < ∞ := by
  have hκ0 : 0 < 2 - γ ^ 2 / 2 := by nlinarith
  set δ : ℝ := (2 - γ ^ 2 / 2) / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hγδ : γ * δ < 2 - γ ^ 2 / 2 := by rw [hδ]; nlinarith
  set r : ℝ := Real.exp (γ * δ) * Real.exp (-(2 - γ ^ 2 / 2)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_add]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hK0 : 0 ≤ Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) := by positivity
  have hτ : ∀ n : ℕ, 0 < Real.exp (-(c + n)) := fun n => Real.exp_pos _
  have hτ1 : ∀ n : ℕ, Real.exp (-(c + n)) ≤ 1 := fun n =>
    Real.exp_le_one_iff.2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hψm : Measurable (clockPsi (fun ω' => fieldCircleAverage γ (hc ω'))) :=
    measurable_unitDiskCircle _ fun r' z' hr' => (hG.measurable_circle r' z' hr').sub measurable_const
  have hgm : ∀ n : ℕ, Measurable fun ω' => ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
      (ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
        gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n)) := fun n =>
    measurable_const.mul ((((hG.measurable_circle _ 0 (hτ n)).const_mul (-γ)).exp.ennreal_ofReal).mul
      ((Measure.measurable_coe (measurableSet_eAdicAnnulus c n)).comp ((measurable_gmcLimit γ ρ ρ₂).comp hψm)))
  -- Step 1: the tilted first moment of each annulus.
  have hbound : ∀ n : ℕ, ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
        gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n) ∂P' ≤
      ENNReal.ofReal (Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * Real.exp (-(2 - γ ^ 2 / 2)) ^ n) := by
    intro n
    refine (lintegral_exp_neg_centredCircle_mul_gmcLimit_annulus_le hG hγ hγ2 hρρ₂ hρ₂ (hτ n) (hτ1 n)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), annulusMomentBound_eq γ (hτ n)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hK0)
    rw [← Real.exp_mul, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc0 hκ0.le])
  -- Step 2: the tilted weighted series has finite expectation.
  have hsum : Summable fun n : ℕ => Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * (((n : ℝ) + 1) * r ^ n) := by
    have hr' : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
    refine (((summable_pow_mul_geometric_of_norm_lt_one 1 hr').add
      (summable_geometric_of_lt_one hr0 hr1)).mul_left (Real.pi * (4 * Real.exp 1) ^ (γ ^ 2))).congr fun n => ?_
    ring
  have hfin : ∑' n : ℕ, ENNReal.ofReal (Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * (((n : ℝ) + 1) * r ^ n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hK0 (mul_nonneg (by positivity) (pow_nonneg hr0 n))) hsum]
    exact ENNReal.ofReal_ne_top
  have hE : ∫⁻ ω', ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
        (ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
          gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n)) ∂P' ≠ ∞ := by
    rw [lintegral_tsum fun n => (hgm n).aemeasurable]
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun n => ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
          ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
            gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n) ∂P'
        ≤ ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
          ENNReal.ofReal (Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * Real.exp (-(2 - γ ^ 2 / 2)) ^ n) := by
          gcongr
          exact hbound n
      _ = ENNReal.ofReal (Real.pi * (4 * Real.exp 1) ^ (γ ^ 2) * (((n : ℝ) + 1) * r ^ n)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hr, mul_pow]
          ring_nf
  -- Step 3: Borel-Cantelli for the circle averages at the radii `τ_n`.
  have hBC : ∀ᵐ ω' ∂P', ∀ᶠ n : ℕ in atTop, ω' ∉ {ω | δ * (n : ℝ) < hc ω (Real.exp (-(c + n))) 0} :=
    ae_eventually_notMem (hG.tsum_circleAverage_exp_upper_lt_top hc0 hδ0)
  filter_upwards [hBC, ae_lt_top (Measurable.tsum hgm) hE] with ω' hBC' hT
  obtain ⟨N, hN⟩ := eventually_atTop.1 hBC'
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ n : ℕ, hc ω' (Real.exp (-(c + n))) 0 ≤ δ * n + D := by
    refine ⟨∑ m ∈ Finset.range N, |hc ω' (Real.exp (-(c + m))) 0 - δ * m|, fun n => ?_⟩
    have hS0 : 0 ≤ ∑ m ∈ Finset.range N, |hc ω' (Real.exp (-(c + m))) 0 - δ * m| :=
      Finset.sum_nonneg fun m _ => abs_nonneg _
    rcases lt_or_ge n N with hn | hn
    · have h1 := Finset.single_le_sum (f := fun m : ℕ => |hc ω' (Real.exp (-(c + m))) 0 - δ * m|)
        (fun m _ => abs_nonneg _) (Finset.mem_range.2 hn)
      have h2 := le_abs_self (hc ω' (Real.exp (-(c + n))) 0 - δ * n)
      linarith
    · have h1 : hc ω' (Real.exp (-(c + n))) 0 ≤ δ * n := not_lt.1 (hN n hn)
      linarith
  -- Step 4: comparison with the tilted series.
  calc ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) + 1) *
        gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n)
      ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (γ * D)) *
          (ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
            (ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
              gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n))) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        have h1 : 1 ≤ Real.exp (γ * D) * Real.exp (γ * δ) ^ n *
            Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
          exact Real.one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left (hD n) hγ.le])
        have hreal : (n : ℝ) + 1 ≤ Real.exp (γ * D) * ((((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
            Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) :=
          calc (n : ℝ) + 1 = ((n : ℝ) + 1) * 1 := (mul_one _).symm
            _ ≤ ((n : ℝ) + 1) * (Real.exp (γ * D) * Real.exp (γ * δ) ^ n *
                Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := by ring
        have hE0 : 0 ≤ Real.exp (γ * D) := (Real.exp_pos _).le
        have hX0 : 0 ≤ ((n : ℝ) + 1) * Real.exp (γ * δ) ^ n := by positivity
        have hsplit : ENNReal.ofReal (Real.exp (γ * D)) * (ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
            ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0))) =
            ENNReal.ofReal (Real.exp (γ * D) * ((((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
              Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0))) := by
          rw [ENNReal.ofReal_mul hE0, ENNReal.ofReal_mul hX0]
        calc ENNReal.ofReal ((n : ℝ) + 1) *
              gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n)
            ≤ ENNReal.ofReal (Real.exp (γ * D)) * (ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
                ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0))) *
              gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n) := by
              rw [hsplit]
              gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.exp (γ * D)) * ∑' n : ℕ,
          ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (γ * δ) ^ n) *
            (ENNReal.ofReal (Real.exp (-γ * hc ω' (Real.exp (-(c + n))) 0)) *
              gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (eAdicAnnulus c n)) :=
        ENNReal.tsum_mul_left
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT

end MatedCRT.KilledOccupation
