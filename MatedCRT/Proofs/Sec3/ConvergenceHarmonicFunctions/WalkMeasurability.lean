import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-!
# Measurability of functionals of the interpolated walk

On the path space `ℕ → ℤ` (product of discrete spaces), the interpolated walk on a
finite time interval depends only on finitely many coordinates. Hence bounded
Lipschitz functionals of the interpolated walk are continuous, and the exit position
from an open set is locally constant on the open event of exiting and a function of
the first coordinates on its complement. This proves `InterpolatedWalkMeasurableStep`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The `k`-th term of the local uniform distance. -/
noncomputable def luTerm (f g : ℝ≥0 → ℂ) (k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ (k + 1) *
    (min 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖)).toReal

theorem localUniformDist_eq_tsum_luTerm (f g : ℝ≥0 → ℂ) :
    localUniformDist f g = ∑' k, luTerm f g k := rfl

theorem summable_luTerm (f g : ℝ≥0 → ℂ) : Summable (luTerm f g) :=
  summable_localUniformDist_terms f g

theorem luTerm_le (f g : ℝ≥0 → ℂ) (k : ℕ) : luTerm f g k ≤ (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold luTerm
  have h1 : (min 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ),
      ENNReal.ofReal ‖f t - g t‖)).toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (min_le_left 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖))
    simpa using this
  calc _ ≤ (2 : ℝ)⁻¹ ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

theorem luTerm_eq_zero (f g : ℝ≥0 → ℂ) {k : ℕ}
    (h : ∀ t : ℝ≥0, t ≤ ((k + 1 : ℕ) : ℝ≥0) → f t = g t) : luTerm f g k = 0 := by
  unfold luTerm
  have hsup : (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖) = 0 := by
    refine ENNReal.iSup_eq_zero.2 fun t => ?_
    rw [h t t.2.2, sub_self, norm_zero, ENNReal.ofReal_zero]
  rw [hsup, min_eq_right zero_le, ENNReal.toReal_zero, mul_zero]

/-- Paths agreeing on `[0, K + 1]` are within `2^{-(K+1)}` in the local uniform distance. -/
theorem localUniformDist_le_of_eqOn (f g : ℝ≥0 → ℂ) (K : ℕ)
    (h : ∀ t : ℝ≥0, t ≤ ((K + 1 : ℕ) : ℝ≥0) → f t = g t) :
    localUniformDist f g ≤ (2 : ℝ)⁻¹ ^ (K + 1) := by
  rw [localUniformDist_eq_tsum_luTerm, ← (summable_luTerm f g).sum_add_tsum_nat_add (K + 1)]
  have h0 : ∑ i ∈ Finset.range (K + 1), luTerm f g i = 0 :=
    Finset.sum_eq_zero fun i hi => luTerm_eq_zero f g fun t ht =>
      h t (ht.trans (Nat.cast_le.2 (by have := Finset.mem_range.1 hi; omega)))
  rw [h0, zero_add]
  have hgeo : Summable fun i : ℕ => (2 : ℝ)⁻¹ ^ (K + 2) * (2 : ℝ)⁻¹ ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' i, luTerm f g (i + (K + 1)) ≤ ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (K + 2) * (2 : ℝ)⁻¹ ^ i :=
        Summable.tsum_le_tsum (fun i => (luTerm_le f g _).trans_eq (by ring))
          ((summable_nat_add_iff (K + 1)).2 (summable_luTerm f g)) hgeo
    _ = (2 : ℝ)⁻¹ ^ (K + 1) := by
        rw [tsum_mul_left, tsum_geometric_inv_two]
        ring

/-- The interpolated walk up to time `T` depends only on the first coordinates. -/
theorem interpolatedWalk_eq_of_eq_le {ε mε : ℝ} {η : ℝ → ℂ} {x x' : ℕ → ℤ} {T : ℝ≥0}
    (h : ∀ i ≤ ⌊|mε| * T⌋₊ + 1, x' i = x i) {t : ℝ≥0} (ht : t ≤ T) :
    interpolatedWalk ε η mε x' t = interpolatedWalk ε η mε x t := by
  have hfl : ⌊mε * (t : ℝ)⌋₊ ≤ ⌊|mε| * T⌋₊ :=
    Nat.floor_mono (mul_le_mul (le_abs_self mε) (by exact_mod_cast ht) t.2 (abs_nonneg mε))
  simp only [interpolatedWalk]
  rw [h _ (show ⌊mε * (t : ℝ)⌋₊ ≤ ⌊|mε| * T⌋₊ + 1 by omega),
    h (⌊mε * (t : ℝ)⌋₊ + 1) (by omega)]

/-- Near any coordinate path, the interpolated walk is unchanged on `[0, T]`. -/
theorem eventually_interpolatedWalk_eqOn (ε mε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) (T : ℝ≥0) :
    ∀ᶠ x' in 𝓝 x, ∀ t ≤ T, interpolatedWalk ε η mε x' t = interpolatedWalk ε η mε x t := by
  have hev : ∀ᶠ x' in 𝓝 x, ∀ i ∈ Finset.range (⌊|mε| * T⌋₊ + 2), x' i = x i := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact (continuous_apply i).continuousAt.eventually_mem
      ((isOpen_discrete {x i}).mem_nhds (mem_singleton _))
  filter_upwards [hev] with x' hx' t ht
  exact interpolatedWalk_eq_of_eq_le (fun i hi => hx' i (Finset.mem_range.2 (by omega))) ht

/-- Bounded Lipschitz path functionals of the interpolated walk are continuous. -/
theorem continuous_pathFunctional_interpolatedWalk {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) (ε mε : ℝ) (η : ℝ → ℂ) :
    Continuous fun x : ℕ → ℤ => F (interpolatedWalk ε η mε x) := by
  obtain ⟨-, L, hL⟩ := hF
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro e he
  have hlim : Tendsto (fun K : ℕ => |L| * (2 : ℝ)⁻¹ ^ (K + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun K : ℕ => (2 : ℝ)⁻¹ ^ (K + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)
    simpa only [mul_zero] using h.const_mul |L|
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds he)).exists
  filter_upwards [eventually_interpolatedWalk_eqOn ε mε η x ((K + 1 : ℕ) : ℝ≥0)] with x' hx'
  rw [Real.dist_eq]
  have hd := localUniformDist_le_of_eqOn _ _ K hx'
  calc |F (interpolatedWalk ε η mε x') - F (interpolatedWalk ε η mε x)|
      ≤ L * localUniformDist (interpolatedWalk ε η mε x') (interpolatedWalk ε η mε x) :=
        hL _ _
    _ ≤ |L| * (2 : ℝ)⁻¹ ^ (K + 1) :=
        mul_le_mul (le_abs_self L) hd (localUniformDist_nonneg _ _) (abs_nonneg L)
    _ < e := hK

/-- Paths agreeing on `[0, T]` and leaving `U` by time `T` have the same exit time. -/
theorem pathExitTime_eq_of_eqOn {U : Set ℂ} {f g : ℝ≥0 → ℂ} {T t₀ : ℝ≥0}
    (hfg : ∀ t ≤ T, f t = g t) (ht₀ : t₀ ≤ T) (h₀ : f t₀ ∉ U) :
    pathExitTime U f = pathExitTime U g := by
  have key : ∀ f g : ℝ≥0 → ℂ, (∀ t ≤ T, f t = g t) → f t₀ ∉ U →
      pathExitTime U f ≤ pathExitTime U g := by
    intro f g hfg h₀
    unfold pathExitTime
    apply le_sInf
    rintro s ⟨t, rfl, ht⟩
    by_cases htT : t ≤ T
    · exact sInf_le ⟨t, rfl, by rwa [hfg t htT]⟩
    · have hmem : (t₀ : ℝ≥0∞) ∈ {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = t ∧ f t ∉ U} := ⟨t₀, rfl, h₀⟩
      exact (sInf_le hmem).trans (ENNReal.coe_le_coe.2 (ht₀.trans (not_le.mp htT).le))
  exact le_antisymm (key f g hfg h₀)
    (key g f (fun t ht => (hfg t ht).symm) (by rwa [← hfg t₀ ht₀]))

/-- Paths agreeing on `[0, T]` and leaving `U` by time `T` have the same exit position. -/
theorem pathExitPosition_eq_of_eqOn {U : Set ℂ} {f g : ℝ≥0 → ℂ} {T t₀ : ℝ≥0}
    (hfg : ∀ t ≤ T, f t = g t) (ht₀ : t₀ ≤ T) (h₀ : f t₀ ∉ U) :
    pathExitPosition U f = pathExitPosition U g := by
  have he := pathExitTime_eq_of_eqOn hfg ht₀ h₀
  have hle : pathExitTime U f ≤ t₀ := by
    unfold pathExitTime
    exact sInf_le ⟨t₀, rfl, h₀⟩
  have hfin : pathExitTime U f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, pathExitTime U f = τ :=
    ⟨_, (ENNReal.coe_toNNReal hfin).symm⟩
  have hτT : τ ≤ T := (ENNReal.coe_le_coe.1 (hτ ▸ hle)).trans ht₀
  unfold pathExitPosition
  rw [← he, hτ]
  exact hfg τ hτT

/-- A path that never leaves `U` has junk exit position `f 0`. -/
theorem pathExitPosition_of_forall_mem {U : Set ℂ} {f : ℝ≥0 → ℂ} (h : ∀ t, f t ∈ U) :
    pathExitPosition U f = f 0 := by
  have hempty : {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = t ∧ f t ∉ U} = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro s ⟨t, -, ht⟩
    exact ht (h t)
  unfold pathExitPosition pathExitTime
  rw [hempty, sInf_empty]
  rfl

/-- Continuous functions of the exit position of the interpolated walk are measurable. -/
theorem measurable_exitPosition_interpolatedWalk (ε mε : ℝ) (η : ℝ → ℂ) {U : Set ℂ}
    {φ : ℂ → ℝ} :
    Measurable fun x : ℕ → ℤ => φ (pathExitPosition U (interpolatedWalk ε η mε x)) := by
  classical
  set g : (ℕ → ℤ) → ℝ := fun x => φ (pathExitPosition U (interpolatedWalk ε η mε x))
  let E : Set (ℕ → ℤ) := {x | ∃ t, interpolatedWalk ε η mε x t ∉ U}
  have hloc : ∀ x ∈ E, ∀ᶠ x' in 𝓝 x, x' ∈ E ∧ g x' = g x := by
    rintro x ⟨t₀, ht₀⟩
    filter_upwards [eventually_interpolatedWalk_eqOn ε mε η x t₀] with x' hx'
    refine ⟨⟨t₀, by rwa [hx' t₀ le_rfl]⟩, ?_⟩
    change φ _ = φ _
    rw [pathExitPosition_eq_of_eqOn hx' le_rfl (by rwa [hx' t₀ le_rfl])]
  have hEopen : IsOpen E := isOpen_iff_mem_nhds.2 fun x hx =>
    (hloc x hx).mono fun _ h => h.1
  have hcE : ContinuousOn g E := fun x hx =>
    ContinuousAt.continuousWithinAt
      (tendsto_nhds_of_eventually_eq ((hloc x hx).mono fun _ h => h.2))
  have hcEc : ContinuousOn g Eᶜ := by
    intro x hx
    have hx0 : ∀ x' ∈ Eᶜ, g x' = φ (interpolatedWalk ε η mε x' 0) := by
      intro x' hx'
      change φ _ = _
      rw [pathExitPosition_of_forall_mem fun t => by
        by_contra h
        exact hx' ⟨t, h⟩]
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_interpolatedWalk_eqOn ε mε η x 0)] with x' hx' hw
    rw [hx0 x' hx', hx0 x hx, hw 0 le_rfl]
  have h := hcE.measurable_piecewise hcEc hEopen.measurableSet
  rwa [piecewise_same] at h

/-- **`InterpolatedWalkMeasurableStep` holds.** -/
theorem interpolatedWalkMeasurableStep : InterpolatedWalkMeasurableStep := by
  intro ε mε η m a
  refine ⟨fun F hF => (continuous_pathFunctional_interpolatedWalk hF ε mε η).measurable
    |>.aestronglyMeasurable, fun U _ φ _ => ?_⟩
  exact (measurable_exitPosition_interpolatedWalk ε mε η).aestronglyMeasurable

end MatedCRT
