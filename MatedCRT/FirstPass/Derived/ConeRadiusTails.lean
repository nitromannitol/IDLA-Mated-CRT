import MatedCRT.FirstPass.Derived.ConeScaleRadiusMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScaleExhaustion
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeRadialOriginLimit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RadialBoundReduction

/-!
# Tails of the cone scale radii (Berestycki–Gwynne (2020), §6.4)

For a quantum cone `(h, γ)` the scale radii `R_b` (eq:cone-scale-radius) satisfy, with no further input:

* `exists_measure_gt_le_coneScaleRadius`: for every `b` and `θ > 0` there is `M` with `P {M < R_b} ≤ θ`
  (tightness of the real random variable `R_b`);
* `exists_measure_coneScaleRadius_le_le`: for every `R₁` and `θ > 0` there is `N` such that
  `P {R_{n+1} ≤ R₁} ≤ θ` for all `n ≥ N` (convergence in probability of `R_{n+1}` to `+∞`, which follows from the
  almost sure divergence `R_{n+1} → ∞`).

The two measure statements are proved for arbitrary almost everywhere measurable real random variables on a
finite measure space.
-/

open MeasureTheory Filter Topology Set HarmonicBalls MatedCRT
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Tightness of a real random variable**: an almost everywhere measurable real function on a finite measure
space exceeds some level only on a set of measure at most `θ`. -/
theorem exists_measure_gt_le_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEMeasurable f P) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ M : ℝ, P {ω | M < f ω} ≤ θ := by
  have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℝ) < f ω} P := fun n =>
    hf.nullMeasurable measurableSet_Ioi
  have hanti : Antitone (fun n : ℕ => {ω | (n : ℝ) < f ω}) := fun m n hmn ω (hω : (n : ℝ) < f ω) =>
    show (m : ℝ) < f ω from lt_of_le_of_lt (Nat.cast_le.2 hmn) hω
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n : ℕ, {ω | (n : ℝ) < f ω}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge (f ω)
    exact ⟨n, hn⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 θ hθ).exists
  exact ⟨n, hn.le⟩

/-- **Convergence in probability to infinity from almost sure divergence**: if almost everywhere measurable
real random variables `R n` tend to `+∞` almost surely on a finite measure space, then for every level `R₁`
and `θ > 0` the sets `{R n ≤ R₁}` have measure at most `θ` for all large `n`. -/
theorem exists_measure_le_le_of_ae_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {R : ℕ → Ω → ℝ} (hR : ∀ n, AEMeasurable (R n) P)
    (hT : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop atTop) (R₁ : ℝ) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n, N ≤ n → P {ω | R n ω ≤ R₁} ≤ θ := by
  set C : ℕ → Set Ω := fun N => ⋃ n, ⋃ (_ : N ≤ n), {ω | R n ω ≤ R₁} with hC
  have hmeas : ∀ N, NullMeasurableSet (C N) P := fun N =>
    NullMeasurableSet.iUnion fun n => NullMeasurableSet.iUnion fun _ =>
      (hR n).nullMeasurable measurableSet_Iic
  have hanti : Antitone C := fun M N hMN ω hω => by
    simp only [hC, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, hω⟩ := hω
    exact ⟨n, hMN.trans hn, hω⟩
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ N, C N) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hT)
    intro hlimω
    obtain ⟨N, hN⟩ := (tendsto_atTop.1 hlimω (R₁ + 1)).exists_forall_of_atTop
    have := mem_iInter.1 hω N
    simp only [hC, mem_iUnion, mem_ofPred_eq] at this
    obtain ⟨n, hn, hle⟩ := this
    have := hN n hn
    linarith
  rw [hnull] at hlim
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 θ hθ).exists
  refine ⟨N, fun n hn => (measure_mono fun ω hω => ?_).trans hN.le⟩
  simp only [hC, mem_iUnion]
  exact ⟨n, hn, hω⟩

/-- The positive integer-mass cone scale radii `R_{n+1}` tend to `+∞` almost surely, for a quantum cone. -/
theorem ae_tendsto_coneScaleRadius_succ {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) atTop atTop := by
  have hpositive (n : ℕ) : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) :=
    (ae_coneScaleRadius_spec hγ hγ2 h ((n : ℝ) + 1)).mono fun ω hω => hω.1
  filter_upwards [h.ae_radial_expression_tendsto_origin hγ hγ2, h.ae_continuousOn_circle,
    ae_all_iff.mpr hpositive] with ω hzero hc hpos
  have hcircle : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun _ hr => ne_of_gt hr)
  have hcont : ContinuousOn (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hcircle.add (continuousOn_const.mul hlog)
  have hlocal : ∀ M : ℝ, 0 < M →
      BddAbove ((fun r => hcirc ω r 0 + lqgQ γ * Real.log r) '' Ioc 0 M) :=
    fun M _ => bddAbove_image_Ioc_of_tendsto_atBot hcont hzero
  exact coneScaleRadius_tendsto_of_radial_bound hγ (hcirc ω) hlocal hpos

/-- **Tightness of the cone scale radius**: for `b ∈ ℝ` and `θ > 0` there is `M` with `P {M < R_b} ≤ θ`. -/
theorem exists_measure_gt_le_coneScaleRadius {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ M : ℝ, P {ω | M < coneScaleRadius γ (hcirc ω) b} ≤ θ :=
  exists_measure_gt_le_of_aemeasurable (aemeasurable_coneScaleRadius hγ hγ2 h b) hθ

/-- **The cone scale radii `R_{n+1}` tend to infinity in probability**: for every level `R₁` and `θ > 0`,
`P {R_{n+1} ≤ R₁} ≤ θ` for all large `n`. -/
theorem exists_measure_coneScaleRadius_le_le {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (R₁ : ℝ) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      P {ω | coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) ≤ R₁} ≤ θ :=
  exists_measure_le_le_of_ae_tendsto_atTop
    (fun n => aemeasurable_coneScaleRadius hγ hγ2 h ((n : ℝ) + 1))
    (ae_tendsto_coneScaleRadius_succ hγ hγ2 h) R₁ hθ

end MatedCRT.FirstPass.Derived
