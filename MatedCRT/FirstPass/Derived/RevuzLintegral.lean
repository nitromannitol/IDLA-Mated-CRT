import MatedCRT.FirstPass.Derived.RevuzFormula
import MatedCRT.FirstPass.Derived.RevuzKernel

/-!
# The Revuz formula for nonnegative functions

For a measurable family of laws `W` and a clock `A` with measurable time slices, the Revuz measure
`revuz W A` integrates every measurable `g ≥ 0` as the iterated integral

`∫ g d(revuz W A) = ∫ dz ∫ W z (dω) ∫_{(0,1]} g(ω_s) dA_s(ω)`

(Revuz–Yor (1999), Chapter X, §2; Fukushima–Oshima–Takeda (2011), (5.1.13) with `h ≡ 1`), first with the
rational-time regularization of the clock (`lintegral_revuz`) and, for a positive continuous additive
functional, with the Stieltjes measure of the clock itself (`lintegral_revuz_of_isPCAF`). The integral against
the occupation measure of a path is the Stieltjes integral along the path (`lintegral_occupationMeasure`).
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Integral against the occupation measure of a path**: `∫ g d(occupationMeasure a ω) =
∫_{(0,1]} g(ω_s) da_s` for measurable `g ≥ 0`. -/
theorem lintegral_occupationMeasure (a : ℝ≥0 → ℝ≥0) (ω : ContinuousPath ℂ) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂occupationMeasure a ω =
      ∫⁻ s in Ioc (0 : ℝ) 1, g (ω s.toNNReal) ∂(stieltjesOfNNReal a).measure := by
  unfold occupationMeasure
  exact lintegral_map hg (g := fun s : ℝ => ω s.toNNReal)
    (ω.continuous.comp continuous_real_toNNReal).measurable

/-- **The Revuz formula for nonnegative functions**, regularized form: for a measurable family of laws `W` and a
clock with measurable time slices, `∫ g d(revuz W A) = ∫ dz ∫ W z (dω) ∫ g d(occupation measure of the
regularized clock along ω)`. -/
theorem lintegral_revuz {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t)) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂revuz W A =
      ∫⁻ z, ∫⁻ ω, ∫⁻ x, g x ∂occupationMeasure (fun t => regularize A t ω) ω ∂W z ∂volume := by
  have hk := measurable_occupationMeasure_regularize hA
  have hm : Measurable fun z : ℂ =>
      (W z).bind fun ω => occupationMeasure (fun t => regularize A t ω) ω :=
    (Measure.measurable_bind' hk).comp hW
  unfold revuz
  rw [Measure.lintegral_bind hm.aemeasurable hg.aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [Measure.lintegral_bind hk.aemeasurable hg.aemeasurable]

/-- **The Revuz formula for nonnegative functions and a PCAF**: `∫ g d(revuz W A) =
∫ dz ∫ W z (dω) ∫_{(0,1]} g(ω_s) dA_s(ω)`, with the Stieltjes measure of the clock `A · ω` itself. -/
theorem lintegral_revuz_of_isPCAF {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂revuz W A =
      ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (0 : ℝ) 1, g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun t => A t ω).measure ∂W z ∂volume := by
  rw [lintegral_revuz hW hA.meas hg]
  refine lintegral_congr fun z => lintegral_congr_ae ?_
  filter_upwards [hA.path z] with ω hω
  rw [occupationMeasure_regularize_eq_of_path hω.2.1 hω.2.2, lintegral_occupationMeasure _ _ hg]

end MatedCRT
