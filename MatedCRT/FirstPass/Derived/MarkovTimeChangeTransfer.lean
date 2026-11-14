import MatedCRT.FirstPass.Derived.MarkovTimeChangeGood

/-!
# Transfer of almost-sure properties of the clock-read path to the planar Brownian path

For a Markovian time-changed planar Brownian motion, the half-speed Euclidean reading `halfRead` of the
planar Brownian path has the same law as the clock-read path of the coupling (`hmap` below, proved in
`IsMarkovTCBM.exists_adaptedClock`).  Hence an almost-sure property of the clock-read path, stated through a
measurable set of paths, holds for the half-speed reading of the planar Brownian path.

* `ae_halfRead_mem_of_ae_clockRead`: the transfer for a measurable set `S` of paths;
* `halfRead_pathShift`: the half-speed reading of the path shifted by `t` is the shifted reading at `2 t`;
* `ae_halfRead_pathShift_mem_clockGoodSet`: almost surely, for each shift `t`, the half-speed reading of the
  shifted planar path has a good skeleton (`clockGoodSet`).
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- **Transfer of an almost-sure property along equality of the laws of the read paths.** -/
theorem ae_halfRead_mem_of_ae_clockRead {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {ν : Measure (ContinuousPath ℂ)} {m : ℝ≥0∞}
    (hmap : μ.map (LatticeProb.clockRead m) = ν.map halfRead)
    {S : Set (ℝ≥0 → EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S)
    (h : ∀ᵐ x ∂μ, LatticeProb.clockRead m x ∈ S) : ∀ᵐ w ∂ν, halfRead w ∈ S := by
  have h1 : ∀ᵐ f ∂(μ.map (LatticeProb.clockRead m)), f ∈ S :=
    (ae_map_iff (LatticeProb.measurable_clockRead (E := EuclideanSpace ℝ (Fin 2)) m).aemeasurable
      hS).2 h
  rw [hmap] at h1
  exact ae_of_ae_map (p := fun f => f ∈ S) measurable_halfRead.aemeasurable h1

/-- The half-speed reading of the planar path shifted by `t` is the half-speed reading of the path, shifted
by `2 t`. -/
theorem halfRead_pathShift (w : ContinuousPath ℂ) (t : ℝ≥0) :
    halfRead (LatticeProb.pathShift w t) = fun u => halfRead w (2 * t + u) := by
  funext u
  have h : (2⁻¹ : ℝ≥0) * (2 * t + u) = t + 2⁻¹ * u := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
  simp only [halfRead, halfPath_apply, LatticeProb.pathShift_apply, h]

/-- **Almost surely every shifted half-speed reading of the planar path has a good skeleton.**  If the
read-path laws agree (`hmap`), the crossing clock is almost surely good and the shift identity holds for the
functionals `F`, then `ν`-almost surely, for the shift `t`, the half-speed reading of the shifted planar path
lies in `clockGoodSet F`. -/
theorem ae_halfRead_pathShift_mem_clockGoodSet {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {ν : Measure (ContinuousPath ℂ)} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : μ.map (LatticeProb.clockRead m) = ν.map halfRead)
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (t : ℝ≥0) :
    ∀ᵐ w ∂ν, halfRead (LatticeProb.pathShift w t) ∈ clockGoodSet F := by
  have hset : MeasurableSet
      {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | (fun q => f (2 * t + q)) ∈ clockGoodSet F} :=
    (measurableSet_clockGoodSet hF).preimage (measurable_pi_iff.2 fun q => measurable_pi_apply _)
  have h := ae_shift_mem_clockGoodSet hgood hS (2 * t)
  filter_upwards [ae_halfRead_mem_of_ae_clockRead hmap hset h] with w hw
  rw [halfRead_pathShift]
  exact hw

end MatedCRT
