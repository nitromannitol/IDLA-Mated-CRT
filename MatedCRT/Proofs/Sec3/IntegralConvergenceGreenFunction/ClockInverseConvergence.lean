import MatedCRT.Proofs.LBM.TimeChangeContinuity
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.StoppedClockExtension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Convergence of inverses of increasing clocks -/

namespace MatedCRT

open Filter HarmonicBalls Topology MeasureTheory MarkovProcess
open scoped NNReal

/-- Pointwise convergence of strictly increasing clocks implies convergence
of their inverses at every clock value of the limiting clock. The
approximating clocks need not have infinite lifetime. -/
theorem tendsto_clockInverse_clockValue_of_tendsto
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i))
    (hGzero : G 0 = 0) (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (r : ℝ≥0)
    (u : ι → ℝ≥0) (hu : Tendsto u l (𝓝 (Real.toNNReal (G r)))) :
    Tendsto (fun i => clockInverse (F i) (u i)) l (𝓝 r) := by
  have hGr : 0 ≤ G r := by
    simpa [hGzero] using hGmono.monotone (show 0 ≤ r from bot_le)
  have hvalue : (Real.toNNReal (G r) : ℝ) = G r := Real.coe_toNNReal _ hGr
  have hu' : Tendsto (fun i => (u i : ℝ)) l (𝓝 (G r)) := by
    simpa [Function.comp_def, hvalue] using NNReal.continuous_coe.continuousAt.tendsto.comp hu
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨s, has, hsr⟩ := exists_between ha
    have hGs : G s < G r := hGmono hsr
    have hupper : G r < G (r + 1) := hGmono (by simp)
    filter_upwards [(hconv s).eventually_lt hu' hGs,
      hu'.eventually_lt (hconv (r + 1)) hupper] with i hi hj
    have hs : s ≤ clockInverse (F i) (u i) := by
      unfold clockInverse
      apply le_csInf
      · exact ⟨r + 1, hj⟩
      · intro t ht
        exact (hmono i).lt_iff_lt.mp (lt_trans hi ht) |>.le
    exact has.trans_le hs
  · intro a ha
    obtain ⟨s, hrs, hsa⟩ := exists_between ha
    have hGs : G r < G s := hGmono hrs
    filter_upwards [hu'.eventually_lt (hconv s) hGs] with i hi
    have hs : clockInverse (F i) (u i) ≤ s := clockInverse_le_of_lt hi
    exact hs.trans_lt hsa

/-- Pointwise convergence of clocks implies convergence of the inverses at
a fixed value of the limiting clock. -/
theorem tendsto_clockInverse_clockValue
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hGzero : G 0 = 0) (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (r : ℝ≥0) :
    Tendsto (fun i => clockInverse (F i) (Real.toNNReal (G r))) l (𝓝 r) :=
  tendsto_clockInverse_clockValue_of_tendsto hmono hGzero hGmono hconv r _ tendsto_const_nhds

/-- If the limiting clock has infinite lifetime, inverse convergence holds
at every nonnegative clock time. -/
theorem tendsto_clockInverse_of_pointwise
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hG : IsTimeChangeClock G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t))) (u : ℝ≥0) :
    Tendsto (fun i => clockInverse (F i) u) l (𝓝 (clockInverse G u)) := by
  obtain ⟨r, hr⟩ := IsTimeChangeClock.surjective_toNNReal hG u
  rw [← hr, clockInverse_clockValue hG.map_zero hG.strictMono]
  exact tendsto_clockInverse_clockValue hmono hG.map_zero hG.strictMono hconv r

/-- For bounded continuous observables, occupation on a fixed clock-time
interval converges under pointwise convergence of infinite-lifetime clocks. -/
theorem tendsto_clockInverse_occupation
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hF : ∀ i, IsTimeChangeClock (F i)) (hG : IsTimeChangeClock G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t)))
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f)
    (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C) (U : ℝ) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..U, f (b (clockInverse (F i) s.toNNReal))) l
      (𝓝 (∫ s in (0 : ℝ)..U, f (b (clockInverse G s.toNNReal)))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · filter_upwards [] with i
    exact Continuous.aestronglyMeasurable (hf.comp (b.continuous.comp
      ((IsTimeChangeClock.continuous_clockInverse (hF i)).comp continuous_real_toNNReal)))
  · filter_upwards [] with i
    exact Filter.Eventually.of_forall (fun s _ => hbound _)
  · exact intervalIntegrable_const
  · filter_upwards [] with s _
    exact hf.continuousAt.tendsto.comp (b.continuous.continuousAt.tendsto.comp
      (tendsto_clockInverse_of_pointwise (fun i => (hF i).strictMono) hG hconv s.toNNReal))

/-- Occupation convergence before a fixed terminal clock value, without an
infinite-lifetime assumption on either the clocks or their approximations. -/
theorem tendsto_clockInverse_occupation_before
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hFzero : ∀ i, F i 0 = 0) (hFcont : ∀ i, Continuous (F i))
    (hFmono : ∀ i, StrictMono (F i))
    (hGzero : G 0 = 0) (hGcont : Continuous G) (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t)))
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f)
    (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C) (T : ℝ≥0) (U : ℝ)
    (hU : 0 ≤ U) (hUT : U < G T) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..U, f (b (clockInverse (F i) s.toNNReal))) l
      (𝓝 (∫ s in (0 : ℝ)..U, f (b (clockInverse G s.toNNReal)))) := by
  have hconv' : ∀ t, Tendsto (fun i => stoppedClockExtension (F i) T t) l
      (𝓝 (stoppedClockExtension G T t)) := by
    intro t
    simpa [stoppedClockExtension] using
      (hconv (min t T)).add_const (max ((t : ℝ) - T) 0)
  have h := tendsto_clockInverse_occupation
    (fun i => stoppedClockExtension_isTimeChangeClock T (hFzero i) (hFcont i) (hFmono i))
    (stoppedClockExtension_isTimeChangeClock T hGzero hGcont hGmono)
    hconv' b f hf C hbound U
  have heq : ∀ᶠ i in l,
      (∫ s in (0 : ℝ)..U, f (b (clockInverse (F i) s.toNNReal))) =
      (∫ s in (0 : ℝ)..U, f (b (clockInverse (stoppedClockExtension (F i) T) s.toNNReal))) := by
    filter_upwards [(tendsto_order.1 (hconv T)).1 U hUT] with i hi
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hU]
    intro s hs
    have hle : (s.toNNReal : ℝ) ≤ F i T := by
      simpa [Real.coe_toNNReal _ hs.1] using hs.2.trans (le_of_lt hi)
    dsimp only
    rw [stoppedClockExtension_inverse_eq (hFzero i) (hFcont i) (hFmono i) hle]
  have hlimit : (∫ s in (0 : ℝ)..U, f (b (clockInverse (stoppedClockExtension G T) s.toNNReal))) =
      (∫ s in (0 : ℝ)..U, f (b (clockInverse G s.toNNReal))) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hU]
    intro s hs
    have hle : (s.toNNReal : ℝ) ≤ G T := by
      simpa [Real.coe_toNNReal _ hs.1] using hs.2.trans (le_of_lt hUT)
    dsimp only
    rw [stoppedClockExtension_inverse_eq hGzero hGcont hGmono hle]
  rw [← hlimit]
  exact h.congr' (heq.mono fun _ hi => hi.symm)

end MatedCRT
