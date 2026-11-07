import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockInverse
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseConvergence

/-! # Convergence of killed clock inverses -/

namespace MatedCRT

open Filter HarmonicBalls MarkovProcess Topology
open scoped ENNReal NNReal

/-- Before the terminal clock value, pointwise convergence of strictly
increasing clocks gives convergence of their killed inverses. The
approximating clocks need not have infinite lifetime. -/
theorem tendsto_killedClockInverse_of_pointwise
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hG : IsTimeChangeClock G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t)))
    {τ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ) < G τ.toNNReal) :
    Tendsto (fun i => killedClockInverse (F i) τ t) l
      (𝓝 (killedClockInverse G τ t)) := by
  have hevent : ∀ᶠ i in l, (t : ℝ) < F i τ.toNNReal :=
    (tendsto_order.1 (hconv τ.toNNReal)).1 _ ht
  have hinv := tendsto_clockInverse_of_pointwise hmono hG hconv t
  have hcast : Tendsto (fun i => (clockInverse (F i) t : ℝ≥0∞)) l
      (𝓝 (clockInverse G t : ℝ≥0∞)) := ENNReal.tendsto_coe.2 hinv
  have hmin : Tendsto (fun i => min τ (clockInverse (F i) t : ℝ≥0∞)) l
      (𝓝 (min τ (clockInverse G t : ℝ≥0∞))) := tendsto_const_nhds.min hcast
  rw [killedClockInverse_eq_min_clockInverse ⟨τ.toNNReal, ht⟩]
  apply hmin.congr'
  filter_upwards [hevent] with i hi
  rw [killedClockInverse_eq_min_clockInverse ⟨τ.toNNReal, hi⟩]

/-- Continuous paths composed with killed inverses converge before the
terminal clock value when the killing time is finite. -/
theorem tendsto_path_killedClockInverse_of_pointwise
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hmono : ∀ i, StrictMono (F i)) (hG : IsTimeChangeClock G)
    (hconv : ∀ t, Tendsto (fun i => F i t) l (𝓝 (G t)))
    (b : ContinuousPath ℂ) {τ : ℝ≥0∞} (hτ : τ < ⊤) {t : ℝ≥0}
    (ht : (t : ℝ) < G τ.toNNReal) :
    Tendsto (fun i => b ((killedClockInverse (F i) τ t).toNNReal)) l
      (𝓝 (b ((killedClockInverse G τ t).toNNReal))) := by
  have hfin : killedClockInverse G τ t ≠ ⊤ :=
    ne_of_lt ((killedClockInverse_le_exit G τ t).trans_lt hτ)
  exact b.continuous.continuousAt.tendsto.comp
    ((ENNReal.tendsto_toNNReal hfin).comp
      (tendsto_killedClockInverse_of_pointwise hmono hG hconv ht))

/-- Convergence only up to a finite stopping time suffices for convergence
of the time-changed path before the terminal clock value. -/
theorem tendsto_path_killedClockInverse_of_local_pointwise
    {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hzero : ∀ i, F i 0 = 0) (hcont : ∀ i, Continuous (F i))
    (hmono : ∀ i, StrictMono (F i)) (hG : IsTimeChangeClock G) (T : ℝ≥0)
    (hconv : ∀ s ≤ T, Tendsto (fun i => F i s) l (𝓝 (G s)))
    (b : ContinuousPath ℂ) {t : ℝ≥0} (ht : (t : ℝ) < G T) :
    Tendsto (fun i => b ((killedClockInverse (F i) T t).toNNReal)) l
      (𝓝 (b ((killedClockInverse G T t).toNNReal))) := by
  let E : ι → ℝ≥0 → ℝ := fun i => stoppedClockExtension (F i) T
  let H : ℝ≥0 → ℝ := stoppedClockExtension G T
  have hE : ∀ i, StrictMono (E i) := fun i =>
    (stoppedClockExtension_isTimeChangeClock T (hzero i) (hcont i) (hmono i)).strictMono
  have hH : IsTimeChangeClock H :=
    stoppedClockExtension_isTimeChangeClock T hG.map_zero hG.continuous hG.strictMono
  have hconv' : ∀ s, Tendsto (fun i => E i s) l (𝓝 (H s)) := by
    intro s
    simpa [E, H, stoppedClockExtension] using
      (hconv (min s T) (min_le_right _ _)).add_const (max ((s : ℝ) - T) 0)
  have ht' : (t : ℝ) < H ((T : ℝ≥0∞).toNNReal) := by
    simpa [H, stoppedClockExtension_eq le_rfl] using ht
  have h := tendsto_path_killedClockInverse_of_pointwise hE hH hconv' b
    (show (T : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) ht'
  have heq : ∀ i, killedClockInverse (E i) T t = killedClockInverse (F i) T t := by
    intro i
    apply killedClockInverse_eq_of_agree_before
    intro s hs
    exact stoppedClockExtension_eq hs
  have heq' : killedClockInverse H T t = killedClockInverse G T t := by
    apply killedClockInverse_eq_of_agree_before
    intro s hs
    exact stoppedClockExtension_eq hs
  simpa only [heq, heq'] using h

end MatedCRT

#print axioms MatedCRT.tendsto_killedClockInverse_of_pointwise
#print axioms MatedCRT.tendsto_path_killedClockInverse_of_pointwise
#print axioms MatedCRT.tendsto_path_killedClockInverse_of_local_pointwise
