import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CompactTestInequalities
import HarmonicBalls.Steps.SecA.Basic
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EventMeasurabilityReduction

/-! # The least supersolution outside its domain -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls

/-- Because the ambient Lean functions are unconstrained off the closed ball,
their values there are unbounded below and the real infimum has junk value zero. -/
theorem leastSupersolution_eq_zero_of_notMem_closedBall
    (μ : Measure ℂ) (r t : ℝ) (z x : ℂ) (ht : 0 ≤ t)
    (hx : x ∉ closedBall 0 r) : leastSupersolution μ r z t x = 0 := by
  classical
  have hzero := zero_mem_supersolutions μ r z ht
  have hmem (a : ℝ) : Function.update (0 : ℂ → ℝ) x a ∈ supersolutions μ r z t := by
    let w := Function.update (0 : ℂ → ℝ) x a
    have heq : EqOn (0 : ℂ → ℝ) w (closedBall 0 r) := by
      intro y hy
      have hyx : y ≠ x := fun h => hx (h ▸ hy)
      simp [w, Function.update_of_ne hyx]
    refine ⟨hzero.1.congr heq.symm,
      hzero.2.1.congr_eqOn measurableSet_ball (heq.mono ball_subset_closedBall), ?_⟩
    intro y hy hyz
    change -t * greenFunction (ball 0 r) z y ≤ w y
    rw [← heq hy]
    exact hzero.2.2 y hy hyz
  have hunbounded : ¬ BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z t) := by
    rintro ⟨b, hb⟩
    have h : b ≤ b - 1 := hb ⟨Function.update (0 : ℂ → ℝ) x (b - 1), hmem _, by simp⟩
    linarith
  exact Real.sInf_of_not_bddBelow hunbounded

/-- The least supersolution vanishes on the boundary when its pole is inside
the ball, by the zero boundary values of its Green obstacle. -/
theorem leastSupersolution_eq_zero_of_mem_sphere_direct
    (μ : Measure ℂ) (r t : ℝ) (z x : ℂ) (ht : 0 ≤ t)
    (hz : z ∈ ball 0 r) (hx : x ∈ sphere (0 : ℂ) r) :
    leastSupersolution μ r z t x = 0 := by
  have hxnot : x ∉ ball (0 : ℂ) r := by
    intro h
    rw [mem_sphere] at hx
    rw [mem_ball] at h
    linarith
  have hxz : x ≠ z := fun h => hxnot (h ▸ hz)
  have hclosed : x ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall hx
  apply le_antisymm (leastSupersolution_nonpos (μ := μ) ht hclosed hxz)
  have h := le_leastSupersolution (μ := μ) ht hclosed hxz
  simpa [greenFunction_of_notMem_right hxnot z] using h

/-- The convergence-event measurability reduction needs continuum pointwise
measurability only on the closed ball. -/
theorem convergenceDivisibleEventMeasurable_of_pointwise_on_closedBall
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r t : ℝ), 0 < r → 0 < t → ∀ z ∈ closedBall (0 : ℂ) r,
        AEMeasurable (fun ω => leastSupersolution (S.μ ω) r 0 t z) S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_pointwise 𝒮 hcell
  intro γ hγ hγ' Ω _ S hS r t hr ht z
  by_cases hz : z ∈ closedBall (0 : ℂ) r
  · exact hpoint γ hγ hγ' Ω S hS r t hr ht z hz
  · have heq : (fun ω => leastSupersolution (S.μ ω) r 0 t z) = fun _ => 0 := by
      funext ω
      exact leastSupersolution_eq_zero_of_notMem_closedBall (S.μ ω) r t 0 z ht.le hz
    rw [heq]
    exact aemeasurable_const

/-- Pointwise measurability in the open ball and adjacent-cell intersection
imply convergence-event measurability. -/
theorem convergenceDivisibleEventMeasurable_of_pointwise_on_ball
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r t : ℝ), 0 < r → 0 < t → ∀ z ∈ ball (0 : ℂ) r,
        AEMeasurable (fun ω => leastSupersolution (S.μ ω) r 0 t z) S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_pointwise_on_closedBall 𝒮 hcell
  intro γ hγ hγ' Ω _ S hS r t hr ht z hz
  by_cases hzb : z ∈ ball (0 : ℂ) r
  · exact hpoint γ hγ hγ' Ω S hS r t hr ht z hzb
  · have hzs : z ∈ sphere (0 : ℂ) r := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hz, hzb⟩
    have heq : (fun ω => leastSupersolution (S.μ ω) r 0 t z) = fun _ => 0 := by
      funext ω
      exact leastSupersolution_eq_zero_of_mem_sphere_direct (S.μ ω) r t 0 z ht.le
        (mem_ball_self hr) hzs
    rw [heq]
    exact aemeasurable_const

end MatedCRT
