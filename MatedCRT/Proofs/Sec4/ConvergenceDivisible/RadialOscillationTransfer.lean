import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BetweenIntegerTimes

/-! # Measurable unit-interval oscillation events -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls MarkovProcess Topology
open scoped NNReal

/-- A countable dense family of times in the `n`th unit interval. -/
noncomputable def unitIntervalSample (n m : ℕ) : ℝ≥0 := by
  let _ : Nonempty (Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)) := ⟨⟨n, le_rfl, by simp⟩⟩
  exact (TopologicalSpace.denseSeq (Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)) m).1

/-- The unit-interval oscillation bound tested on countably many times. -/
def unitOscillationEvent (a : ℝ) : Set (ℝ≥0 → ℝ) :=
  {f | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
    |f (unitIntervalSample n m) - f (n : ℝ≥0)| ≤ a * n}

theorem measurableSet_unitOscillationEvent (a : ℝ) : MeasurableSet (unitOscillationEvent a) := by
  unfold unitOscillationEvent
  simp only [ofPred_exists, ofPred_forall]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro m
  exact measurableSet_le (((measurable_pi_apply (unitIntervalSample n m)).sub
    (measurable_pi_apply (n : ℝ≥0))).abs)
    measurable_const

/-- A continuous path satisfying the countable tests satisfies the bound at
every time in each sufficiently late unit interval. -/
theorem unitOscillationEvent.bound {a : ℝ} {f : ℝ≥0 → ℝ}
    (hf : Continuous f) (h : f ∈ unitOscillationEvent a) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0, (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |f t - f (n : ℝ≥0)| ≤ a * n := by
  obtain ⟨N, hN⟩ := h
  filter_upwards [eventually_ge_atTop N] with n hn t hnt htn
  let I := Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)
  let _ : Nonempty I := ⟨⟨n, le_rfl, by simp⟩⟩
  let x : I := ⟨t, hnt, htn⟩
  have hc : IsClosed {x : I | |f x.1 - f (n : ℝ≥0)| ≤ a * n} :=
    isClosed_le (((hf.comp continuous_subtype_val).sub continuous_const).abs) continuous_const
  have hbound : |f x.1 - f (n : ℝ≥0)| ≤ a * n :=
    (TopologicalSpace.denseRange_denseSeq I).induction_on
      (p := fun x : I => |f x.1 - f (n : ℝ≥0)| ≤ a * n) x hc (fun m => hN n hn m)
  exact hbound

/-- A Brownian unit-interval oscillation estimate transfers to the centered
circle-average radial process. -/
theorem IsQuantumCone.ae_radial_oscillation_of_brownian
    {Ω : Type} [MeasurableSpace Ω] {γ a : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc)
    (hB : ∀ᵐ w ∂brownianMotion 0, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ≥0, (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
        |w t - w (n : ℝ≥0)| ≤ a * n) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
      (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |(hcirc ω (Real.exp (-(t : ℝ))) 0 - γ * t) -
        (hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n)| ≤ a * n := by
  have hBe : ∀ᵐ w ∂brownianMotion 0, (fun t : ℝ≥0 => w t) ∈ unitOscillationEvent a := by
    filter_upwards [hB] with w hw
    obtain ⟨N, hN⟩ := eventually_atTop.mp hw
    refine ⟨N, fun n hn m => ?_⟩
    have hm : unitIntervalSample n m ∈ Icc (n : ℝ≥0) ((n : ℝ≥0) + 1) := by
      let _ : Nonempty (Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)) := ⟨⟨n, le_rfl, by simp⟩⟩
      exact (TopologicalSpace.denseSeq (Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)) m).2
    exact hN n hn _ hm.1 hm.2
  have hE := hcone.ae_radial_centered_of_brownian (measurableSet_unitOscillationEvent a) hBe
  filter_upwards [hE, hcone.ae_continuousOn_circle] with ω he hc
  have hf : Continuous (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0 - γ * t) := by
    have hpoint : Continuous (fun t : ℝ≥0 => (Real.exp (-(t : ℝ)), (0 : ℂ))) :=
      (Real.continuous_exp.comp NNReal.continuous_coe.neg).prodMk continuous_const
    have hcircle : Continuous (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) := by
      apply continuousOn_univ.mp
      exact hc.comp hpoint.continuousOn (fun t _ => ⟨Real.exp_pos _, mem_univ _⟩)
    exact hcircle.sub (continuous_const.mul NNReal.continuous_coe)
  exact unitOscillationEvent.bound hf he

/-- Brownian unit-interval oscillation bounds imply convergence-event
measurability through the cone radial law. -/
theorem convergenceDivisibleEventMeasurable_of_brownian_oscillation
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hB : ∀ a : ℝ, 0 < a → ∀ᵐ w ∂brownianMotion 0,
      ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
        (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
        |w t - w (n : ℝ≥0)| ≤ a * n) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_radial_oscillation 𝒮 h27 hscale hpos
  intro γ hγ hγ2 Ω _ S hS
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂S.P, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
      (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |(S.hcirc ω (Real.exp (-(t : ℝ))) 0 - γ * t) -
        (S.hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n)| ≤ (1 / ((k : ℝ) + 1)) * n := by
    intro k
    exact hS.isQuantumCone.ae_radial_oscillation_of_brownian (hB _ (by positivity))
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro ε hε
  obtain ⟨k, hkε⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn t hnt htn
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) hnt
  let u : ℝ≥0 := ⟨t, ht0⟩
  have hun : (n : ℝ≥0) ≤ u := by exact_mod_cast hnt
  have hnu : u ≤ (n : ℝ≥0) + 1 := by exact_mod_cast htn
  have hbound := hn u hun hnu
  have hmul : (1 / ((k : ℝ) + 1)) * n ≤ ε * n :=
    mul_le_mul_of_nonneg_right hkε.le (Nat.cast_nonneg n)
  exact hbound.trans hmul

end MatedCRT
