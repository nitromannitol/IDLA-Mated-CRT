import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapScaling
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapTonelli

/-! Fixed-time regularization defects under exponential mass shifts. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- A compactly confined raw obstacle cluster differs from its regularization. -/
def confinedRegularizationDefect (ρ t : ℝ) (z : ℂ) : Set (Measure ℂ) :=
  {μ | closure (cluster μ ρ z t) ⊆ ball 0 ρ ∧
    interior (closure (cluster μ ρ z t)) ≠ cluster μ ρ z t}

/-- The fixed-time regularization defect is null when comparison holds almost
surely, the defect event is jointly measurable under mass shifts, and the
unshifted measure law is absolutely continuous with respect to every shifted
measure law. -/
theorem ae_no_regularization_defect_of_shifted_measure_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) {ρ t γ : ℝ} {z : ℂ} (ht : 0 < t) (hγ : γ ≠ 0)
    (hopen : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → IsOpen (cluster (μ ω) ρ z s))
    (hcompare : ∀ᵐ ω ∂P, ∀ s u : ℝ, 0 < s → s < u →
      closure (cluster (μ ω) ρ z u) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z s)) ⊆ cluster (μ ω) ρ z u)
    (hB : MeasurableSet (confinedRegularizationDefect ρ t z))
    (hY : ∀ c : ℝ, AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • μ ω) P)
    (hjoint : MeasurableSet {p : Ω × ℝ |
      ENNReal.ofReal (Real.exp (γ * p.2)) • μ p.1 ∈ confinedRegularizationDefect ρ t z})
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) • μ ω) P ≪
        Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • μ ω) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  have hcount : ∀ᵐ ω ∂P, {c : ℝ |
      ENNReal.ofReal (Real.exp (γ * c)) • μ ω ∈ confinedRegularizationDefect ρ t z}.Countable := by
    filter_upwards [hopen, hcompare] with ω ho hc
    exact countable_regularization_defect_shifts_of_comparison ht hγ ho hc
  have hnull := ae_no_defect_of_shifted_law P
    (fun c ω => ENNReal.ofReal (Real.exp (γ * c)) • μ ω)
    (confinedRegularizationDefect ρ t z) hB hY hjoint hcount hlaw
  filter_upwards [hnull] with ω hω hcompact
  have hω' : μ ω ∉ confinedRegularizationDefect ρ t z := by
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] using hω
  by_contra hne
  exact hω' ⟨hcompact, hne⟩

end MatedCRT
