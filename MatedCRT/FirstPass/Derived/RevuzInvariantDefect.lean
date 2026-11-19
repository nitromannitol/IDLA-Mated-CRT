import MatedCRT.FirstPass.Derived.RevuzExcessive

/-!
# The defect of the Revuz measure under the time change

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock, Revuz measure
`μ = μ_A` and time-change kernels `P_u`. The Revuz measure is excessive, `μ P_h ≤ μ` (`bind_revuz_timeChangeKernel_le`),
so `μ P_h` has a density `ρ_h ≤ 1` with respect to the `σ`-finite measure `μ`, and the defect
`D_h = μ.withDensity (1 − ρ_h)` satisfies `μ = μ P_h + D_h` without any subtraction of measures.

Applying `P_t` and the semigroup property `(μ P_h) P_t = μ P_{h+t}` gives, for every Borel set `E`,
`(μ P_t)(E) = (μ P_{h+t})(E) + (D_h P_t)(E)`, and by induction
`(μ P_s)(E) = (μ P_{s+nh})(E) + ∑_{k<n} (D_h P_{s+kh})(E)`, so that `∑_{k<n} (D_h P_{s+kh})(E) ≤ μ(E)`.
This is the first half of the passage from excessive to invariant measures for a recurrent time change
(Azéma–Duflo–Revuz (1969), §§2–3; Revuz–Yor (1999), Chapter X, §3).

## Main results

* `revuzDefect`, `revuz_eq_bind_add_revuzDefect`: `μ = μ P_h + D_h`;
* `bind_timeChangeKernel_revuz_apply_eq`: `(μ P_t)(E) = (μ P_{h+t})(E) + (D_h P_t)(E)`;
* `bind_timeChangeKernel_revuz_apply_eq_add_sum`: the iterated identity;
* `sum_bind_timeChangeKernel_revuzDefect_le`: `∑_{k<n} (D_h P_{s+kh})(E) ≤ μ(E)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- The defect `D_h = μ_A − μ_A P_h` of the Revuz measure under the time change, written as `μ_A` with density
`1 − d(μ_A P_h)/dμ_A`. -/
noncomputable def revuzDefect (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℝ≥0) : Measure ℂ :=
  (revuz planarLaw A).withDensity
    (1 - (timeChangeKernel A h ∘ₘ revuz planarLaw A).rnDeriv (revuz planarLaw A))

/-- **`μ_A = μ_A P_h + D_h`.** -/
theorem revuz_eq_bind_add_revuzDefect {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (h : ℝ≥0) :
    revuz planarLaw A = timeChangeKernel A h ∘ₘ revuz planarLaw A + revuzDefect A h := by
  have := sigmaFinite_revuz hA hG
  have hle := bind_revuz_timeChangeKernel_le hA hG h
  have : SigmaFinite (timeChangeKernel A h ∘ₘ revuz planarLaw A) := Measure.sigmaFinite_of_le _ hle
  have hρ := Measure.rnDeriv_le_one_of_le hle
  calc revuz planarLaw A = (revuz planarLaw A).withDensity 1 := withDensity_one.symm
    _ = (revuz planarLaw A).withDensity
          ((timeChangeKernel A h ∘ₘ revuz planarLaw A).rnDeriv (revuz planarLaw A) +
            (1 - (timeChangeKernel A h ∘ₘ revuz planarLaw A).rnDeriv (revuz planarLaw A))) := by
        refine withDensity_congr_ae ?_
        filter_upwards [hρ] with x hx
        simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hx ⊢
        exact (add_tsub_cancel_of_le hx).symm
    _ = (revuz planarLaw A).withDensity
          ((timeChangeKernel A h ∘ₘ revuz planarLaw A).rnDeriv (revuz planarLaw A)) + revuzDefect A h :=
        withDensity_add_left (Measure.measurable_rnDeriv _ _) _
    _ = timeChangeKernel A h ∘ₘ revuz planarLaw A + revuzDefect A h := by
        rw [Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hle)]

/-- **One step**: `(μ_A P_t)(E) = (μ_A P_{h+t})(E) + (D_h P_t)(E)`. -/
theorem bind_timeChangeKernel_revuz_apply_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (h t : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E) :
    (timeChangeKernel A t ∘ₘ revuz planarLaw A) E =
      (timeChangeKernel A (h + t) ∘ₘ revuz planarLaw A) E + (timeChangeKernel A t ∘ₘ revuzDefect A h) E := by
  conv_lhs => rw [revuz_eq_bind_add_revuzDefect hA hG h]
  rw [comp_timeChangeKernel_add hA hG _ h t, Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _), Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_add_measure]

/-- **The iterated identity**: `(μ_A P_s)(E) = (μ_A P_{s+nh})(E) + ∑_{k<n} (D_h P_{s+kh})(E)`. -/
theorem bind_timeChangeKernel_revuz_apply_eq_add_sum {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (h s : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E)
    (n : ℕ) :
    (timeChangeKernel A s ∘ₘ revuz planarLaw A) E =
      (timeChangeKernel A (s + n * h) ∘ₘ revuz planarLaw A) E +
        ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ revuzDefect A h) E := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, bind_timeChangeKernel_revuz_apply_eq hA hG h (s + n * h) hE,
      show h + (s + n * h) = s + ((n + 1 : ℕ) : ℝ≥0) * h by push_cast; ring]
    ring

/-- **The defects of the time-shifted kernels sum below the Revuz mass**: `∑_{k<n} (D_h P_{s+kh})(E) ≤ μ_A(E)`. -/
theorem sum_bind_timeChangeKernel_revuzDefect_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (h s : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ revuzDefect A h) E ≤ revuz planarLaw A E :=
  calc ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ revuzDefect A h) E
      ≤ (timeChangeKernel A (s + n * h) ∘ₘ revuz planarLaw A) E +
          ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ revuzDefect A h) E := le_add_self
    _ = (timeChangeKernel A s ∘ₘ revuz planarLaw A) E :=
        (bind_timeChangeKernel_revuz_apply_eq_add_sum hA hG h s hE n).symm
    _ ≤ revuz planarLaw A E := Measure.le_iff'.1 (bind_revuz_timeChangeKernel_le hA hG s) E

end MatedCRT
