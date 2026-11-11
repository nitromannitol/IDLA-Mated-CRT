import MatedCRT.Proofs.Sec3.KilledOccupation.ClockExitLIntegral

/-!
# Measurability of a nested clock integral over `[0, σ]`

For a measurable family `κ` of measures on `ℝ≥0`, indexed by a parameter `a` and a path `b`
(the mass `κ (a, b) (Iic t)` is finite and measurable in `(a, b)`), and an s-finite measure `μ`
on the path space, the integral over `b` of the clock integrals over `[0, σ(b)]`, where
`σ = exitNN z r` is the exit time of the ball `ball z r`, is a measurable function of `a`.

The proof reduces to the Iic-kernel lemma `LatticeProb.measurable_lintegral_of_measurable_Iic`
on the parameter space `α × ContinuousPath ℂ`, followed by Tonelli for the s-finite measure `μ`
(`Measurable.lintegral_prod_right'`).
-/

noncomputable section

open MarkovProcess MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Measurability of the nested clock integral over `[0, σ]`.** Let `κ : α × ContinuousPath ℂ →
Measure ℝ≥0` with each `κ p (Iic t)` finite and measurable in `p`, let `μ` be an s-finite measure
on `ContinuousPath ℂ`, and let `q : ℂ → ℝ≥0∞` be measurable. Then for the exit time
`σ = exitNN z r` of `ball z r`, the map `a ↦ ∫⁻ b, ∫⁻ u in [0, σ(b)], q (b u) ∂(κ (a, b)) ∂μ`
is measurable. -/
theorem measurable_lintegral_setLIntegral_exitNN {α : Type*} [MeasurableSpace α]
    (κ : α × ContinuousPath ℂ → Measure ℝ≥0) (hfin : ∀ p t, κ p (Set.Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Set.Iic t))
    (μ : Measure (ContinuousPath ℂ)) [SFinite μ] (z : ℂ) (r : ℝ) (q : ℂ → ℝ≥0∞)
    (hq : Measurable q) :
    Measurable fun a => ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ (a, b)) ∂μ := by
  -- The set of (b, u) with u ≤ σ(b), and the integrand on it.
  let M : Set (ContinuousPath ℂ × ℝ≥0) := {p | p.2 ≤ exitNN z r p.1}
  have hM : MeasurableSet M :=
    measurableSet_le measurable_snd ((measurable_exitNN z r).comp measurable_fst)
  have hF : Measurable fun p : ContinuousPath ℂ × ℝ≥0 => M.indicator (fun p => q (p.1 p.2)) p :=
    (hq.comp measurable_eval_path_pair).indicator hM
  -- The same integrand, as a function of the parameter `x = (a, b)` and of `u`.
  have hG : Measurable fun x : (α × ContinuousPath ℂ) × ℝ≥0 =>
      M.indicator (fun p => q (p.1 p.2)) (x.1.2, x.2) :=
    hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  -- Pointwise: the clock integral over `[0, σ(b)]` against `κ (a, b)` is the integral of the
  -- indicator of `M` against the same measure.
  have hint : ∀ a : α, ∀ b : ContinuousPath ℂ,
      ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ (a, b)) =
        ∫⁻ u, M.indicator (fun p => q (p.1 p.2)) (b, u) ∂(κ (a, b)) := by
    intro a b
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    by_cases h : u ≤ exitNN z r b
    · rw [Set.indicator_of_mem (show u ∈ Icc (0 : ℝ≥0) (exitNN z r b) from ⟨zero_le, h⟩),
        Set.indicator_of_mem (show (b, u) ∈ M from h)]
    · rw [Set.indicator_of_notMem (show u ∉ Icc (0 : ℝ≥0) (exitNN z r b) from fun hh => h hh.2),
        Set.indicator_of_notMem (show (b, u) ∉ M from h)]
  -- Measurability of the inner integral in `x = (a, b)`: the Iic-kernel lemma.
  have hJ : Measurable fun x : α × ContinuousPath ℂ =>
      ∫⁻ u, M.indicator (fun p => q (p.1 p.2)) (x.2, u) ∂(κ x) :=
    LatticeProb.measurable_lintegral_of_measurable_Iic κ hfin hIic hG
  -- Tonelli for the s-finite measure `μ` on the path space.
  have hfun : (fun a => ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ (a, b)) ∂μ) =
      fun a => ∫⁻ b, (fun x : α × ContinuousPath ℂ =>
        ∫⁻ u, M.indicator (fun p => q (p.1 p.2)) (x.2, u) ∂(κ x)) (a, b) ∂μ :=
    funext fun a => lintegral_congr fun b => hint a b
  rw [hfun]
  exact Measurable.lintegral_prod_right' (ν := μ) hJ

end MatedCRT.KilledOccupation
