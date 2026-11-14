import MatedCRT.FirstPass.Derived.BrownianTwoTimeSmallBall
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockExitLIntegral
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# Two-point small-ball bound for the occupation measure of killed planar Brownian motion

Let `b` be a planar Brownian motion started at `y`, `τ = exitNN z r b` its exit time of the disc
`B(z, r)`, and `μ_τ = lebNN|[0, τ]` the Lebesgue measure on the time interval before the exit. For
`a ≥ 0` and `θ ∈ [0, 1]`,

`E_y[(μ_τ ⊗ μ_τ){(u, v) | ‖b u - b v‖ < a}] ≤ ∫∫ (q ^ (⌊max u v⌋₊ - 1)) ^ θ · (a ² / |u - v|) ^ (1 - θ) du dv`,

with `q = unitIncrementStayProb r < 1`. This is the Tonelli step of the two-point estimate for the
occupation measure `b_* μ_τ` of the killed Brownian motion: the expectation of the product measure of
the event is the time integral of its probability, the diagonal `u = v` is null, and off the diagonal
the two-time bound `planarBrownianMotion_twoTime_norm_sub_lt_le` applies.

* `twoTimeEvent`, `measurableSet_twoTimeEvent`: the event `u ≤ τ, v ≤ τ, ‖b u - b v‖ < a`, jointly
  measurable in the path and the pair of times.
* `lebNN_prod_diagonal`: the diagonal of `ℝ≥0 × ℝ≥0` is `lebNN ⊗ lebNN`-null.
* `lintegral_occupation_prod_norm_sub_lt_le`: the bound above.
-/

open MeasureTheory Set Metric MarkovProcess ProbabilityTheory HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The event that both times `u, v` precede the exit time of `B(z, r)` and `‖b u - b v‖ < a`, as a set
of triples `(b, (u, v))`. -/
def twoTimeEvent (z : ℂ) (r a : ℝ) : Set (ContinuousPath ℂ × (ℝ≥0 × ℝ≥0)) :=
  {q | q.2.1 ≤ exitNN z r q.1 ∧ q.2.2 ≤ exitNN z r q.1 ∧ ‖q.1 q.2.1 - q.1 q.2.2‖ < a}

theorem mem_twoTimeEvent (z : ℂ) (r a : ℝ) (q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0)) :
    q ∈ twoTimeEvent z r a ↔
      q.2.1 ≤ exitNN z r q.1 ∧ q.2.2 ≤ exitNN z r q.1 ∧ ‖q.1 q.2.1 - q.1 q.2.2‖ < a :=
  Iff.rfl

/-- The two-time event is jointly measurable in the path and the pair of times. -/
theorem measurableSet_twoTimeEvent (z : ℂ) (r a : ℝ) : MeasurableSet (twoTimeEvent z r a) := by
  have hτ : Measurable fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) => exitNN z r q.1 :=
    (measurable_exitNN z r).comp measurable_fst
  have h1 : Measurable fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) => q.1 q.2.1 :=
    measurable_eval_path_pair.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) => q.1 q.2.2 :=
    measurable_eval_path_pair.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (measurableSet_le (measurable_fst.comp measurable_snd) hτ).inter
    ((measurableSet_le (measurable_snd.comp measurable_snd) hτ).inter
      (measurableSet_lt (h1.sub h2).norm measurable_const))

/-- The diagonal of `ℝ≥0 × ℝ≥0` is null for the product Lebesgue measure. -/
theorem lebNN_prod_diagonal : (lebNN.prod lebNN) {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} = 0 := by
  have hD : MeasurableSet {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have h : ∀ x : ℝ≥0, Prod.mk x ⁻¹' {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} = {x} := fun x => by
    ext v
    exact eq_comm
  rw [Measure.prod_apply hD]
  simp_rw [h, lebNN_singleton, lintegral_zero]

/-- **Two-point small-ball bound for the occupation measure of killed planar Brownian motion.** For
`a ≥ 0` and `θ ∈ [0, 1]`, with `τ = exitNN z r b` and `q = unitIncrementStayProb r`,
`E_y[(lebNN|[0, τ] ⊗ lebNN|[0, τ]){‖b u - b v‖ < a}]` is at most the `lebNN ⊗ lebNN` integral of
`(q ^ (⌊max u v⌋₊ - 1)) ^ θ · (a ² / |u - v|) ^ (1 - θ)`. -/
theorem lintegral_occupation_prod_norm_sub_lt_le (z y : ℂ) (r : ℝ) {a : ℝ} (ha : 0 ≤ a) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫⁻ b, ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
        {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < a} ∂planarBrownianMotion y ≤
      ∫⁻ p : ℝ≥0 × ℝ≥0, (unitIncrementStayProb r ^ (⌊max p.1 p.2⌋₊ - 1)) ^ θ *
        ENNReal.ofReal (a ^ 2 / |(p.1 : ℝ) - p.2|) ^ (1 - θ) ∂(lebNN.prod lebNN) := by
  have hF := measurableSet_twoTimeEvent z r a
  have hsec : ∀ b : ContinuousPath ℂ,
      ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
        {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < a} = (lebNN.prod lebNN) (Prod.mk b ⁻¹' twoTimeEvent z r a) := by
    intro b
    rw [Measure.prod_restrict, Measure.restrict_apply' (measurableSet_Icc.prod measurableSet_Icc)]
    congr 1
    ext p
    rw [Set.mem_preimage, mem_twoTimeEvent]
    constructor
    · rintro ⟨h, ⟨-, h1⟩, ⟨-, h2⟩⟩
      exact ⟨h1, h2, h⟩
    · rintro ⟨h1, h2, h⟩
      exact ⟨h, ⟨zero_le, h1⟩, ⟨zero_le, h2⟩⟩
  have hswap : ∫⁻ b, (lebNN.prod lebNN) (Prod.mk b ⁻¹' twoTimeEvent z r a) ∂planarBrownianMotion y =
      ∫⁻ p, planarBrownianMotion y ((fun b => (b, p)) ⁻¹' twoTimeEvent z r a) ∂(lebNN.prod lebNN) := by
    rw [← Measure.prod_apply hF, Measure.prod_apply_symm hF]
  simp_rw [hsec]
  rw [hswap]
  refine lintegral_mono_ae ?_
  have hdiag : ∀ᵐ p ∂(lebNN.prod lebNN), p ∉ {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} :=
    measure_eq_zero_iff_ae_notMem.1 lebNN_prod_diagonal
  filter_upwards [hdiag] with p hp
  exact planarBrownianMotion_twoTime_norm_sub_lt_le z y r hp ha hθ0 hθ1

end MatedCRT.KilledOccupation
