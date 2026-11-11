import MatedCRT.Proofs.LBM.AlmostSureRegularExit
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.FirstPass.S3t.Defs

/-!
# Truncated quenched laws, Step 4: almost-sure regular exit of the limiting LBM

Step 4 of the truncated-laws argument (section 3). For almost every environment and almost every
Brownian path `b` from `y`, the rescaled Liouville Brownian motion `rescaledLBMPath (S.clock ω) S.m₀ b` exits the disk
`ball z r` regularly. The proof is the existing transfer of Brownian radial excursions to LBM regular exits
(`MatedCRTEnv.IsValid.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion`,
`MatedCRT/Proofs/LBM/AlmostSureRegularExit.lean`), applied to `BrownianOutwardExcursionAtExitStep`.

`RegularExit` is the regular-exit predicate of Berestycki–Gwynne and Mörters–Peres (Theorem 2.16 and Theorem 2.8): the
path either never exits `D`, or it leaves the closure of `D` at arbitrarily small positive times after its exit time.
The answer's Step 4 omits the hypothesis `y ∈ ball z r`, which the existing transfer lemma needs, so it is kept. The
positivity `0 < S.m₀` of the transfer lemma is removed: for `S.m₀ ≤ 0` the rescaled path is constant (`clockInverse f 0 = 0`),
hence never leaves the disk and has exit time `⊤` (answer 47(d) §5, l.221-255). `IsValid` is not changed.
-/

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- Regular exit of the path `w` from the disk-like set `D`: either `D` is never exited, or after the exit time `τ_D(w)`
the path is outside the closure of `D` at arbitrarily small positive times (Frequently in `𝓝[>] τ_D(w)`). -/
def RegularExit (D : Set ℂ) (w : ℝ≥0 → ℂ) : Prop :=
  pathExitTime D w = ⊤ ∨ ∃ᶠ t in 𝓝[>] (pathExitTime D w).toNNReal, w t ∉ closure D

/-- A path that stays in `U` for all times has exit time `⊤`. -/
lemma pathExitTime_eq_top_of_forall_mem {U : Set ℂ} {f : ℝ≥0 → ℂ} (h : ∀ t, f t ∈ U) :
    pathExitTime U f = ⊤ := by
  unfold pathExitTime
  have hempty : {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ f t ∉ U} = ∅ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, _, ht⟩
    exact ht (h t)
  rw [hempty, sInf_empty]

/-- For a nonpositive mass `m ≤ 0` and a time-change clock `F b`, the rescaled path is constant at `b 0`:
`clockInverse (F b) 0 = 0`. -/
lemma rescaledLBMPath_const_of_nonpos {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {m : ℝ} (hm : m ≤ 0)
    {b : ContinuousPath ℂ} (hF : IsTimeChangeClock (F b)) (t : ℝ≥0) :
    rescaledLBMPath F m b t = b 0 := by
  have h0 : m.toNNReal = 0 := Real.toNNReal_eq_zero.mpr hm
  have hI : clockInverse (F b) 0 = 0 := by
    have h := clockInverse_clockValue hF.map_zero hF.strictMono 0
    simpa only [hF.map_zero, Real.toNNReal_zero] using h
  simp only [rescaledLBMPath, liouvilleBrownianPath, h0, zero_mul, hI]

/-- Step 4 without the positivity of the mass: almost surely, the limiting rescaled LBM from `y ∈ ball z r` exits
`ball z r` regularly, for almost every Brownian path from `y`. For `S.m₀ ≤ 0` the path is constant at `y`. -/
theorem ae_regularExit_rescaledLBM_noMassHyp {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {y z : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    (hexit : BrownianOutwardExcursionAtExitStep) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      RegularExit (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
  by_cases hm : 0 < S.m₀
  · filter_upwards [MatedCRTEnv.IsValid.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hS hm hy
      (hexit y z r hy)] with ω hω
    filter_upwards [hω] with b hb
    exact Or.inr hb
  · filter_upwards [hS.isLQGClock] with ω hω
    filter_upwards [(hω y).2, ae_planarBrownianMotion_eval_zero y] with b hb hb0
    refine Or.inl (pathExitTime_eq_top_of_forall_mem fun t => ?_)
    rw [rescaledLBMPath_const_of_nonpos (not_lt.1 hm) hb t, hb0]
    exact hy

/-- Step 4 (previous signature, kept so that existing callers still build): the positivity `0 < S.m₀` is not used.
Callers should switch to `ae_regularExit_rescaledLBM_noMassHyp`. -/
theorem ae_regularExit_rescaledLBM {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (_hm : 0 < S.m₀) {y z : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    (hexit : BrownianOutwardExcursionAtExitStep) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      RegularExit (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) :=
  ae_regularExit_rescaledLBM_noMassHyp hS hy hexit

#print axioms ae_regularExit_rescaledLBM_noMassHyp
#print axioms ae_regularExit_rescaledLBM

end MatedCRT.TruncatedLaws
