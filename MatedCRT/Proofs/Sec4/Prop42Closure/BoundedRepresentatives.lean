import MatedCRT.Proofs.Sec4.Prop42Closure.ScaledRegularizedFamily

/-! # Bounded representatives of the dilated subharmonic balls (Proposition 4.2, z5)

Task `z5-m5q-steps3-bounded-representatives-repair`. Written argument: `notes/wpn-steps3/steps3.tex`, lines 211-368:
the representative lemma `lem:bounded-jensen-representatives` (steps3:230-317) and the bounded repair
`prop:bounded-scaled-representatives` (steps3:319-368).

Proved here:
* `hasSubMeanValueProperty_scaled_boundedTestClass`: for a bounded-domain test function `f` of the dilated set
  `a⁻¹ Λ`, the sub-mean inequality for `scaledMeasure μ a c` on `a⁻¹ Λ` (steps3:340-368: the change of variables
  `F(y) = f(y/a)` into `T_b(Λ, 0)`, and the scaled mean-value transfer of `ScaledRegularizedFamily.lean`).
* `scaledBoundedRepresentativesStep_of_jensen`: the repaired `ScaledBoundedRepresentativesStep` (bounded `Λ`,
  steps3:319), from the representative lemma `BoundedJensenRepresentativesStep`. The mass identity
  `μ_a(a⁻¹ Λ) = c⁻¹ μ(Λ) ∈ (0, ∞)` and the boundedness and openness of `a⁻¹ Λ` are proved here.

Not proved here: `BoundedJensenRepresentativesStep` (steps3:230-317), carried as a named Step with its exact written
premises (bounded open `S`, `z ∈ S`, `0 < λ(S) < ∞`, sub-mean inequality on `T_b(S, z)`). Its written proof uses the local
Riesz decomposition of E. B. Saff (arXiv:1010.3760v1, Theorem 2.4), and the Green characterization (a')-(c') and (3.8),
staged in `MatedCRT/Proposed/Saff2010.lean`. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls InnerProductSpace
open scoped Pointwise ENNReal

/-- **Named Step: the bounded representative lemma (steps3:230-233).** Let `S` be bounded and open, `z ∈ S`, and
`0 < m S < ∞`. If the sub-mean inequality (eq:submean) holds for `m` on `S` for every bounded-domain test function of
`S` at `z`, then every subharmonic test function of `S` at `z` has a bounded-domain representative for `m`
(`HasBoundedSubharmonicRepresentatives`, HB `Audit/GreenSubharmonicTestClass.lean:48`).
Written proof: steps3:234-317 (potential localization, bounded approximation and the Green identification).
Consumer: `scaledBoundedRepresentativesStep_of_jensen`, which gives the repaired `ScaledBoundedRepresentativesStep`. -/
def BoundedJensenRepresentativesStep : Prop :=
  ∀ (m : Measure ℂ) (S : Set ℂ) (z : ℂ), IsOpen S → Bornology.IsBounded S → z ∈ S → 0 < m S → m S < ⊤ →
    (∀ f ∈ boundedSubharmonicBallTestClass S z, HasSubMeanValueProperty m S z f) →
    HasBoundedSubharmonicRepresentatives m S z

/-- **The sub-mean inequality on the bounded test class of the dilated set (steps3:340-368).** For a subharmonic ball
`Λ` of `μ` at `0` and `a, c > 0`, every `f ∈ T_b(a⁻¹ Λ, 0)` satisfies the sub-mean inequality for `μ_a = scaledMeasure μ a c`
on `a⁻¹ Λ`. Here `F(y) = f(y / a)` lies in `T_b(Λ, 0)` (`boundedSubharmonicBallTestClass_rescaled`), and the scaled
mean-value transfer is `hasSubMeanValueProperty_rescaledMeasure`. -/
theorem hasSubMeanValueProperty_scaled_boundedTestClass {μ : Measure ℂ} {Λ : Set ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : IsSubharmonicBall μ Λ 0) {f : ℂ → ℝ}
    (hf : f ∈ boundedSubharmonicBallTestClass ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0) :
    HasSubMeanValueProperty (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0 f := by
  obtain ⟨-, -, -, -, hmv⟩ := h
  rw [scaledMeasure_eq_rescaledMeasure μ hc]
  have hg := boundedSubharmonicBallTestClass_rescaled ha hf
  have hH := hmv _ (boundedSubharmonicBallTestClass_subset Λ 0 hg)
  have hT := hasSubMeanValueProperty_rescaledMeasure ha.ne' hc hH
  simpa only [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.2 ha.ne')] using hT

/-- **The repaired `ScaledBoundedRepresentativesStep`, from the bounded representative lemma.** For a bounded subharmonic
ball `Λ` of `μ` at `0`, the set `S = a⁻¹ Λ` is open, bounded and contains `0`, and `μ_a(S) = c⁻¹ μ(Λ)` lies in `(0, ∞)`
(`rescaledMeasure_preimage`). The sub-mean inequality on `T_b(S, 0)` is
`hasSubMeanValueProperty_scaled_boundedTestClass`. The named representative lemma `hJ` then gives the representatives.
The input is the representative lemma itself, not the repaired Step. -/
theorem scaledBoundedRepresentativesStep_of_jensen (hJ : BoundedJensenRepresentativesStep) :
    ScaledBoundedRepresentativesStep := by
  intro μ Λ a c ha hc hΛ hbd
  have hR0 : a ≠ 0 := ha.ne'
  have hRc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  refine hJ (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0
    (hΛ.1.preimage (continuous_const.mul continuous_id)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨R, hR⟩ := hbd.subset_closedBall (0 : ℂ)
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R / a)).subset ?_
    intro x hx
    have hΛx : (a : ℂ) * x ∈ Λ := hx
    have hx' : (a : ℂ) * x ∈ closedBall (0 : ℂ) R := hR hΛx
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le] at hx'
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ ha]
    linarith [mul_comm ‖x‖ a]
  · show (a : ℂ) * 0 ∈ Λ
    rw [mul_zero]
    exact hΛ.2.1
  · rw [scaledMeasure_eq_rescaledMeasure μ hc, rescaledMeasure_preimage μ hR0 c Λ]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne' hΛ.2.2.1.ne'
  · rw [scaledMeasure_eq_rescaledMeasure μ hc, rescaledMeasure_preimage μ hR0 c Λ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ.2.2.2.1
  · intro f hf
    exact hasSubMeanValueProperty_scaled_boundedTestClass ha hc hΛ hf

end MatedCRT
