import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppingTime

/-! # Stopped cone families stay inside the half ball before the stopping time

The stopping-time test of `StoppingTime.lean` (`halfBallTest_iff_lt`) uses strict growth only through the closure
containment `closure (Λ q) ⊆ ball 0 (1/2)` for rational `q < T`. This file isolates that weaker input,
`ConeHalfBallClosureInsideStep`, shows that `ConeHarmonicBallStrictGrowthStep` implies it, and proves the
stopping-test equivalence under the weaker input. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- Closure containment before the stopping time: almost surely, every family `{Λ_t}_{0 < t < T}` of the cone
with the properties of Lemma 2.4 satisfies `closure (Λ_t) ⊆ B_{1/2}` for `0 < t < T`. Not stated in the paper;
implied by `ConeHarmonicBallStrictGrowthStep`. -/
def ConeHalfBallClosureInsideStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T → IsStoppedAtHalfBall Λ T →
      ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2)

/-- Strict growth gives closure containment before the stopping time: for `0 < t < T`, pick `t < t' < T`, then
`cl Λ_t ⊆ Λ_{t'} ⊆ B_{1/2}`. -/
theorem coneHalfBallClosureInsideStep_of_strictGrowth (hgrow : ConeHarmonicBallStrictGrowthStep) :
    ConeHalfBallClosureInsideStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
  intro T Λ hΛ hs t ht
  obtain ⟨t', htt', ht'T⟩ := exists_between ht.2
  have h1 : closure (Λ t) ⊆ Λ t' := hω T Λ hΛ t t' ht.1 htt' ht'T
  have h2 : Λ t' ⊆ ball (0 : ℂ) (1 / 2) := hs.1 t' ⟨ht.1.trans htt', ht'T⟩
  exact h1.trans h2

/-- The stopping test `halfBallTest` of an open monotone family with the stopped family `Λ` before `T` is
equivalent to `q < T`, using only closure containment before `T` (not full strict growth): the direction
`q < T ⇒ test` is the only place where the closure input is used. -/
theorem halfBallTest_iff_lt_of_closure {C : Ioi (0 : ℝ) → Set ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (ho : ∀ t, IsOpen (C t)) (hm : Monotone C)
    (heq : ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t)
    (hs : IsStoppedAtHalfBall Λ T) (hcl : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2))
    (q : PositiveRational) : halfBallTest (C ⟨q, q.property⟩) ↔ (q : ℝ) < T := by
  constructor
  · rintro ⟨r, hr, htest⟩
    by_contra hq
    have hTq : T ≤ (q : ℝ) := le_of_not_gt hq
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    obtain ⟨t, ht, hx⟩ := hs.2 r' hr'
    have hsub := (closure_subset_closedBall_of_halfBallTest (ho ⟨q, q.property⟩) htest)
    apply hx
    intro x hxΛ
    have hxC : x ∈ C ⟨t, ht.1⟩ := by rwa [heq t ht]
    have hxq := (hm (show (⟨t, ht.1⟩ : Ioi (0 : ℝ)) ≤ ⟨q, q.property⟩ from
      le_of_lt (ht.2.trans_le hTq))) hxC
    have hdist : dist x 0 ≤ (r : ℝ) := hsub (subset_closure hxq)
    exact hdist.trans_lt hrr'
  · intro hq
    have hcl' : closure (Λ (q : ℝ)) ⊆ ball (0 : ℂ) (1 / 2) := hcl (q : ℝ) ⟨q.property, hq⟩
    obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball isClosed_closure hcl'
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    refine ⟨r', hr', fun n hn => ?_⟩
    rw [heq q ⟨q.property, hq⟩] at hn
    exact le_of_lt ((hsub (subset_closure hn)).trans hrr')

end MatedCRT
