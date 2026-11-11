import MatedCRT.FirstPass.S2g
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfConeFamily

/-! # Draft Lemma 2.4 and Proposition 6.1 from the canonical step and the closure step

The Section 6 chain (`Proofs/Sec6/IDLAUpperBound/OfConeFamily.lean:16`) takes the Draft statement
`ConeHarmonicBallsUpToFixedTimeStmt` (`Draft/Section2.lean:66-72`), whose clause `T' = T` says that the stopping time is
unique among all stopped families. That clause is derived here, not assumed: with the closure containment of every stopped
family (`ConeHalfBallClosureInsideStep`, a.s., `Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18`), two stopped
families on the same measure have the same stopping time (`stopped_unique_of_closureInside_fp` below, a copy of the S2b lemma), and
the fixed-time uniqueness gives the family. The existence part is the canonical step `ConeCanonicalHalfBallStep`
(OPEN, `FirstPass/S2g.lean`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

/-- Closure route, one inequality (copy of `stopped_le_of_closureInside`, `FirstPass/S2b.lean`, under a new name so that
this module does not import `FirstPass/S2b.lean`, whose import clashes with the Section 6 chain). -/
theorem stopped_le_of_closureInside_fp {Λ Λ' : ℝ → Set ℂ} {T T' : ℝ} (hT : 0 < T)
    (h : IsStoppedAtHalfBall Λ T) (hmono : MonotoneOn Λ' (Ioo 0 T'))
    (heq : EqOn Λ Λ' (Ioo 0 (min T T'))) (hcl : ∀ s ∈ Ioo 0 T', closure (Λ' s) ⊆ ball (0 : ℂ) (1 / 2)) :
    T' ≤ T := by
  by_contra hlt
  rw [not_le] at hlt
  set s : ℝ := (T + T') / 2 with hs_def
  have hTs : T < s := by rw [hs_def]; linarith
  have hs : s ∈ Ioo 0 T' := ⟨by linarith, by rw [hs_def]; linarith⟩
  have key : ∀ r : ℝ, r < 1 / 2 → ∃ x ∈ Λ' s, r ≤ ‖x‖ := by
    intro r hr
    obtain ⟨u, hu, hnot⟩ := h.2 r hr
    have hu' : u ∈ Ioo 0 T' := ⟨hu.1, hu.2.trans hlt⟩
    have hΛu : Λ u = Λ' u := heq ⟨hu.1, lt_min hu.2 (hu.2.trans hlt)⟩
    have hsub : Λ u ⊆ Λ' s := by
      rw [hΛu]
      exact hmono hu' hs (le_of_lt (hu.2.trans hTs))
    rw [Set.not_subset] at hnot
    obtain ⟨x, hxu, hxr⟩ := hnot
    refine ⟨x, hsub hxu, ?_⟩
    rw [mem_ball_zero_iff, not_lt] at hxr
    exact hxr
  have hK : IsCompact (closure (Λ' s)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (Metric.isBounded_ball.subset (hcl s hs))
  obtain ⟨x1, hx1, -⟩ := key 0 (by norm_num)
  obtain ⟨x0, hx0, hmax⟩ := hK.exists_isMaxOn ⟨x1, subset_closure hx1⟩ continuous_norm.continuousOn
  have hx0' : ‖x0‖ < 1 / 2 := mem_ball_zero_iff.1 (hcl s hs hx0)
  obtain ⟨x, hx, hxr⟩ := key ((‖x0‖ + 1 / 2) / 2) (by linarith)
  have h1 : ‖x‖ ≤ ‖x0‖ := isMaxOn_iff.1 hmax x (subset_closure hx)
  linarith

/-- Closure route, uniqueness of the stopping time (copy of `stopped_unique_of_closureInside`, `FirstPass/S2b.lean`). -/
theorem stopped_unique_of_closureInside_fp {Λ Λ' : ℝ → Set ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (h : IsStoppedAtHalfBall Λ T) (h' : IsStoppedAtHalfBall Λ' T')
    (hmono : MonotoneOn Λ (Ioo 0 T)) (hmono' : MonotoneOn Λ' (Ioo 0 T'))
    (heq : EqOn Λ' Λ (Ioo 0 (min T T')))
    (hcl : ∀ s ∈ Ioo 0 T, closure (Λ s) ⊆ ball (0 : ℂ) (1 / 2))
    (hcl' : ∀ s ∈ Ioo 0 T', closure (Λ' s) ⊆ ball (0 : ℂ) (1 / 2)) : T = T' := by
  have h1 : T' ≤ T := stopped_le_of_closureInside_fp hT h hmono' heq.symm hcl'
  have h2 : T ≤ T' := stopped_le_of_closureInside_fp hT' h' hmono (by rw [min_comm]; exact heq) hcl
  exact le_antisymm h2 h1

/-- **Draft Lemma 2.4 from the canonical step and the closure step.** The stopping time `T = halfBallTime`
of the canonical family is the stopping time of every stopped family on the same measure, and every such family agrees
with the canonical one on `(0, T)`. -/
theorem coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) : ConeHarmonicBallsUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone, hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω hcl'
  obtain ⟨Λ, hT, hΛ, hst⟩ := hω
  refine ⟨halfBallTime (μ ω), hT, Λ, hΛ, hst, fun T' Λ' hT' hΛ' hst' => ?_⟩
  have hTT : halfBallTime (μ ω) = T' :=
    stopped_unique_of_closureInside_fp hT hT' hst hst' hΛ.2.1.monotoneOn hΛ'.2.1.monotoneOn (hΛ.eqOn hΛ')
      (hcl' _ _ hΛ hst) (hcl' _ _ hΛ' hst')
  refine ⟨hTT.symm, ?_⟩
  have heq := hΛ.eqOn hΛ'
  rw [hTT, min_self] at heq
  rw [hTT]
  exact heq

/-- **Proposition 6.1 from the canonical step, the closure step and the Section 6 inputs.** The composition
`iDLAUpperBound_of_coneFamilyAEMeasurable` with the Draft Lemma 2.4 of `coneHarmonicBallsUpToFixedTimeStmt_of_canonical`
in place of the Draft statement. Hypotheses: Lemma 6.10 (`IterativeBoundStmt`), Proposition 5.1 (`IDLALowerBoundStmt`),
the measurability step `ConeFamilyAEMeasurableStep` (its rescaled conjunct is OPEN), and the two steps above. -/
theorem firstPass_6_1_of_canonical (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) : IDLAUpperBoundStmt 𝒮 :=
  iDLAUpperBound_of_coneFamilyAEMeasurable 𝒮 h610 h51 hfam
    (coneHarmonicBallsUpToFixedTimeStmt_of_canonical hcan hcl)

end MatedCRT
