import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-! The deterministic fixed-time reduction for the obstacle gap. -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- If the raw obstacle cluster is open and agrees with its regularization
whenever its closure is contained in the comparison disk, then the harmonic
ball lies in the raw cluster before the exit time. -/
theorem coneFamily_subset_cluster_of_no_regularization_defect
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t : ℝ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ)
    (hopen : IsOpen (cluster μ ρ 0 t))
    (hdefect : closure (cluster μ ρ 0 t) ⊆ ball 0 ρ →
      interior (closure (cluster μ ρ 0 t)) = cluster μ ρ 0 t) :
    Λ t ⊆ cluster μ ρ 0 t := by
  unfold clusterExitTime at hT
  have hne : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    have he : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    simp only [he, Real.sSup_empty] at hT
    linarith
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne hT
  have hsmall : Λ t ⊆ ball 0 (ρ / 3) :=
    (hΛ.2.1.monotoneOn ht hs.1 hts.le).trans hs.2
  have heq := (hΛ.2.2 t (ρ / 3) ht (by linarith) hsmall ρ (by linarith)).1
  have hclosed : closure (cluster μ ρ 0 t) ⊆ ball 0 ρ := by
    apply (closure_mono (hopen.subset_interior_closure.trans (heq.symm.subset.trans hsmall))).trans
    exact Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))
  rw [heq, hdefect hclosed]

/-- Fixed-time openness and absence of regularization defects imply the
strict obstacle-gap step, with the exceptional event independent of the
chosen harmonic-ball family. -/
theorem harmonicBallStrictObstacleGapStep_of_no_regularization_defect
    (𝒮 : SpaceFillingSLEModel)
    (hlocal : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂S.P,
        IsOpen (cluster (S.μ ω) ρ 0 t) ∧
        (closure (cluster (S.μ ω) ρ 0 t) ⊆ ball 0 ρ →
          interior (closure (cluster (S.μ ω) ρ 0 t)) = cluster (S.μ ω) ρ 0 t)) :
    HarmonicBallStrictObstacleGapStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht
  filter_upwards [hΛ, hlocal γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht] with ω hfamily hproperty
  intro hT
  exact coneFamily_subset_cluster_of_no_regularization_defect hfamily hρ ht hT
    hproperty.1 hproperty.2

end MatedCRT
