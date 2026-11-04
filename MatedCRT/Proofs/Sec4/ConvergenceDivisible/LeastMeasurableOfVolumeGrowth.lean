import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DenseMajorants
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMassMeasurable

/-! # Measurability of least supersolutions under volume growth -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Almost sure volume growth implies pointwise measurability of the least
supersolution. -/
theorem MatedCRTEnv.IsValid.aemeasurable_leastSupersolution_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (R t : ℝ) (z x : ℂ) (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ closedBall (0 : ℂ) R)
    (hV : ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus) :
    AEMeasurable (fun ω => leastSupersolution (S.μ ω) R z t x) S.P := by
  classical
  let K := closedBall (0 : ℂ) R
  have hcont : ∀ᵐ ω ∂S.P, ContinuousOn (greenPotentialBall (S.μ ω) R) K := by
    filter_upwards [hV, hS.isLQGMeasure] with ω ⟨βm, βp, hv⟩ hω
    exact greenPotentialBall_continuousOn (S.μ ω) hω.isLocallyFiniteMeasure R βm βp hR hv
  obtain ⟨g, hg, hga⟩ := hS.exists_jointlyMeasurable_greenPotentialBall R hR.le hcont
  obtain ⟨D, hDc, hD, hdense⟩ := exists_countable_superharmonic_majorants R
  let D' := insert (0 : ℂ → ℝ) D
  have hD' (v : ℂ → ℝ) (hv : v ∈ D') :
      ContinuousOn v K ∧ LaplacianLE v 0 (ball 0 R) := by
    rcases mem_insert_iff.mp hv with rfl | hv
    · exact ⟨continuous_zero.continuousOn, laplacianLE_zero 0 _⟩
    · exact hD v hv
  obtain ⟨seq, hseq⟩ := (hDc.insert (0 : ℂ → ℝ)).exists_eq_range ⟨0, by simp⟩
  have hseq' (n : ℕ) : seq n ∈ D' := by
    change seq n ∈ insert (0 : ℂ → ℝ) D
    rw [hseq]
    exact ⟨n, rfl⟩
  let W : ℕ → Ω × ℂ → ℝ := fun n p => K.piecewise (seq n) 0 p.2 - g p
  have hW (n : ℕ) : Measurable (W n) := by
    have hv : Measurable (K.piecewise (seq n) 0) :=
      ((hD' (seq n) (hseq' n)).1).measurable_piecewise
        continuous_zero.continuousOn isClosed_closedBall.measurableSet
    exact (hv.comp measurable_snd).sub hg
  have hWcont (n : ℕ) : ∀ᵐ ω ∂S.P,
      ContinuousOn (fun y => W n (ω, y)) K := by
    filter_upwards [hcont, hga] with ω hc hq
    have heq : EqOn (fun y => W n (ω, y))
        (fun y => seq n y - greenPotentialBall (S.μ ω) R y) K := by
      intro y hy
      simp [W, hy, hq y hy]
    exact ((hD' (seq n) (hseq' n)).1.sub hc).congr heq
  apply hS.aemeasurable_leastSupersolution_of_measurable_candidates R t z x hz W hW hWcont
  filter_upwards [hV, hS.isLQGMeasure, hga] with ω ⟨βm, βp, hv⟩ hω hq
  let μ := S.μ ω
  have hμ := hω.isLocallyFiniteMeasure
  obtain ⟨hbdd, _, hleast, _, _⟩ :=
    obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βm βp hR hv z hz t ht
  obtain ⟨hcompat, hshift, _, _⟩ :=
    obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hv z hz t ht
  intro q
  constructor
  · intro hlt
    let u := shiftedLeastSupersolution μ R z t
    have hlt' : 0 < q - leastSupersolution μ R z t x := sub_pos.mpr hlt
    obtain ⟨v, hvD, hvapprox⟩ := hdense u hleast.1 hleast.2.1
      (q - leastSupersolution μ R z t x) hlt'
    have hvD' : v ∈ D' := mem_insert_of_mem _ hvD
    obtain ⟨n, hn⟩ : ∃ n, seq n = v := by
      change v ∈ insert (0 : ℂ → ℝ) D at hvD'
      rw [hseq] at hvD'
      exact hvD'
    have hshifted : v ∈ shiftedSupersolutions μ R z t := by
      refine ⟨(hD v hvD).1, (hD v hvD).2, ?_⟩
      intro y hy hyz
      exact (hleast.2.2 y hy hyz).trans (hvapprox y hy).1
    have hcandidate : (fun y => v y - greenPotentialBall μ R y) ∈ supersolutions μ R z t := by
      apply (hcompat _).2
      convert hshifted using 1
      funext y
      ring
    have heq : EqOn (fun y => v y - greenPotentialBall μ R y) (fun y => W n (ω, y)) K := by
      intro y hy
      simp [W, hn, hy, hq y hy, μ]
    have hmem : (fun y => W n (ω, y)) ∈ supersolutions μ R z t := by
      refine ⟨hcandidate.1.congr heq.symm, hcandidate.2.1.congr_eqOn measurableSet_ball
        (heq.mono ball_subset_closedBall), ?_⟩
      intro y hy hyz
      rw [← heq hy]
      exact hcandidate.2.2 y hy hyz
    refine ⟨n, hmem, ?_⟩
    change (fun y => W n (ω, y)) x < q
    rw [← heq hx]
    have := (abs_lt.mp (hvapprox x hx).2).2
    dsimp [u] at this
    linarith [hshift x hx]
  · rintro ⟨n, hn, hnlt⟩
    have hnshift := (hcompat _).1 hn
    have hle : shiftedLeastSupersolution μ R z t x ≤ W n (ω, x) + greenPotentialBall μ R x :=
      csInf_le (hbdd x hx) ⟨_, hnshift, rfl⟩
    rw [hshift x hx]
    linarith

end MatedCRT
