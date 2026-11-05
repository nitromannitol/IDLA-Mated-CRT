import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.GapThresholdMeasurable
import MatedCRT.Proofs.Measurability.BoundaryLayer

/-! # Coverage under noncoincidence of the inner neighbourhood -/

namespace MatedCRT

open Set Metric MeasureTheory Filter _root_.HarmonicBalls

/-- An open set is contained in another set exactly when each of its
positive inner neighbourhoods is contained there. -/
theorem isOpen_subset_iff_innerNbhd_subset {U V : Set ℂ} (hU : IsOpen U) :
    U ⊆ V ↔ ∀ δ : ℝ, 0 < δ → innerNbhd δ U ⊆ V := by
  constructor
  · intro h δ _ x hx
    exact h hx.1
  · intro h x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    have hmem : x ∈ innerNbhd (r / 2) U := by
      rw [innerNbhd_eq_infEDist_superlevel (half_pos hr)]
      apply Metric.le_infEDist.mpr
      intro y hy
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have hd : r ≤ dist y x := by
        by_contra hn
        exact hy (hball (by simpa [mem_ball] using (lt_of_not_ge hn)))
      rw [dist_comm]
      linarith
    exact h (r / 2) (half_pos hr) hmem

/-- For an open obstacle cluster, containment of every inner neighbourhood
of its regularization in the cluster is equivalent to regular openness. -/
theorem isOpen_regularOpen_iff_innerNbhd_subset {C : Set ℂ} (hC : IsOpen C) :
    interior (closure C) = C ↔
      ∀ δ : ℝ, 0 < δ → innerNbhd δ (interior (closure C)) ⊆ C := by
  rw [← isOpen_subset_iff_innerNbhd_subset isOpen_interior]
  exact ⟨fun h => h.subset, fun h => Subset.antisymm h (interior_maximal subset_closure hC)⟩

/-- On a set inside the disc, the positive scaled obstacle gap away from the
pole is equivalent to membership in the unregularized obstacle cluster. -/
theorem subset_cluster_iff_scaled_strict_gap
    {μ : Measure ℂ} {ρ t c : ℝ} {K : Set ℂ} (hc : 0 < c)
    (hK : K ⊆ ball 0 ρ) :
    K ⊆ cluster μ ρ 0 t ↔
      ∀ x ∈ K \ {0}, 0 < c * leastSupersolution μ ρ 0 t x -
        (-t * c * greenFunction (ball 0 ρ) 0 x) := by
  constructor
  · intro h x hx
    have hx0 : x ≠ 0 := by simpa using hx.2
    have hcluster := h hx.1
    rcases hcluster.2 with hzero | hlt
    · exact (hx0 hzero).elim
    · have hpos := mul_pos hc (sub_pos.mpr hlt)
      nlinarith
  · intro h x hx
    refine ⟨hK hx, ?_⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hpos := h x ⟨hx, by simpa using hx0⟩
      have heq : c * leastSupersolution μ ρ 0 t x -
          (-t * c * greenFunction (ball 0 ρ) 0 x) =
          c * (leastSupersolution μ ρ 0 t x -
            (-t * greenFunction (ball 0 ρ) 0 x)) := by ring
      rw [heq] at hpos
      exact sub_pos.mp (pos_of_mul_pos_left (by simpa [mul_comm] using hpos) hc.le)

/-- If the inner neighbourhood is contained in the unregularized continuum
cluster almost surely before exit, then it is covered by discrete obstacle
cells with high probability. Exit measurability follows from cone-family
measurability and Lemma 2.4. -/
theorem innerNbhd_coverage_of_subset_cluster (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (hcluster : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      innerNbhd δ (Λ ω t) ⊆ cluster (S.μ ω) ρ 0 t) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      (fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
  have hexit := hS.nullMeasurableSet_lt_clusterExitTime hγ hγ' hfam h24 hρ hρ' hΛ ht
  apply innerNbhd_coverage_of_strict_gap_of_volumeGrowth 𝒮 h41 h33 h28 h27
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ ht hexit
  have hc : 0 < S.c₀ / 6 := matedCRTScalingConstantPositive 𝒮 γ hγ hγ' Ω S hS
  filter_upwards [hΛ, hS.isLQGMeasure, hcluster] with ω hω hμ hcl hT
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  have hsub := (coneFamily_innerNbhd_compact_subset hω hρ ht hT hδ).2
  have hsub' : innerNbhd δ (Λ ω t) ⊆ ball 0 ρ :=
    hsub.trans (closedBall_subset_ball (by linarith))
  exact (subset_cluster_iff_scaled_strict_gap hc hsub').mp (hcl hT)

end MatedCRT
