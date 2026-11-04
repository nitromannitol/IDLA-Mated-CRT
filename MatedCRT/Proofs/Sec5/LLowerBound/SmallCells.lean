import MatedCRT.Proofs.Sec5.LLowerBound.Mass

/-! Continuity and properness give uniform smallness of cells meeting a fixed ball. -/

open Set Filter Metric

namespace MatedCRT

/-- A continuous proper curve has uniformly small cells on bounded regions. -/
theorem cell_diam_small_of_proper {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (ρ d : ℝ) (hd : 0 < d) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ k ∈ cellVertices ε η (ball 0 ρ),
      diam (cell ε η k) ≤ d := by
  have hcompact : IsCompact (η ⁻¹' closedBall 0 ρ) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη, hp⟩).isCompact_preimage
      (isCompact_closedBall 0 ρ)
  obtain ⟨T, hT⟩ := hcompact.isBounded.subset_closedBall 0
  let B : ℝ := |T| + 2
  have hu : UniformContinuousOn η (Icc (-B) B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hη.continuousOn
  obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuousOn_iff.mp hu d hd
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro ε hε hε₀ k hk
  have hε1 : ε < 1 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ : ε < δ := lt_of_lt_of_le hε₀ (min_le_right _ _)
  obtain ⟨w, ⟨t, ht, rfl⟩, hw⟩ := hk
  have htT : |t| ≤ T := by
    have h := hT (show t ∈ η ⁻¹' closedBall 0 ρ from ball_subset_closedBall hw)
    simpa [Real.dist_eq] using h
  have htime : ∀ s ∈ Icc (ε * (k - 1)) (ε * k), s ∈ Icc (-B) B := by
    intro s hs
    obtain ⟨htl, htr⟩ := ht
    obtain ⟨hsl, hsr⟩ := hs
    obtain ⟨htlo, hthi⟩ := abs_le.1 htT
    have hT' := le_abs_self T
    dsimp [B]
    constructor <;> nlinarith
  apply Metric.diam_le_of_forall_dist_le hd.le
  rintro _ ⟨s, hs, rfl⟩ _ ⟨u, hu, rfl⟩
  apply le_of_lt (huδ s (htime s hs) u (htime u hu) ?_)
  rw [Real.dist_eq, abs_lt]
  obtain ⟨hsl, hsr⟩ := hs
  obtain ⟨hul, hur⟩ := hu
  constructor <;> nlinarith

end MatedCRT
