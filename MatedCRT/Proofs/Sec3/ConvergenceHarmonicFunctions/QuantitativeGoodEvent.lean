import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ModulusThreshold

/-! # Good-event bound for the projected harmonic modulus -/

namespace MatedCRT

open Filter Topology Metric MeasureTheory Set Tightness _root_.HarmonicBalls
open scoped ENNReal

/-- On any event where the curve, cell-radius, boundary, and interior bounds
hold, the quantitative projected-modulus failure event is contained in the
complement. This is the good-event reduction used before taking limits. -/
theorem projected_modulus_failure_subset_compl_good {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (ε : ℝ)
    {d H K χ ξ : ℝ} {G : Set Ω} (hr : 0 < r) (hε : 0 < ε)
    (hd : 0 ≤ d) (hH : 0 ≤ H) (hK : 0 ≤ K) (hχ : 0 ≤ χ) (hξ : 0 ≤ ξ)
    (hcurve : ∀ ω ∈ G, Continuous (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective (S.η ω))
    (hcell : ∀ ω ∈ G, ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r),
      ∀ p ∈ cell ε (S.η ω) a, dist (vertexPoint ε (S.η ω) a) p ≤ d)
    (hdata : ∀ ω ∈ G, ∀ a ∈ cellVertices ε (S.η ω) (frontier (ball z r)),
      ∀ b ∈ cellVertices ε (S.η ω) (frontier (ball z r)),
      |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
        projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
        H * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ χ)
    (hmod : ∀ ω ∈ G, ∀ a ∈ cellVertices ε (S.η ω) (ball z r),
      ∀ b ∈ cellVertices ε (S.η ω) (ball z r),
      |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
        projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
        K * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ ξ) :
    {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
      |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y| >
        2 * (H * max ε (2 * d) ^ χ) + K * max ε (dist x y + 6 * d) ^ ξ} ⊆ Gᶜ := by
  intro ω ⟨x, hx, y, hy, hbad⟩ hω
  obtain ⟨hη, hp, hsurj⟩ := hcurve ω hω
  have hxcl : x ∈ closure (ball z r) := by rw [closure_ball z hr.ne']; exact hx
  have hycl : y ∈ closure (ball z r) := by rw [closure_ball z hr.ne']; exact hy
  have hc : ∀ a ∈ cellVertices ε (S.η ω) (closure (ball z r)),
      ∀ p ∈ cell ε (S.η ω) a, dist (vertexPoint ε (S.η ω) a) p ≤ d := by
    simpa only [closure_ball z hr.ne'] using hcell ω hω
  have hbound := projectedExtension_modulus_of_boundary_holder S r z ψ ε ω hε hd hH hK hχ hξ
    hη hp hsurj isOpen_ball hc (hdata ω hω) (hmod ω hω) hxcl hycl
    (mem_cell_vertexOf hη hp hsurj hε x) (mem_cell_vertexOf hη hp hsurj hε y)
  exact (not_lt_of_ge hbound) hbad

/-- A regularity good event for the cell embedding and projected vertex values.
This is a proof step, not an imported literature assertion. -/
def CorrectedHarmonicRegularityGoodEventStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, IsHolderContinuousOn ψ (closedBall z r) →
  ∀ e : ℝ≥0∞, 0 < e → ∃ H K χ ξ : ℝ, ∃ d : ℝ → ℝ, ∃ G : ℝ → Set Ω,
    0 ≤ H ∧ 0 ≤ K ∧ 0 < χ ∧ 0 < ξ ∧
    Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ d ε) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P (G ε)ᶜ ≤ e ∧
      (∀ ω ∈ G ε, Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
        Function.Surjective (S.η ω)) ∧
      (∀ ω ∈ G ε, ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r),
        ∀ p ∈ cell ε (S.η ω) a, dist (vertexPoint ε (S.η ω) a) p ≤ d ε) ∧
      (∀ ω ∈ G ε, ∀ a ∈ cellVertices ε (S.η ω) (frontier (ball z r)),
        ∀ b ∈ cellVertices ε (S.η ω) (frontier (ball z r)),
        |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
          projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
          H * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ χ) ∧
      (∀ ω ∈ G ε, ∀ a ∈ cellVertices ε (S.η ω) (ball z r),
        ∀ b ∈ cellVertices ε (S.η ω) (ball z r),
        |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
          projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
          K * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ ξ))

/-- The geometric and vertex good event implies the quantitative modulus. -/
theorem correctedHarmonicQuantitativeModulus_of_goodEvent (𝒮 : SpaceFillingSLEModel)
    (hgood : CorrectedHarmonicRegularityGoodEventStep 𝒮) :
    CorrectedHarmonicQuantitativeModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ e he
  obtain ⟨H, K, χ, ξ, d, G, hH, hK, hχ, hξ, hd, hdpos, hG⟩ :=
    hgood γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ e he
  refine ⟨H, K, χ, ξ, d, hH, hK, hχ, hξ, hd, hdpos, ?_⟩
  filter_upwards [hG, hdpos, self_mem_nhdsWithin] with ε hεG hdε hε
  obtain ⟨hprob, hcurve, hcell, hdata, hmod⟩ := hεG
  exact (measure_mono (projected_modulus_failure_subset_compl_good S r z ψ ε
    hr hε hdε hH hK hχ.le hξ.le hcurve hcell hdata hmod)).trans hprob

/-- The corrected convergence assertion follows from the regularity good event
and the already isolated walk-to-LBM and cell-size inputs. -/
theorem correctedHarmonicConvergence_of_goodEvent (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hgood : CorrectedHarmonicRegularityGoodEventStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_holder_modulus 𝒮 h211 hmeps hexc hX h28
    (correctedHarmonicHolderModulus_of_quantitative 𝒮
      (correctedHarmonicQuantitativeModulus_of_goodEvent 𝒮 hgood))

end MatedCRT
