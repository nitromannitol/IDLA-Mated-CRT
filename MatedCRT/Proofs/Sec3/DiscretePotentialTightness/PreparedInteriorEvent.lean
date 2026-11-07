import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Equicontinuity
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Common-event interior vertex estimates for deterministic preparation. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Tightness
open scoped ENNReal

/-- On a single event the interior vertex modulus holds for every domain and
every admissible sequence of scales in the prepared deterministic range. -/
theorem ae_prepared_interior_vertex_modulus
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℕ → ℝ), (∀ n, ε n ∈ range e) → Tendsto ε atTop (𝓝 0) →
      ∀ (D K : Set ℂ) (u : ℕ → ℤ → ℝ) (C : ℝ),
      IsOpen D → D ⊆ ball 0 ρ → IsCompact K → K ⊆ D → 0 ≤ C →
      (∀ n, ∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
        |matedLaplacian (S.mult (ε n) ω) (u n) a| ≤ C) →
      (∀ n, ∀ a ∈ cellVertices (ε n) (S.η ω) D, |u n a| ≤ C / ε n) →
      IsVertexAsymptoticallyEquicontinuous ε (S.η ω) u K := by
  obtain ⟨α, hα, h18α⟩ := h218 γ hγ hγ2
  obtain ⟨C₁, hC₁, h18C⟩ := h18α ρ hρ hρ1
  obtain ⟨q, hq, h17q⟩ := h217 γ hγ hγ2
  have h17 := (h17q ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).2
  obtain ⟨ξ, A, β, hξ, _, hA, hβ, _, hHχ⟩ := hH γ hγ hγ2 ρ hρ hρ1
  obtain ⟨_, _, _, _, _, hH1⟩ := hHχ 1 1 one_pos le_rfl one_pos
  filter_upwards [ae_eventually_mem_of_polyHighProb (h18C Ω S hS) he,
    ae_eventually_mem_of_polyHighProb h17 he,
    ae_eventually_mem_of_polyHighProb (hH1 Ω S hS) he,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω h18ω h17ω hHω hadjω hηω hpω
  intro ε hεrange hε0 D K u C hDo hDρ hK hKD hC hlap hbd
  have hε : ∀ n, 0 < ε n := fun n => by
    obtain ⟨j, hj⟩ := hεrange n
    rw [← hj]
    exact he.1 j
  have hM : ∀ R₀ : ℝ, 0 < R₀ → ∃ R : ℝ, 0 < R ∧ R < R₀ ∧
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball y R) ≤ ENNReal.ofReal (R ^ q) := by
    intro R₀ hR₀
    obtain ⟨j, hj1, hj2⟩ := (h17ω.and (he.tendsto_zero.eventually (gt_mem_nhds hR₀))).exists
    exact ⟨e j, he.1 j, hj2, hj1⟩
  have hHball : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) (ball x r), matedLaplacian (S.mult (ε n) ω) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) (S.η ω) (ball x r), ∀ b ∈ cellVertices (ε n) (S.η ω) (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) (S.η ω) a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (ε n) (S.η ω) (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) (S.η ω) a - vertexPoint (ε n) (S.η ω) b‖ ^ ξ := by
    apply eventually_of_range (Q := fun s => ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices s (S.η ω) (ball x r), matedLaplacian (S.mult s ω) f a = 0) →
      ∀ a ∈ interiorCellVertices s (S.η ω) (ball x r), ∀ b ∈ cellVertices s (S.η ω) (ball x r),
        |f a - f b| * infDist (vertexPoint s (S.η ω) a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices s (S.η ω) (ball x r), |f a'|) *
            max (s ^ β) ‖vertexPoint s (S.η ω) a - vertexPoint s (S.η ω) b‖ ^ ξ)
      he.1 hεrange hε0
    filter_upwards [hHω] with n hn x r hr hxr f hf
    exact (hn (ball x r) f hxr isOpen_ball ((convex_ball x r).isConnected (nonempty_ball.2 hr)) hf).1
  have hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) (S.η ω) D',
      expectedExitTime (S.mult (ε n) ω) (interiorCellVertices (ε n) (S.η ω) D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε n ^ α) D') := by
    apply eventually_of_range (Q := fun r => ∀ D' : Set ℂ, D' ⊆ ball 0 ρ →
      ∀ a ∈ cellVertices r (S.η ω) D',
        expectedExitTime (S.mult r ω) (interiorCellVertices r (S.η ω) D') a ≤
          ENNReal.ofReal (C₁ * r⁻¹) * largestExitTimeRV (S.μ ω) (thickening (r ^ α) D'))
      he.1 hεrange hε0
    filter_upwards [h18ω] with n hn D' hD' a ha
    exact (hn.2 D' hD' a ha).2
  exact interior_vertexEquicontinuous (m := fun n => S.mult (ε n) ω) hε hε0 hηω.1 hpω
    (fun n => hadjω _ (hε n)) (fun n k => S.mult_succ_ne_zero (hε n).le ω k) hDo hDρ hK hKD
    hC hlap hbd hξ hA.le hβ hα hC₁.le hq hHball hQ hM

end MatedCRT
