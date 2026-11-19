import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodG
import MatedCRT.FirstPass.Derived.BlockExitSkeletonJoinParametersSandwichDerived
import MatedCRT.FirstPass.Derived.BlockExitGridCellFrozen

/-!
# The uniform-start event from the block-exit skeleton comparison, frozen on a union of grid cells

This is `BlockExitSkeletonGoodG` with the frozen set `farSet (ball 0 R) d'` replaced by a measurable set `F`
sandwiched between far sets, `farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'` with `d' + 2 s ≤ d₁`.  The block
parameters `s, d', d₁, δ₀, N` are independent of `F`.  For the choice `F = ballFrozenSet s (R + d')`, the union
of the closed grid cells of mesh `s` that miss `ball 0 (R + d')`, the sandwich holds, and the complement of `F` is a
staircase grid polygon around the ball.

* `exists_blockExit_parameters_mem_goodG_sandwich`: the walk-side block-exit hypotheses for the walk frozen on `F`,
  at all vertices in `closedBall 0 ρ`, give `ω ∈ goodG S ε R ρ κ`.
* `ae_eventually_mem_goodG_of_blockExit_sandwich`: the almost-sure eventual form along a mesh sequence, with the
  walk-side hypotheses for the frozen set `ballFrozenSet s (R + d')`.
* `gms21UniformStartInput_of_blockExit_sandwich`: the uniform-start invariance principle with the walk-side
  block-exit hypotheses for these frozen sets as the only hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology
open HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit

/-- **The uniform-start event from the block-exit skeleton comparison, sandwiched frozen set.** For
`0 ≤ ρ < R` and `κ > 0` there are block parameters `s, d', d₁, δ₀, N`, depending only on `ρ, R, κ`, such that for
every measurable `F` with `farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'`, every environment `S`, mesh `ε` and
`ω`: if at every vertex `x` with `vertexPoint ε (S.η ω) x ∈ closedBall 0 ρ` the block-exit positions frozen on `F`
of the embedded walk from `x` are `(δ₀, κ / 4)`-Prokhorov-close to those of planar Brownian motion from the
embedded point, and the walk reaches `F` within `N` blocks outside probability `κ / 8`, then
`ω ∈ goodG S ε R ρ κ`. -/
theorem exists_blockExit_parameters_mem_goodG_sandwich {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ d' + 2 * s ≤ d₁ ∧ 0 < δ₀ ∧
      ∀ {F : Set ℂ}, MeasurableSet F → farSet (ball (0 : ℂ) R) d₁ ⊆ F →
      F ⊆ farSet (ball (0 : ℂ) R) d' →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s F j b) ∈ F}ᶜ ≤ ENNReal.ofReal (κ / 16)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω),
        (∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult ε ω) x).map fun ξ =>
              blockExitPositions s F N (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint ε (S.η ω) x)).map fun b =>
              blockExitPositions s F N b) δ₀ (κ / 4) ∧
          srwLaw (S.mult ε ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ
              (blockExitTimes s F j (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ)) ∈ F}ᶜ ≤
            ENNReal.ofReal (κ / 8)) →
        ω ∈ goodG S ε R ρ κ := by
  obtain ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, H⟩ :=
    exists_blockExit_parameters_allSet_le_sandwich_derived.{0} hρ hρR hκ
  refine ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, ?_⟩
  intro F hFm hF₁ hF₂
  obtain ⟨hguard, H'⟩ := H hFm hF₁ hF₂
  refine ⟨hguard, ?_⟩
  intro Ω _ S ε ω hω x hx A
  exact H' (srwLaw (S.mult ε ω) x) (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one)
    (measurable_interpPathCM _ _) (vertexPoint ε (S.η ω) x) hx (δ := δ₀) (e := κ / 4) hδ₀.le le_rfl le_rfl
    (hω x hx).1 (hω x hx).2 A

/-- **Almost-sure eventual uniform start from the block-exit skeleton comparison, frozen on a union of grid
cells.** If, for all block parameters with `d' + 2 s ≤ d₁`, almost surely and eventually in `n`, the walk-side
block-exit hypotheses for the frozen set `ballFrozenSet s (R + d')` hold at all the vertices in `closedBall 0 ρ` at
mesh `e n`, then almost surely `ω ∈ goodG S (e n) R ρ κ` for all large `n`. -/
theorem ae_eventually_mem_goodG_of_blockExit_sandwich {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) (e : ℕ → ℝ)
    (hwalk : ∀ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → d' + 2 * s ≤ d₁ → 0 < δ₀ →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (ballFrozenSet s (R + d')) j b) ∈
          ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal (κ / 16)) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e n) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e n) ω) x).map fun ξ =>
              blockExitPositions s (ballFrozenSet s (R + d')) N
                (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e n) (S.η ω) x)).map fun b =>
              blockExitPositions s (ballFrozenSet s (R + d')) N b) δ₀ (κ / 4) ∧
          srwLaw (S.mult (e n) ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (ballFrozenSet s (R + d')) j
                (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ)) ∈
              ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal (κ / 8)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ κ := by
  obtain ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, H⟩ :=
    exists_blockExit_parameters_mem_goodG_sandwich hρ hρR hκ
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  obtain ⟨hguard, H'⟩ := H (measurableSet_ballFrozenSet s (R + d'))
    (farSet_subset_ballFrozenSet hs hR hd' hd₁) (ballFrozenSet_subset_farSet s R d')
  filter_upwards [hwalk s d' d₁ δ₀ N hs hd' hd₁ hδ₀ hguard] with ω hω
  exact hω.mono fun n hn => H' S (e n) ω hn

/-- **The uniform-start invariance principle from the walk-side block-exit hypotheses, frozen on a union of grid
cells.** -/
theorem gms21UniformStartInput_of_blockExit_sandwich {𝒮 : SpaceFillingSLEModel}
    (hwalk : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ →
      ∀ (e : ℕ → ℝ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → d' + 2 * s ≤ d₁ → 0 < δ₀ →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (ballFrozenSet s (R + d')) j b) ∈
          ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 16)) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e n) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e n) ω) x).map fun ξ =>
              blockExitPositions s (ballFrozenSet s (R + d')) N
                (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e n) (S.η ω) x)).map fun b =>
              blockExitPositions s (ballFrozenSet s (R + d')) N b) δ₀ ((κ / 2) / 4) ∧
          srwLaw (S.mult (e n) ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (ballFrozenSet s (R + d')) j
                (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ)) ∈
              ballFrozenSet s (R + d')}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 8)) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  exact exists_eps_uniformStart_bound_derived hγ hγ2 hS hκ
    (fun e he he0 => ae_eventually_mem_goodG_of_blockExit_sandwich S hρ.le hρR (half_pos hκ) e
      (hwalk γ hγ hγ2 Ω S hS R ρ hρ hρR κ hκ e he he0)) hθ

end UniformStartGood

end MatedCRT
