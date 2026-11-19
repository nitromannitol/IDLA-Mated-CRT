import MatedCRT.FirstPass.Derived.BlockExitSkeletonJoinParametersDerived
import MatedCRT.FirstPass.Derived.UniformStartGoodDerived

/-!
# The uniform-start event from the block-exit skeleton comparison

`goodG S ε R ρ κ` (the uniform-start event) says that, from every vertex `x` with `vertexPoint ε (S.η ω) x` in
`closedBall 0 ρ`, the stopped embedded walk is dominated by the stopped planar Brownian motion from the same point in
the all-set form with tolerance `κ`.  This is the conclusion of `BlockExit.exists_blockExit_parameters_allSet_le_derived`
applied to the law of the walk from `x`, embedded as a continuous path by `interpPathCM`, and to planar Brownian motion
from `vertexPoint ε (S.η ω) x`.  So the event is reached from the block-exit data directly, without a cellwise
Lévy-Prokhorov comparison.

* `exists_blockExit_parameters_mem_goodG`: for `0 ≤ ρ < R` and `κ > 0` there are block parameters `s, d', δ₀, N`
  (independent of the environment and of the mesh) such that the walk-side block-exit hypotheses at all the vertices
  in `closedBall 0 ρ` give `ω ∈ goodG S ε R ρ κ`.
* `ae_eventually_mem_goodG_of_blockExit`: the almost-sure eventual form along a mesh sequence `e`, with the walk-side
  hypotheses at all block parameters for which planar Brownian motion from `closedBall 0 ρ` reaches the far set within
  `N` blocks outside probability `κ / 16` (this guard excludes, for instance, `N = 0`, for which the walk-side reach
  bound cannot hold).
* `gms21UniformStartInput_of_blockExit`: the uniform-start invariance principle with the walk-side block-exit
  hypotheses as the only hypothesis.

The walk-side hypotheses are, at each vertex `x` with embedded point in `closedBall 0 ρ`: the one-sided Prokhorov bound
`ProkhorovLE` with parameters `(δ₀, κ / 4)` between the law of the block-exit positions of the embedded walk from `x`
and that of planar Brownian motion from the embedded point, and the reach of the far set within `N` blocks by the walk
outside probability `κ / 8`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology
open HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit

/-- **The uniform-start event from the block-exit skeleton comparison.** For `0 ≤ ρ < R` and `κ > 0` there are
block parameters `s, d', δ₀, N`, depending only on `ρ, R, κ`, such that for every environment `S`, mesh `ε` and
`ω`: if at every vertex `x` with `vertexPoint ε (S.η ω) x ∈ closedBall 0 ρ` the block-exit positions of the embedded
walk from `x` are `(δ₀, κ / 4)`-Prokhorov-close to those of planar Brownian motion from the embedded point, and the
walk reaches the far set within `N` blocks outside probability `κ / 8`, then `ω ∈ goodG S ε R ρ κ`. -/
theorem exists_blockExit_parameters_mem_goodG {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (s d' δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ 0 < δ₀ ∧
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j b) ∈
          farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 16)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω),
        (∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult ε ω) x).map fun ξ =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint ε (S.η ω) x)).map fun b =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N b) δ₀ (κ / 4) ∧
          srwLaw (S.mult ε ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ
              (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ)) ∈
              farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 8)) →
        ω ∈ goodG S ε R ρ κ := by
  obtain ⟨s, d', δ₀, N, hs, hd', hδ₀, hguard, H⟩ := exists_blockExit_parameters_allSet_le_derived.{0} hρ hρR hκ
  refine ⟨s, d', δ₀, N, hs, hd', hδ₀, hguard, ?_⟩
  intro Ω _ S ε ω hω x hx A
  exact H (srwLaw (S.mult ε ω) x) (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one)
    (measurable_interpPathCM _ _) (vertexPoint ε (S.η ω) x) hx (δ := δ₀) (e := κ / 4) hδ₀.le le_rfl le_rfl
    (hω x hx).1 (hω x hx).2 A

/-- **Almost-sure eventual uniform start from the block-exit skeleton comparison.** If, for all block parameters,
almost surely and eventually in `n`, the walk-side block-exit hypotheses hold at all the vertices in `closedBall 0 ρ` at
mesh `e n`, then almost surely `ω ∈ goodG S (e n) R ρ κ` for all large `n`. -/
theorem ae_eventually_mem_goodG_of_blockExit {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) (e : ℕ → ℝ)
    (hwalk : ∀ (s d' δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → 0 < δ₀ →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j b) ∈
          farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 16)) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e n) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e n) ω) x).map fun ξ =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e n) (S.η ω) x)).map fun b =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N b) δ₀ (κ / 4) ∧
          srwLaw (S.mult (e n) ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ)) ∈
              farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 8)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ κ := by
  obtain ⟨s, d', δ₀, N, hs, hd', hδ₀, hguard, H⟩ := exists_blockExit_parameters_mem_goodG hρ hρR hκ
  filter_upwards [hwalk s d' δ₀ N hs hd' hδ₀ hguard] with ω hω
  exact hω.mono fun n hn => H S (e n) ω hn

/-- **The uniform-start invariance principle from the walk-side block-exit hypotheses.** -/
theorem gms21UniformStartInput_of_blockExit {𝒮 : SpaceFillingSLEModel}
    (hwalk : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ →
      ∀ (e : ℕ → ℝ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ (s d' δ₀ : ℝ) (N : ℕ), 0 < s → 0 < d' → 0 < δ₀ →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j b) ∈
          farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 16)) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ x : ℤ, vertexPoint (e n) (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
          ProkhorovLE ((srwLaw (S.mult (e n) ω) x).map fun ξ =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ))
            ((planarBrownianMotion (vertexPoint (e n) (S.η ω) x)).map fun b =>
              blockExitPositions s (farSet (ball (0 : ℂ) R) d') N b) δ₀ ((κ / 2) / 4) ∧
          srwLaw (S.mult (e n) ω) x {ξ | ∃ j ≤ N, interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ
              (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j (interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one ξ)) ∈
              farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal ((κ / 2) / 8)) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  exact exists_eps_uniformStart_bound_derived hγ hγ2 hS hκ
    (fun e he he0 => ae_eventually_mem_goodG_of_blockExit S hρ.le hρR (half_pos hκ) e
      (hwalk γ hγ hγ2 Ω S hS R ρ hρ hρR κ hκ e he he0)) hθ

end UniformStartGood

end MatedCRT
