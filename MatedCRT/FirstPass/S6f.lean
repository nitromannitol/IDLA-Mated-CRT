import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-! # Probabilistic events of Lemma 6.8, uniform in scale and vertex

Lemmas consumed by the assembly of `UniformConstantOrderLowerBoundStmt` (`FirstPass/S6d.lean:90`).

* `draft68_events_probTendsToOne`: the three Draft events with polynomially high probability, intersected. The Green lower
  bound (Draft Lemma 2.16, `GreenKernelLowerBoundStmt`), the cell-size estimate (Draft Lemma 2.8, `CellSizeEstimateStmt`) and
  the exit-time upper bound (Draft Lemma 2.18, `ExitTimeUpperBoundStmt`) each quantify over all vertices and all scales
  `r ≥ ε^{ω₀}` (resp. all cells and all sets `D ⊆ B_ρ`), so the intersection is uniform in scale and vertex. Its probability
  tends to one (`PolyHighProb.probTendsToOne`).
* `draft68_hfin_ae`: almost surely, every finite vertex set has exit time `⊤` with probability zero from every start
  (`ExitNull68.exit_null_of_finite`), for every `ε > 0`. This is the finiteness input `hfin` on the Good event.

The almost-sure volume-growth input (Draft Lemma 2.7, scale-uniform on `ball 0 R`, `R < 1`) is
`MatedCRTEnv.IsValid.ae_volumeGrowth_inside_unit` (`Proofs/Sec4/ConvergenceDivisible/VolumeGrowthInsideUnit.lean`). -/

open HarmonicBalls

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Draft events of Lemma 6.8, uniform in scale and vertex.** Fix `γ ∈ (0,2)` and `ζ ∈ (0,1)`. There are
`ω₀ > 0` (Draft Lemma 2.16) and `α > 0` (Draft Lemma 2.18) such that, for each `ρ ∈ (0,1)`, there are constants `CG`, `CE`
with: for every valid environment `S`, the set of `ε` at which the Green lower bound on the vertices `a` of `B_{ρ-ε^{ω₀}}`
and all scales `r ∈ [ε^{ω₀}, dist(a, ∂B_ρ)]`, the cell-size estimate on every cell meeting `B_ρ`, and the exit-time bound
on all `D ⊆ B_ρ` with `ε^α ≤ μ(D)` all hold, has probability tending to one as `ε → 0`. -/
theorem draft68_events_probTendsToOne {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ CG : ℝ, 0 < CG ∧ ∃ CE : ℝ, 0 < CE ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ProbTendsToOne S.P fun ε =>
      {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ,
        ε ^ ω₀ ≤ r → r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)),
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b ≤
            greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b ∧
          CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
            greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b} ∩
      {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)} ∩
      {ω | (∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ N) ∧
        (∀ D : Set ℂ, D ⊆ ball 0 ρ → ∀ a ∈ cellVertices ε (S.η ω) D,
          ENNReal.ofReal (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a) ≤
            expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ∧
          expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
            ENNReal.ofReal (CE * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D))} := by
  obtain ⟨ω₀, hω₀, hGr⟩ := hG γ hγ hγ2
  obtain ⟨α, hα, hEr⟩ := hE γ hγ hγ2
  refine ⟨ω₀, hω₀, α, hα, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  obtain ⟨CE, hCE, hES⟩ := hEr ρ hρ0 hρ1
  refine ⟨CG, hCG, CE, hCE, fun Ω _ S hS => ?_⟩
  have h := ((hGS Ω S hS).inter (hC γ hγ hγ2 ζ ρ hζ0 hζ1 hρ0 hρ1 Ω S hS)).inter (hES Ω S hS)
  exact HarmonicBalls.PolyHighProb.probTendsToOne h

/-- **Finiteness on the Good event.** For a valid environment, almost surely: for every `ε > 0`, every finite
set `A ⊆ ℤ` and every start `y`, the exit from `A` is almost surely finite (`srwLaw (S.mult ε ω) y {exit from A = ⊤} = 0`).
This is `hfin` of `Uniform68Walk.config_exit_lower_bound_walk`, via `ExitNull68.exit_null_of_finite` and the environment
inputs `Uniform68Env.ae_envInputs` (continuity, `η → ∞`, adjacency of cells) and `Uniform68Env.envAt` (local finiteness). -/
theorem draft68_hfin_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ A : Set ℤ, A.Finite → ∀ y : ℤ,
      srwLaw (S.mult ε ω) y {x | vExitTime A x = ⊤} = 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ hγ2 hS] with ω hω
  intro ε hε A hA y
  obtain ⟨hc, hp, hadj⟩ := hω
  obtain ⟨hlf, hcons, -⟩ := Uniform68Env.envAt S hε ω hc hp hadj
  exact ExitNull68.exit_null_of_finite hlf hcons hA y

end MatedCRT
