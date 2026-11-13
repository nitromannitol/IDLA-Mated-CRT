import MatedCRT.FirstPass.SLERef.Reference

/-!
# Frozen external input, Berestycki-Gwynne Proposition 5.1

`BG20Prop51` is the mass-restricted first-moment estimate for the exit times of the random walk on the mated-CRT map, which the paper cites from Berestycki-Gwynne (bib key `berestycki2020random`, paper line 916, Lemma 2.18). It is the first clause of `ExitTimeUpperBoundStmt` (Draft Lemma 2.18), without the unrestricted-domain second clause. The second clause is not frozen: it is proved from `BG20Prop51` in `MatedCRT/FirstPass/S3c/ExitTimeBridge.lean`.

`BG20Prop51Ref ν` is the estimate for every space-filling SLE model `𝒮` with normalized code law `ν`, under the certified reference package `SLEReferenceInput ν`. It is proved for every `ν` as `bg20Prop51Ref_of_reference` (`MatedCRT/FirstPass/SLERef/BG20.lean`). The exit-time bounds take the per-model input `BG20Prop51 𝒮`, a component of `CertifiedReferenceModel ν 𝒮` (`MatedCRT/FirstPass/SLERef/Certified.lean`), directly.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Literature input. Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, Commun. Math. Phys. (bib key `berestycki2020random`; arXiv:2003.10320), Proposition 5.1, equation (5.1). Mass-restricted first moment of the exit times: there are `α = α(γ) > 0` and `C = C(ρ, γ) > 0` such that, with polynomially high probability as `ε → 0`, for every measurable `D ⊆ B_ρ` with `μ_h(D) ≥ ε^α`, every `a ∈ V^ε(D)` and every `N ∈ ℕ`, the `N`-th moment of the exit time from the interior cells of `D` is at most `N! C^N ε^{-N} (sup_{z ∈ D} ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ_h(w))^N`.
Weakest form used: the first clause of `ExitTimeUpperBoundStmt` only (no clause for arbitrary `D`), quantified over valid environments `S` for `𝒮` and cone parameter `γ`, exactly as in Draft Lemma 2.18.
Truth check: TRUE. The quantifier order and the probability level are those of the source, with the guard `S.IsValid 𝒮 γ` read as the faithful mated-CRT environment guard. -/
def BG20Prop51 (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω |
    ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
          ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ N}

/-- Literature input, restricted to the certified reference package: under `SLEReferenceInput ν`, the estimate `BG20Prop51` holds for every space-filling SLE model `𝒮` with normalized law `ν`. Same source as `BG20Prop51` (Proposition 5.1, equation (5.1)).
Truth check: TRUE. Proved for every `ν` as `bg20Prop51Ref_of_reference` (`MatedCRT/FirstPass/SLERef/BG20.lean`), from the exit-time component of `SLEReferenceInput ν`. The exit-time bounds take the per-model input `BG20Prop51 𝒮` (a component of `CertifiedReferenceModel ν 𝒮`, `MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def BG20Prop51Ref (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν → ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → BG20Prop51 𝒮

end MatedCRT
