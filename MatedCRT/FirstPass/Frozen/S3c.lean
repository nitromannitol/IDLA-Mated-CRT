import MatedCRT.FirstPass.SLERef.Reference

/-!
# First pass: frozen external input, BG20 Proposition 5.1 (task fp-S3c-3-1-fidelity-fix, route A; worker z12)

`BG20Prop51` is the mass-restricted first-moment estimate for the exit times of the random walk on the mated-CRT
map, which the paper cites from Berestycki–Gwynne (bib key `berestycki2020random`, paper line 916, Lemma 2.18). It is
the first clause of `ExitTimeUpperBoundStmt` (Draft Lemma 2.18), without the unrestricted-domain second clause.
The second clause is NOT frozen: it is proved from `BG20Prop51` in `MatedCRT/FirstPass/S3c/ExitTimeBridge.lean`
(audit `notes/fp-gaps/CHATGPT-idla-3-1-audit.md` §2.3, operator decision of 05:34 UTC, route A).

`BG20Prop51Ref ν` restricts the input to the certified reference package: it is asserted only under
`SLEReferenceInput ν`, and only for space-filling SLE models `𝒮` with normalized law `ν`
(`SLEReferenceInput` and `HasNormalizedSLELaw` are in `MatedCRT/FirstPass/SLERef/Reference.lean`
and `SLERef/Code.lean`).
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- FIRST-PASS FROZEN (EXTERNAL). Berestycki–Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian
motion*, arXiv:2003.10320 (Commun. Math. Phys., to appear; bib key `berestycki2020random`), Proposition 5.1 (printed
page: PENDING TRUTH CHECK). Mass-restricted first moment of the exit times: there are `α = α(γ) > 0` and
`C = C(ρ, γ) > 0` such that, with polynomially high probability as `ε → 0`, for every measurable `D ⊆ B_ρ` with
`μ_h(D) ≥ ε^α`, every `a ∈ V^ε(D)` and every `N ∈ ℕ`, the `N`-th moment of the exit time from the interior cells of `D`
is at most `N! C^N ε^{-N} (sup_{z ∈ D} ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ_h(w))^N`.
Weakest form used: the first clause of `ExitTimeUpperBoundStmt` only (no clause for arbitrary `D`), quantified over
valid environments `S` for `𝒮` and cone parameter `γ`, exactly as in Draft Lemma 2.18.
Used by: `exitTimeUpperBoundStmt_of_bg20` (MatedCRT/FirstPass/S3c/ExitTimeBridge.lean), hence `firstPass_3_1_faithful`
through `ExitTimeUpperBoundStmt`. -/
def BG20Prop51 (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω |
    ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
          ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ N}

/-- FIRST-PASS FROZEN (EXTERNAL), restricted to the certified reference package: under `SLEReferenceInput ν`, the
estimate `BG20Prop51` holds for every space-filling SLE model `𝒮` with normalized law `ν`. Same source as `BG20Prop51`
(arXiv:2003.10320, Proposition 5.1; PENDING TRUTH CHECK). Used by: `exitTimeUpperBoundStmt_of_bg20`. -/
def BG20Prop51Ref (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν → ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → BG20Prop51 𝒮

end MatedCRT
