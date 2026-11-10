import MatedCRT.FirstPass.SLERef.Reference

/-!
# First pass: frozen external input, BG20 Proposition 5.1 (task fp-S3c-3-1-fidelity-fix, route A; worker z12)

`BG20Prop51` is the mass-restricted first-moment estimate for the exit times of the random walk on the mated-CRT
map, which the paper cites from Berestycki–Gwynne (bib key `berestycki2020random`, paper line 916, Lemma 2.18). It is
the first clause of `ExitTimeUpperBoundStmt` (Draft Lemma 2.18), without the unrestricted-domain second clause.
The second clause is NOT frozen: it is proved from `BG20Prop51` in `MatedCRT/FirstPass/S3c/ExitTimeBridge.lean`
(audit `notes/fp-gaps/CHATGPT-idla-3-1-audit.md` §2.3, operator decision of 05:34 UTC, route A).

`BG20Prop51Ref ν` is FALSE as typed (chat 186): its universal transfer over all space-filling SLE models `𝒮` with normalized
code law `ν` is not justified, since `HasNormalizedSLELaw 𝒮 ν` does not constrain the IsSLE semantics of `𝒮`. It is kept
unchanged and superseded by the per-model input `BG20Prop51 𝒮`, a component of `CertifiedReferenceModel ν 𝒮`
(`MatedCRT/FirstPass/SLERef/Certified.lean`, operator note 06:10 UTC). The 3.1 consumers take `BG20Prop51 𝒮` directly
(`firstPass_3_1_faithful_of_bg20Model`, `firstPass_3_1_countable_of_bg20Model` in `MatedCRT/FirstPass/S3c.lean`).
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- FIRST-PASS FROZEN (EXTERNAL). Berestycki–Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian
motion*, Commun. Math. Phys. (bib key `berestycki2020random`; arXiv:2003.10320 as recorded in the bibliography audit),
Proposition 5.1, equation (5.1). Truth check TRUE (chat 186, `notes/fp-gaps/CHATGPT-idla-new-frozen-SLERef-BG20.md`;
operator note 06:10 UTC): the quantifier order and the probability level are those of the source, with the guard
`S.IsValid 𝒮 γ` read as the faithful mated-CRT environment guard.
Mass-restricted first moment of the exit times: there are `α = α(γ) > 0` and
`C = C(ρ, γ) > 0` such that, with polynomially high probability as `ε → 0`, for every measurable `D ⊆ B_ρ` with
`μ_h(D) ≥ ε^α`, every `a ∈ V^ε(D)` and every `N ∈ ℕ`, the `N`-th moment of the exit time from the interior cells of `D`
is at most `N! C^N ε^{-N} (sup_{z ∈ D} ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ_h(w))^N`.
Weakest form used: the first clause of `ExitTimeUpperBoundStmt` only (no clause for arbitrary `D`), quantified over
valid environments `S` for `𝒮` and cone parameter `γ`, exactly as in Draft Lemma 2.18.
Used by: `exitTimeUpperBoundStmt_core` (MatedCRT/FirstPass/S3c/ExitTimeCore.lean), hence the per-model forms
`firstPass_3_1_faithful_of_bg20Model` and `firstPass_3_1_countable_of_bg20Model` (MatedCRT/FirstPass/S3c.lean). -/
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
(Proposition 5.1, equation (5.1)). FALSE as typed (chat 186, operator note 06:10 UTC): `HasNormalizedSLELaw 𝒮 ν` does not
constrain the IsSLE semantics of `𝒮`, so the universal transfer is not justified. Superseded by the per-model input
`BG20Prop51 𝒮` (a component of `CertifiedReferenceModel ν 𝒮`, `MatedCRT/FirstPass/SLERef/Certified.lean`). Kept, not
deleted; statement unchanged. Used by: `exitTimeUpperBoundStmt_of_bg20` (MatedCRT/FirstPass/S3c/ExitTimeCore.lean). -/
def BG20Prop51Ref (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν → ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → BG20Prop51 𝒮

end MatedCRT
