import MatedCRT.Draft.Section2

/-!
# Frozen canonical form of Berestycki-Gwynne Lemma 5.6

The Green-function crude bound of the IDLA paper (Lemma 2.15, `GreenFunctionCrudeBoundStmt`, Draft/Section2.lean:201) kills the walk on the interior vertex set `V^ε(B_ρ) \ V^ε(∂B_ρ)`. Berestycki-Gwynne, arXiv:2003.10320v2, Lemma 5.6 (equation (5.20)) kills it on the full vertex set `V^ε(B_ρ)` of the cells meeting `B_ρ`. The frozen Prop below is the canonical BG form. The IDLA-form statement is derived from it by domain monotonicity of the killed Green function, `greenFunctionCrudeBound_of_canonical` (`MatedCRT/FirstPass/S5u.lean`).

Rules of this file. (i) The model `𝒮` is a parameter, never quantified (no `∀ 𝒮`). (ii) Nothing here is proved. (iii) The frozen Prop is used only as a hypothesis type.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- Literature input, canonical form. Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320v2, Lemma 5.6, equation (5.20) (BG20 Definition 3.2 for the Green function killed on a vertex set). For each `ζ ∈ (0,1)`, with polynomially high probability as `ε → 0`, `sup_{a,b ∈ V^ε(B_ρ)} G^ε_{V^ε(B_ρ)}(a,b) ≤ ε^{-ζ}`, where `G^ε_A` is the Green function of the walk killed on exiting the vertex set `A`.
Truth check: TRUE (BG20 Definition 3.2, Notation 3.3 and Lemma 5.6, (5.20)). Killing on exiting all of `cellVertices(Bρ)` is the correct convention, and the BG statement implies the IDLA form. Caveat: `greenFn` is real-valued with junk value `0` when the expectation is infinite, so this Prop does not by itself give finiteness; the derivation in `MatedCRT/FirstPass/S5u.lean` uses only finite-domain monotonicity and does not need it. -/
def FrozenBG20GreenCrudeCanonical (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ ζ : ℝ, 0 < ρ → ρ < 1 → 0 < ζ → ζ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
    greenFn (S.mult ε ω) (cellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-ζ)}

end MatedCRT
