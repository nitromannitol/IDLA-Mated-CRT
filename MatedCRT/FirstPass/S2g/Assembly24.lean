import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.Canonical

/-! # Canonical stopped existence from the factorization (q1, fp-S2g)

`ConeCanonicalHalfBallStep` (the pathwise existence of the canonical stopped family, `S2g.lean`) is a consequence of z2's
`ConeCanonicalFactorStep` (`S2g/Canonical.lean`): clause (ii) of that step gives, at every continuous circle process in the
full-law set `G` and every LQG limit, a canonical stopped family with positive time. So the pathwise route
`ConePathwiseHalfBallInputs` is an independent alternative, not needed once the factor step is available. The corrected
Lemma 2.4 from the factor step is `firstPass_2_4_canonical_of_factor` (`S2g/Canonical.lean:69`). -/

namespace MatedCRT

open MeasureTheory Filter Set

/-- **Canonical stopped existence from the factorization (q1, fp-S2g).** Almost surely the canonical family of the cone
measure exists, by clause (ii) of `ConeCanonicalFactorStep` at the circle process of `hcirc ω`. -/
theorem coneCanonicalHalfBallStep_of_factor (hfac : ConeCanonicalFactorStep) : ConeCanonicalHalfBallStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨ΨT, Ψ, G, _, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨_, _, hGc⟩ := hfull Ω P hC hcirc μ hcone
  filter_upwards [hGc, hcone.2.1.ae_continuousOn_circle, hcone.2.2] with ω hg hc hl
  obtain ⟨_, ⟨Λ, h1, h2⟩, hp, _⟩ := hchar (hcirc ω) hg hc (μ ω) hl
  exact ⟨Λ, hp, h1, h2⟩

end MatedCRT
