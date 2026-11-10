import MatedCRT.FirstPass.S6p

/-!
# Lemma 6.5, corrected uniform form: `firstPass_6_5_uniform` (task fp-S6q-6-5-uniform-wrapper, worker q3)

`AnnulusHitStmt` (Draft/Section6.lean:72) quantifies `∀ ρ` before `∃ C`, so its constant may depend on `ρ`.
The printed Lemma 6.5 (`lemma:annulus-hit`, corrected tex line 2682) says `C = C(p)`. The uniform form
`AnnulusHitUniformStmt` (FirstPass/S6p.lean:33) moves `∀ ρ` after `∃ C`. The event is the corrected one,
CORRECTION [C5] (`IsGoodAnnulusEvent`).

This file gives:

* `firstPass_6_5_uniform`: `AnnulusHitUniformStmt` from the same three FIRST-PASS inputs as `firstPass_6_5`
  (FirstPass/S5S6S7.lean:50): `FPWholePlaneLQGExistence`, `FPWholePlaneLQGCoordinateChange`,
  `FPWholePlaneUpperVolumeTail`. It is the wrapper `annulusHit_uniform` (S6p.lean:44) with the tightness step
  `wholePlaneGoodAnnulusTightness_of_volumeTail`, as `firstPass_6_4_uniform` (S6p.lean:213) is. Nothing beyond that
  instantiation is proved here.
* `FirstPass64.AnnulusHitUniformStmt.toStmt`: the uniform form implies `AnnulusHitStmt` (for each `ρ`, the same `C`).
-/

namespace MatedCRT.FirstPass64

/-- **Lemma 6.5 (corrected [C5] uniform form)**: `AnnulusHitUniformStmt`, that is `C = C(p)` (lemma:annulus-hit,
corrected tex line 2682), with the good-annulus event `IsGoodAnnulusEvent` of [C5]. Hypotheses: the same three
FIRST-PASS inputs as `firstPass_6_5` (FirstPass/S5S6S7.lean:50). -/
theorem firstPass_6_5_uniform (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) : AnnulusHitUniformStmt :=
  annulusHit_uniform h0 AnnulusHitField.coneWholePlaneWeylComparison h2
    (wholePlaneGoodAnnulusTightness_of_volumeTail h0 hV)

/-- The uniform form implies the Draft statement `AnnulusHitStmt` (Draft/Section6.lean:72): for each `ρ`, the same `C`. -/
theorem AnnulusHitUniformStmt.toStmt (H : AnnulusHitUniformStmt) : AnnulusHitStmt := by
  intro γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀' p hp hp1
  obtain ⟨C, hC, h⟩ := H γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  exact ⟨C, hC, h ρ hρ hρ1⟩

end MatedCRT.FirstPass64
