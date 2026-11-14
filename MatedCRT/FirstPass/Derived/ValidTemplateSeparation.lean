import MatedCRT.FirstPass.Derived.ValidPeanosphere
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.Compose
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210

/-!
# Template separation for the mated-CRT map of a valid environment

Step (C2) of the disconnection estimate behind the invariance principle of
Gwynne-Miller-Sheffield (Lemma 3.14 (a)), on the discrete side.

For a cellular embedding `H` of the mated-CRT map with cell size `ε` whose cells are the cells
`H^ε_{εx} = η([ε(x - 1), εx])` of Definition 1.2, the property `H.TemplateSeparation z r` (every walk
whose cells follow the polar template moved to the centre `z` and the radius `r` separates the cells
meeting `∂B_{3r/4}(z)` from those meeting `∂B_{5r/4}(z)`) holds as soon as

* the boundary-length pair and a continuous version of the curve form a Peanosphere,
* the Brownian side condition `SideStrict ε` holds, and
* the cells meeting `closedBall z (2r)` have diameter at most `r / 1000`.

This is Bonanno's `RouteM.templateSeparation_matedCRT`. In a valid environment the first two
conditions hold almost surely: the Peanosphere and the identity of the cells come from the
mating-of-trees coupling (`MatedCRTEnv.IsValid.exists_curve_peanosphere`), and the side condition at
the mesh `ε > 0` from the law of the boundary-length pair (`GMSMain.epsA_ae_sideStrict`).

## Main results

* `templateSeparation_of_peanosphere_cell`: the deterministic step, for one sample.
* `MatedCRTEnv.IsValid.ae_templateSeparation`: for a valid environment and `ε > 0`, almost surely every
  such cellular embedding has `TemplateSeparation z r` at every centre `z` and radius `r > 0` with small
  cells near `closedBall z (2r)`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set

/-- **Template separation for one sample.** If `w` and the continuous curve `η'` form a Peanosphere,
`w` satisfies the side condition at the mesh `ε`, and the cells `H^ε_{εx}` of `η` are the images
`η'([ε(x - 1), εx])`, then every cellular embedding of the mated-CRT map with these cells has
`TemplateSeparation z r` for each `r > 0` such that the cells meeting `closedBall z (2r)` have diameter
at most `r / 1000`. -/
theorem templateSeparation_of_peanosphere_cell {ε : ℝ} {w : MatedCRTHarmonic.MatedCRT.Path2}
    {η : ℝ → ℂ} {η' : C(ℝ, ℂ)} (hP : MatedCRTHarmonic.RouteM.Peanosphere w η')
    (hG : MatedCRTHarmonic.RouteM.SideStrict ε w)
    (hcell : ∀ x : ℤ, cell ε η x = η' '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    {hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε w}
    (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε w hlf) (0 : ℤ))
    (hHc : H.cell = cell ε η) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000) :
    H.TemplateSeparation z r :=
  MatedCRTHarmonic.RouteM.templateSeparation_matedCRT hP hG H
    (funext fun x => (congrFun hHc x).trans (hcell x)) hr hsmall

/-- **Template separation in a valid environment.** For a valid environment and a cell size `ε > 0`,
almost surely: for every proof of local finiteness and every cellular embedding `H` of the mated-CRT
map with cell size `ε` whose cells are the cells `H^ε_{εx}` of Definition 1.2, `H.TemplateSeparation z r`
holds at every centre `z` and radius `r > 0` such that the cells meeting `closedBall z (2r)` have
diameter at most `r / 1000`. -/
theorem MatedCRTEnv.IsValid.ae_templateSeparation {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (z : ℂ) (r : ℝ), 0 < r →
      (∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000) →
      H.TemplateSeparation z r := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hC, -⟩ := hS.matingOfTrees
  obtain ⟨η', -, hpeano, hcellEq⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  filter_upwards [hpeano, hcellEq, MatedCRTHarmonic.GMSMain.epsA_ae_sideStrict hC hε]
    with ω hP hcell hG
  intro hlf H hHc z r hr hsmall
  exact templateSeparation_of_peanosphere_cell hP hG (hcell ε) H hHc hr hsmall

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.templateSeparation_of_peanosphere_cell
#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_templateSeparation
