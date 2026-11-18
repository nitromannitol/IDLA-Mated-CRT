import MatedCRT.FirstPass.Derived.EdgeCountLabelledEdges
import LatticeProb.LQG.SidedContactEdges

/-!
# The mated-CRT map as the map of shared sided contact arcs

Definition 1.1 gives the `γ`-mated-CRT map with cell size `ε` as the edge multiplicity
`bmEdgeCount ε L R` (`MatedCRTEnv.mult`) of the boundary-length pair. Under the mating-of-trees
coupling of the environment, Gwynne–Miller–Sheffield (2019), §1.2 (the discussion after (1.1)),
describe the same edges through the space-filling SLE cells: between non-consecutive vertices
`x + 1 < y` the edge of side `L` (resp. `R`) is present iff the cells `η([ε(x-1), εx])` and
`η([ε(y-1), εy])` share a non-trivial boundary arc traced by the left (resp. right) boundary,
i.e. iff the image under `η` of the direct contact times of that contour coordinate is not a
singleton (`MatedCRTHarmonic.RouteM.sidedContactMult`).

This file composes the count of labelled edges (`MatedCRTEnv.mult_eq_nat_card_isEdge`) with the
almost sure edge/contact correspondence for the coupled curves.

## Main statements

* `MatedCRT.MatedCRTEnv.IsValid.ae_mult_eq_sidedContactMult`: at a fixed mesh `ε > 0`, almost
  surely, for all `x + 1 < y`, the adjacency condition (eq:edge-map) of each side holds iff the
  contact image of that side is nontrivial, and `S.mult ε ω x y` is the sided contact
  multiplicity.
* `MatedCRT.MatedCRTEnv.IsValid.ae_prod_shifted_mult_eq_sidedContactMult`: the same on the grid
  shifted by an independent phase whose law is absolutely continuous and s-finite.
-/

namespace MatedCRT

open MeasureTheory Set
open MatedCRTHarmonic.RouteM

/-- At a fixed mesh `ε > 0`, almost surely, for all non-consecutive vertices `x + 1 < y`, the
adjacency condition (eq:edge-map) of Definition 1.1 for the coordinate of each side holds iff the
cells share the non-trivial contact arc of that side, and the edge multiplicity of the mated-CRT
map is the sided contact multiplicity. -/
theorem MatedCRTEnv.IsValid.ae_mult_eq_sidedContactMult {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ x y : ℤ, x + 1 < y →
      (∀ b : Bool, bmAdjacent ε (fun t => if b then (S.bm ω t).2 else (S.bm ω t).1) x y ↔
        (S.η ω '' directContactTimes ε
          (if b then rCoord (S.bm ω) else lCoord (S.bm ω)) x y).Nontrivial) ∧
      S.mult ε ω x y = sidedContactMult ε (S.bm ω) (S.η ω) x y := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  filter_upwards [MatedCRTHarmonic.MoTInput.ae_isEdge_iff_nontrivial_contact hε hC, htie]
    with ω hω htω
  intro x y hxy
  obtain ⟨h1, h2⟩ := hω x y hxy
  rw [htω.1] at h1 h2
  refine ⟨fun b => (isEdge_iff_bmAdjacent ε (S.bm ω) hxy b).symm.trans (h1 b), ?_⟩
  rw [MatedCRTEnv.mult_eq_nat_card_isEdge S hε.le ω (by omega), h2]

/-- On the grid shifted by an independent phase `c` whose law `Q` is s-finite and absolutely
continuous, at a fixed mesh `ε > 0`, almost surely for the product law, for all non-consecutive
vertices `x + 1 < y`: the adjacency condition of each side for the shifted boundary-length pair
holds iff the shifted cells share the non-trivial contact arc of that side, and the edge
multiplicity of the mated-CRT map of the shifted pair is the sided contact multiplicity. -/
theorem MatedCRTEnv.IsValid.ae_prod_shifted_mult_eq_sidedContactMult
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂S.P.prod Q, ∀ x y : ℤ, x + 1 < y →
      (∀ b : Bool, bmAdjacent ε
          (fun t => if b then (S.bm p.1 (t + p.2)).2 else (S.bm p.1 (t + p.2)).1) x y ↔
        ((fun t => S.η p.1 (t + p.2)) '' directContactTimes ε
          (if b then rCoord (timeTranslate (S.bm p.1) p.2)
            else lCoord (timeTranslate (S.bm p.1) p.2)) x y).Nontrivial) ∧
      bmEdgeCount ε (fun t => (S.bm p.1 (t + p.2)).1) (fun t => (S.bm p.1 (t + p.2)).2) x y =
        sidedContactMult ε (timeTranslate (S.bm p.1) p.2) (fun t => S.η p.1 (t + p.2)) x y := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have htie' : ∀ᵐ p ∂S.P.prod Q, ⇑(η' p.1) = S.η p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := S.P) (ν := Q)).ae (htie.mono fun ω h => h.1)
  filter_upwards [MatedCRTHarmonic.MoTInput.ae_prod_isEdge_time_translate_iff_nontrivial_contact
    hC hε Q hQ, htie'] with p hp htp
  intro x y hxy
  obtain ⟨h1, h2⟩ := hp x y hxy
  rw [htp] at h1 h2
  refine ⟨fun b => (isEdge_iff_bmAdjacent ε (timeTranslate (S.bm p.1) p.2) hxy b).symm.trans
    (h1 b), ?_⟩
  have h3 := bmEdgeCount_eq_card_isEdge hε.le (timeTranslate (S.bm p.1) p.2)
    (x := x) (y := y) (by omega)
  rw [← nat_card_isEdge_eq_card_filter, h2] at h3
  exact h3

end MatedCRT
