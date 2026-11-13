import MatedCRT.FirstPass.Derived.SrwHarnackGreen

/-!
# The pair events of the Harnack inequality and the quenched Green kernel Harnack inequality

Berestycki–Gwynne (2020), Lemmas 3.9–3.11.  For the mesh-`ε` mated-CRT map of the path `ω` and the curve `η`:

* `PairItinGood ε ω η p₀ z r`: the cells `η([ε(x-1), εx])` form a cellular embedding `H` of the map, and from every
  vertex whose cell meets `∂B_r(z)` the walk follows a polar template itinerary around `∂B_r(z)` with quenched
  probability at least `p₀`;
* `PairL311Good ε ω η ρ'' s₂ p₁`: the same for the disconnection event of Lemma 3.11 at all balls `B_r(w)`,
  `s₂ ≤ r ≤ ρ''`, `B_{2r}(w) ⊆ B_{ρ''}(0)`, with probability at least `p₁`.

`greenKernel_le_inv_mul_of_pairEvents` is the quenched consequence: if these events hold at the lattice circles of
mesh `h₀` and at `ρ'' = (1 + ρ)/2`, then `g(a, b) ≤ (p₀ p₁)⁻¹ g(y, b)` for every vertex `b` whose cell meets `B_ρ` and
all vertices `a, y` whose cells meet a circle `∂B_s(z_b)`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

/-- Two cellular embeddings of the same graph with the same cells are equal. -/
theorem cellularEmbedding_eq_of_cell_eq {V E : Type*} {G : LFMultigraph V E} {o : V}
    {H H' : CellularEmbedding G o} (hc : H.cell = H'.cell) : H = H' := by
  cases H
  cases H'
  cases hc
  rfl

/-- **The itinerary event at the circle `∂B_r(z)`** (Berestycki–Gwynne (2020), (3.21)): the mesh-`ε` mated-CRT map of
`ω` is locally finite, its cells `η([ε(x-1), εx])` form a cellular embedding `H`, and from every vertex whose cell
meets `∂B_r(z)` the walk performs a polar template itinerary around `∂B_r(z)` with quenched probability `≥ p₀`. -/
def PairItinGood (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) (η : ℝ → ℂ) (p₀ : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω,
    ∃ H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ), H.cell = cell ε η ∧
      ∀ y ∈ verticesMeeting H.cell (sphere z r),
        ENNReal.ofReal p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).walkLaw y
          {ξ | PolarTemplateItinerary H z r ((MatedCRTHarmonic.MatedCRT.graph ε ω hlf).vertexPath ξ)}

/-- **The disconnection event of Lemma 3.11** at the balls `B_r(w)`, `f ≤ r ≤ ρ''`, `B_{2r}(w) ⊆ B_{ρ''}(0)`
(with `f = ε^β` this is `Lemma311Holds H ε ρ'' β p₁`): the mesh-`ε` mated-CRT map of `ω` is locally finite, its cells
form a cellular embedding `H`, and from every vertex whose cell meets `B_r(w)` the walk disconnects `V(∂B_{r/2}(w))`
from `V(∂B_{2r}(w))` before hitting `V(∂B_{2r}(w))` with quenched probability `≥ p₁`. -/
def PairL311Good (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) (η : ℝ → ℂ) (ρ'' f p₁ : ℝ) : Prop :=
  ∃ hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω,
    ∃ H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ), H.cell = cell ε η ∧
      ∀ (w : ℂ) (r : ℝ), f ≤ r → r ≤ ρ'' → ball w (2 * r) ⊆ ball (0 : ℂ) ρ'' →
        ∀ y ∈ verticesMeeting H.cell (ball w r),
          ENNReal.ofReal p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).walkLaw y
            {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) H.cell w r
              ((MatedCRTHarmonic.MatedCRT.graph ε ω hlf).vertexPath ξ)}

/-- `Lemma311Holds` is the disconnection event with floor `ε^β`. -/
theorem pairL311Good_of_lemma311Holds {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} {η : ℝ → ℂ}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ)) (hHc : H.cell = cell ε η)
    {ρ'' β p₁ : ℝ} (h : Lemma311Holds H ε ρ'' β p₁) : PairL311Good ε ω η ρ'' (ε ^ β) p₁ :=
  ⟨hlf, H, hHc, h⟩

/-- **Quenched Harnack inequality for the Green kernel on circles from the pair events** (Berestycki–Gwynne (2020),
Lemma 3.9 with the events (3.21) and (3.35); the consumer of `mul_greenKernel_le_of_pairEvents`).  The itinerary
events hold at all lattice circles of mesh `h₀` with centre `z'` and radius `h₀ l ≥ s₁` with `B_{2 h₀ l}(z') ⊆
B_{(1+ρ)/2}(0)`, the disconnection event holds for the radii `≥ s₂` in `B_{(1+ρ)/2}(0)`, and the cells of all
vertices meeting `B_{(1+ρ)/2}(0)` have diameter `≤ δ ≤ h₀`. -/
theorem greenKernel_le_inv_mul_of_pairEvents {ε : ℝ} (hε : 0 ≤ ε) {ω : MatedCRTHarmonic.MatedCRT.Path2}
    {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {ρ δ h₀ s₀ s₁ s₂ p₀ p₁ : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ x' ∈ cell ε η k, dist x x' ≤ δ)
    (hs₀ : 300 * h₀ ≤ s₀) (hs₁ : s₁ + 3 * h₀ ≤ s₀) (hs₂ : 5 * s₂ ≤ s₀)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hItin : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l → ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      PairItinGood ε ω η p₀ (latticePt h₀ m' n') (h₀ * l))
    (h311 : PairL311Good ε ω η ((1 + ρ) / 2) s₂ p₁)
    (hB : (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))).Finite) :
    ∀ b ∈ cellVertices ε η (ball (0 : ℂ) ρ), ∀ s : ℝ, s₀ ≤ s → s ≤ (1 - ρ) / 8 →
      ∀ a ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
      ∀ y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
        greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
            (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b ≤
          (p₀ * p₁)⁻¹ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
            (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) y b := by
  obtain ⟨h, H, hHc, h311'⟩ := h311
  have hItin' : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l →
      ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (sphere (latticePt h₀ m' n') (h₀ * l)),
        ENNReal.ofReal p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | PolarTemplateItinerary H (latticePt h₀ m' n') (h₀ * l)
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)} := by
    intro m' n' l hl hball y hy
    obtain ⟨h', H', hH'c, hit⟩ := hItin m' n' l hl hball
    have hHH : H' = H := cellularEmbedding_eq_of_cell_eq (hH'c.trans hHc.symm)
    subst hHH
    exact hit y hy
  intro b hb s hs0 hs1 a ha y hy
  have key := mul_greenKernel_le_of_pairEvents h hε H hlf hcons hHc hh hδ hδh hdiam hs₀ hs₁ hs₂ hs0 hs1
    hp₀.le hp₁.le hItin' h311' hB hb (a := y) (y := a) hy ha
  have hp : 0 < p₀ * p₁ := mul_pos hp₀ hp₁
  calc greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b
      = (p₀ * p₁)⁻¹ * ((p₀ * p₁) * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b) := by
        field_simp
    _ ≤ (p₀ * p₁)⁻¹ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) y b :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hp.le)

end MatedCRT

#print axioms MatedCRT.greenKernel_le_inv_mul_of_pairEvents
