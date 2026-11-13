import MatedCRT.FirstPass.Derived.ExitCouplingQuenched
import MatedCRT.FirstPass.Derived.NoShortTravelEuclidean

/-!
# Equicontinuity of the laws of the stopped walks from the no-short-travel estimate

The quenched form of Berestycki–Gwynne (2020), Proposition 6.12, Steps 1–2 (`ExitCouplingQuenched`),
with the short-travel probability supplied by the Euclidean form of Proposition 6.5: the successive exit
times from the balls `B_s(η(y))` of the interior vertices of `B_{ρ0}` reach the exit time from `B_{ρ0}`
with probability at least `1 - ψ₀` ((6.36)), and the walk leaves each such ball within `g` steps with
probability at most `q` (Lemma 6.11).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingNoShortTravel

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry
open MatedCRT.FirstPass36 (FiniteExitData)

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **Equicontinuity of the laws of the stopped walks (Proposition 6.12, Steps 1–2) from Proposition 6.5.**
Let `Y = V^ε(B_{ρ0})` (interior vertices) and `A y = V^ε(B_s(η(y)))`.  If the walk from `x` (resp. `y`)
satisfies `τ_Y ≤ σ_K` outside probability `ψ₀`, every `y ∈ Y` leaves `A y` within `g` steps with probability at
most `q`, and every edge out of `Y` has embedded length at most `J`, then walks that visit two vertices fewer than
`g` steps apart before the exit from `Y` at embedded distance more than `3 s + J` have probability at most
`ψ₀ + K q`; the quenched equicontinuity statement then holds with `D = 3 s + J`. -/
theorem levyProkhorovEDist_stoppedWalk_le_of_noShortTravel {mult : ℤ → ℤ → ℕ} (hε : 0 ≤ ε)
    (hη : Continuous η) {z : ℂ} {δ r0 c ρ0 s J : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ r0)
    (hr0 : 2 * r0 + δ < Real.sqrt δ) (hball : ball z (Real.sqrt δ) ⊆ ball (0 : ℂ) ρ0)
    (hA' : FiniteExitData mult (interiorCellVertices ε η (ball z (Real.sqrt δ))))
    {x y : ℤ} (hx : x ∈ cellVertices ε η (ball z δ)) (hy : y ∈ cellVertices ε η (ball z δ))
    (hTV : ∀ T : Set ℤ,
      |(srwLaw mult x).real {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T} -
        (srwLaw mult y).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T}| ≤ c)
    {m : ℝ≥0} (hm : 0 < m) (ρt : ℝ≥0) (hs0 : 0 ≤ s) (hJ0 : 0 ≤ J) {g K : ℕ}
    (hg : (m : ℝ) * ρt + 2 ≤ g) (T0 r : ℝ≥0) {p₁ ψ₀ q : ℝ≥0∞}
    (hJ : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0), ∀ w' : ℤ, mult w w' ≠ 0 →
      dist (vertexPoint ε η w) (vertexPoint ε η w') ≤ J)
    (hr : (T0 : ℝ) * (2 * (3 * s + J) + (2 * δ + 2 * r0)) + Real.exp (-(T0 : ℝ)) < r)
    (hfinx : srwLaw mult x {X | vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X = ⊤} = 0)
    (hfiny : srwLaw mult y {X | vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X = ⊤} = 0)
    (hTx : srwLaw mult x {X | ρt <
      ((vExitTime (interiorCellVertices ε η (ball z (Real.sqrt δ))) X).toNat : ℝ≥0) / m} ≤ p₁)
    (hTy : srwLaw mult y {X | ρt <
      ((vExitTime (interiorCellVertices ε η (ball z (Real.sqrt δ))) X).toNat : ℝ≥0) / m} ≤ p₁)
    (h0x : srwLaw mult x {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
      succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s)) K X} ≤ ψ₀)
    (h0y : srwLaw mult y {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
      succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s)) K X} ≤ ψ₀)
    (hq : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult w {X | vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η w) s)) X <
        (g : ℕ∞)} ≤ q)
    (hap : ENNReal.ofReal c + (p₁ + (ψ₀ + (K : ℝ≥0∞) * q)) + (p₁ + (ψ₀ + (K : ℝ≥0∞) * q)) ≤ r) :
    levyProkhorovEDist
      ((srwLaw mult x).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0))))
      ((srwLaw mult y).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0)))) ≤ r := by
  have hA : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0),
      ∀ u ∈ interiorCellVertices ε η (ball (vertexPoint ε η w) s),
        dist (vertexPoint ε η u) (vertexPoint ε η w) ≤ s := fun w _ u hu =>
    (mem_ball.1 (vertexPoint_mem_of_mem_interiorCellVertices hε hη hu)).le
  have hshort := fun a (h0 : srwLaw mult a {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
      succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s)) K X} ≤ ψ₀) =>
    srwLaw_exists_shortTravel_le mult a (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s))
      (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) g K (vertexPoint ε η) h0 hq hA hJ hJ0
  exact levyProkhorovEDist_stoppedWalk_le_of_shortTravel hη hδ hδ1 hcell hr0 hball hA' hx hy hTV hm ρt
    (by positivity) hg T0 r hr hfinx hfiny hTx hTy (hshort x h0x) (hshort y h0y) hap

end ExitCouplingNoShortTravel
end MatedCRT
