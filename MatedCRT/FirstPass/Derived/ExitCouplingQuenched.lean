import MatedCRT.FirstPass.Derived.ExitCouplingCells
import MatedCRT.FirstPass.Derived.ExitCouplingOscillation

/-!
# Equicontinuity of the laws of the stopped walks: the quenched statement

Berestycki–Gwynne (2020), Proposition 6.12, Steps 1–2, for a fixed mated-CRT map and the walks from
two vertices of `V^ε(B_δ(z))`, in terms of the three quantities that the probabilistic estimates supply:
the total variation distance `c` of the exit positions from `A'` (Lemma 6.13), the exit time tail from `A'`
(Corollary 5.2 with Markov's inequality), and the no-short-travel bound before the exit time from `A`
(Proposition 6.5).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingQuenched

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingEvents MatedCRT.ExitCouplingGlue
  MatedCRT.ExitCouplingCells MatedCRT.ExitCouplingOscillation
open MatedCRT.FirstPass36 (FiniteExitData)

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **Equicontinuity of the laws of the stopped walks (Proposition 6.12, Steps 1–2, quenched).**
For two vertices `x, y` of `V^ε(B_δ(z))`, the laws of the interpolated walks stopped at the exit time
from `A = V^ε(B_{ρ0})`-interior are at Lévy–Prokhorov distance at most `r`, provided the exit positions from
`A'` (the interior vertices of `B_{√δ}(z)`) are within `c` in total variation, the exit time from `A'` is at
most `ρt` (in rescaled time) outside probability `p₁`, vertices visited fewer than `g` steps apart before the
exit from `A` are at embedded distance at most `D` outside probability `p₂`, and `T0 (2 D + 2 δ + 2 r0) +
exp (-T0) < r`, `c + 2 (p₁ + p₂) ≤ r`. -/
theorem levyProkhorovEDist_stoppedWalk_le_of_shortTravel {mult : ℤ → ℤ → ℕ} (hη : Continuous η)
    {z : ℂ} {δ r0 c ρ0 D : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ r0)
    (hr0 : 2 * r0 + δ < Real.sqrt δ) (hball : ball z (Real.sqrt δ) ⊆ ball (0 : ℂ) ρ0)
    (hA' : FiniteExitData mult (interiorCellVertices ε η (ball z (Real.sqrt δ))))
    {x y : ℤ} (hx : x ∈ cellVertices ε η (ball z δ)) (hy : y ∈ cellVertices ε η (ball z δ))
    (hTV : ∀ T : Set ℤ,
      |(srwLaw mult x).real {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T} -
        (srwLaw mult y).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T}| ≤ c)
    {m : ℝ≥0} (hm : 0 < m) (ρt : ℝ≥0) (hD : 0 ≤ D) {g : ℕ} (hg : (m : ℝ) * ρt + 2 ≤ g)
    (T0 r : ℝ≥0) {p₁ p₂ : ℝ≥0∞}
    (hr : (T0 : ℝ) * (2 * D + (2 * δ + 2 * r0)) + Real.exp (-(T0 : ℝ)) < r)
    (hfinx : srwLaw mult x {X | vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X = ⊤} = 0)
    (hfiny : srwLaw mult y {X | vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X = ⊤} = 0)
    (hTx : srwLaw mult x {X | ρt <
      ((vExitTime (interiorCellVertices ε η (ball z (Real.sqrt δ))) X).toNat : ℝ≥0) / m} ≤ p₁)
    (hTy : srwLaw mult y {X | ρt <
      ((vExitTime (interiorCellVertices ε η (ball z (Real.sqrt δ))) X).toNat : ℝ≥0) / m} ≤ p₁)
    (hshx : srwLaw mult x {X | ∃ i j : ℕ, i < j ∧ j < i + g ∧
      (j : ℕ∞) ≤ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ∧
      D < dist (vertexPoint ε η (X i)) (vertexPoint ε η (X j))} ≤ p₂)
    (hshy : srwLaw mult y {X | ∃ i j : ℕ, i < j ∧ j < i + g ∧
      (j : ℕ∞) ≤ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ∧
      D < dist (vertexPoint ε η (X i)) (vertexPoint ε η (X j))} ≤ p₂)
    (hap : ENNReal.ofReal c + (p₁ + p₂) + (p₁ + p₂) ≤ r) :
    levyProkhorovEDist
      ((srwLaw mult x).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0))))
      ((srwLaw mult y).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0)))) ≤ r :=
  levyProkhorovEDist_stoppedWalk_le hη hδ hδ1 hcell hr0 hball hA' hx hy hTV hm ρt T0 r hr
    (srwLaw_walkGood_compl_le_of_shortTravel mult x (vertexPoint ε η) hm _ _ ρt hD hg hfinx hTx hshx)
    (srwLaw_walkGood_compl_le_of_shortTravel mult y (vertexPoint ε η) hm _ _ ρt hD hg hfiny hTy hshy)
    hap

end ExitCouplingQuenched
end MatedCRT
