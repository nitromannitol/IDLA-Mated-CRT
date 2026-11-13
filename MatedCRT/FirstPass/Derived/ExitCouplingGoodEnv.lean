import MatedCRT.FirstPass.Derived.ExitCouplingHq
import MatedCRT.FirstPass.Derived.ExitCouplingMarkov
import MatedCRT.FirstPass.Derived.ExitCouplingNoShortTravel
import MatedCRT.FirstPass.Derived.CellLocation

/-!
# Equicontinuity of the laws of the stopped walks in a good environment

The deterministic core of Berestycki–Gwynne (2020), Proposition 6.12 (Steps 1–2): in one fixed environment,
if the cells near `B_{ρ1}` have diameter at most `d`, the exit positions from the interior vertices of
`B_{√δ}(z)` have total variation distance at most `c` for starting points in `V^ε(B_δ(z))`, the walk exits
these sets in expected time at most `Q` (Lemma 2.19), the walk leaves `B_{ρ0}` within `K` successive exits
(Lemma 6.10, (6.36)) and leaves every small ball `B_{δ'}(η(x))` after time `T ≥ g` with probability at
least `1 - ψ` (Lemma 6.11), then for **every** `z ∈ B_ρ` and every pair `x, y ∈ V^ε(B_δ(z))` the Lévy–Prokhorov
distance of the laws of the stopped interpolated walks is at most `r`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingGoodEnv

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue MatedCRT.ExitCouplingNoShortTravel MatedCRT.ExitCouplingMarkov
  MatedCRT.ExitCouplingHq
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry
open MatedCRT.FirstPass36 (FiniteExitData)

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **Equicontinuity of the laws of the stopped walks in a good environment (Proposition 6.12, Steps 1–2).**
All hypotheses are deterministic statements about one environment; for every `z ∈ B_ρ` and every
`x, y ∈ V^ε(B_δ(z))` the laws of the walks from `x` and from `y`, interpolated at speed `m` and stopped at
the exit from the interior vertices of `B_{ρ0}`, are at Lévy–Prokhorov distance at most `r`. -/
theorem levyProkhorovEDist_stoppedWalk_le_of_goodEnv {mult : ℤ → ℤ → ℕ} (hε : 0 ≤ ε)
    (hη : Continuous η) (hadj : ∀ j k, mult k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ ρ0 ρ1 δ d δ' : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hd0 : 0 ≤ d) (hδ' : 0 < δ')
    (hρ0 : ρ + Real.sqrt δ ≤ ρ0) (hρ1 : ρ0 + δ' ≤ ρ1) (hd : d < δ') (hr0 : 2 * d + δ < Real.sqrt δ)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ1).Nonempty → ∀ x ∈ cell ε η k,
      ∀ y ∈ cell ε η k, dist x y ≤ d)
    {c : ℝ}
    (hTV : ∀ z ∈ ball (0 : ℂ) ρ, ∀ x ∈ cellVertices ε η (ball z δ), ∀ y ∈ cellVertices ε η (ball z δ),
      ∀ T : Set ℤ,
      |(srwLaw mult x).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T} -
        (srwLaw mult y).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T}| ≤ c)
    (hA' : ∀ z ∈ ball (0 : ℂ) ρ, FiniteExitData mult (interiorCellVertices ε η (ball z (Real.sqrt δ))))
    (hfin : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult x {X | vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X = ⊤} = 0)
    {m : ℝ≥0} (hm : 0 < m) {ρt : ℝ≥0} (hρt : 0 < ρt) {Q : ℝ≥0∞}
    (hQ : ∀ z ∈ ball (0 : ℂ) ρ, ∀ a : ℤ,
      expectedExitTime mult (interiorCellVertices ε η (ball z (Real.sqrt δ))) a ≤ Q)
    {g K : ℕ} (hg : (m : ℝ) * ρt + 2 ≤ g) {T ψ : ℝ} (hgT : (g : ℝ) ≤ T) {R₁ : ℝ} (hR₁ : ρ0 ≤ R₁)
    (h611 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) R₁),
      srwLaw mult x {X | (vExitTime (cellVertices ε η (ball (vertexPoint ε η x) δ')) X : ℝ≥0∞) <
        ENNReal.ofReal T} ≤ ENNReal.ofReal ψ)
    {ψ₀ : ℝ≥0∞}
    (h0 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult x {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
        succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) (2 * δ'))) K X} ≤ ψ₀)
    (T0 r : ℝ≥0)
    (hr : (T0 : ℝ) * (2 * (3 * (2 * δ') + 2 * d) + (2 * δ + 2 * d)) + Real.exp (-(T0 : ℝ)) < r)
    (hap : ENNReal.ofReal c + (Q / ((m * ρt : ℝ≥0) : ℝ≥0∞) + (ψ₀ + (K : ℝ≥0∞) * ENNReal.ofReal ψ)) +
      (Q / ((m * ρt : ℝ≥0) : ℝ≥0∞) + (ψ₀ + (K : ℝ≥0∞) * ENNReal.ofReal ψ)) ≤ r) :
    ∀ z ∈ ball (0 : ℂ) ρ, ∀ x ∈ cellVertices ε η (ball z δ), ∀ y ∈ cellVertices ε η (ball z δ),
      levyProkhorovEDist
        ((srwLaw mult x).map
          (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0))))
        ((srwLaw mult y).map
          (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0)))) ≤ r := by
  intro z hz x hx y hy
  have hδs : δ ≤ Real.sqrt δ := by nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ]
  have hρ01 : ρ0 ≤ ρ1 := by linarith
  have hzb : ball z δ ⊆ ball (0 : ℂ) ρ0 := fun p hp => by
    rw [mem_ball] at hp hz ⊢
    calc dist p 0 ≤ dist p z + dist z 0 := dist_triangle _ _ _
      _ < δ + ρ := add_lt_add hp hz
      _ ≤ ρ0 := by linarith
  have hball : ball z (Real.sqrt δ) ⊆ ball (0 : ℂ) ρ0 := fun p hp => by
    rw [mem_ball] at hp hz ⊢
    calc dist p 0 ≤ dist p z + dist z 0 := dist_triangle _ _ _
      _ < Real.sqrt δ + ρ := add_lt_add hp hz
      _ ≤ ρ0 := by linarith
  have hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ d := by
    intro v hv p hp
    have hv' : (cell ε η v ∩ ball (0 : ℂ) ρ1).Nonempty :=
      Set.Nonempty.mono (inter_subset_inter_right _ (hzb.trans (ball_subset_ball hρ01))) hv
    exact hdiam v hv' _ (Lemma68C12Geom.vertexPoint_mem_cell hε v) p hp
  have hJ : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0), ∀ w' : ℤ, mult w w' ≠ 0 →
      dist (vertexPoint ε η w) (vertexPoint ε η w') ≤ 2 * d := by
    intro w hw w' hww'
    obtain ⟨p, hp', hp⟩ := hadj w' w hww'
    have hpb : p ∈ ball (0 : ℂ) ρ1 := by
      have := cell_subset_interior_of_mem_interiorCellVertices hη hw hp
      rw [isOpen_ball.interior_eq] at this
      exact ball_subset_ball hρ01 this
    have h1 := hdiam w ⟨p, hp, hpb⟩ _ (Lemma68C12Geom.vertexPoint_mem_cell hε w) p hp
    have h2 := hdiam w' ⟨p, hp', hpb⟩ _ (Lemma68C12Geom.vertexPoint_mem_cell hε w') p hp'
    calc dist (vertexPoint ε η w) (vertexPoint ε η w')
        ≤ dist (vertexPoint ε η w) p + dist p (vertexPoint ε η w') := dist_triangle _ _ _
      _ ≤ d + d := by rw [dist_comm p]; exact add_le_add h1 h2
      _ = 2 * d := by ring
  have hq := srwLaw_exitInterior_lt_le_of_exitTimeLower mult hε hη hδ' hd hdiam hρ1 hR₁ hgT h611
  have hx0 : x ∈ cellVertices ε η (ball (0 : ℂ) ρ0) :=
    Set.Nonempty.mono (inter_subset_inter_right _ hzb) hx
  have hy0 : y ∈ cellVertices ε η (ball (0 : ℂ) ρ0) :=
    Set.Nonempty.mono (inter_subset_inter_right _ hzb) hy
  exact levyProkhorovEDist_stoppedWalk_le_of_noShortTravel hε hη hδ hδ1 hcell hr0 hball (hA' z hz) hx hy
    (hTV z hz x hx y hy) hm ρt (by positivity) (by positivity) hg T0 r hJ hr (hfin x hx0) (hfin y hy0)
    (srwLaw_exitTimeScaled_gt_le mult _ x hm hρt (hQ z hz x))
    (srwLaw_exitTimeScaled_gt_le mult _ y hm hρt (hQ z hz y)) (h0 x hx0) (h0 y hy0) hq hap

end ExitCouplingGoodEnv
end MatedCRT
