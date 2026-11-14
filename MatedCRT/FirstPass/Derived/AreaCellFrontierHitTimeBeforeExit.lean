import MatedCRT.FirstPass.Derived.AreaCellFirstFrontierBeforeExit

/-! # The frontier hitting time precedes the outer exit -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- Simultaneously for all shifts and admissible concentric balls, the first
frontier hitting time identifies the first frontier index, whose jump
occurs strictly before exit from any open set containing the scaled outer ball. -/
theorem ae_hitTime_frontier_scaled_jumpTime_lt_exit_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (hc : (areaCellConfig h hε m).IsCellConfiguration)
    (hpos : ∀ C, 0 < (areaCellConfig h hε m).holding C) (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ (ρ R d : ℝ) (K : ℕ), ρ < 1 → ρ ≤ R →
        (∀ k, (cell ε η k ∩ ball 0 1).Nonempty → diam (cell ε η k) ≤ d) →
        d < R - ρ →
        (((ξ K).1 : Set Plane) ∩ ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty →
        ∃ n : ℕ,
          hitTime {C : (areaCellConfig h hε m).cells |
            ((C.1 : Set Plane) ∩ frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty}
            (fun j => ξ (K + j)) = (n : ℕ∞) ∧
          (hitTime {C : (areaCellConfig h hε m).cells |
            ((C.1 : Set Plane) ∩ frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty}
            (fun j => ξ (K + j))).toNat = n ∧
          (((ξ (K + n)).1 : Set Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty ∧
          (∀ j < n, ¬ (((ξ (K + j)).1 : Set Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty) ∧
          ((ξ (K + n)).1 : Set Plane) ⊆ ball (Complex.orthonormalBasisOneI.repr 0) R ∧
          ∀ (p : (areaCellConfig h hε m).cells → Plane),
            (∀ C, p C ∈ (C.1 : Set Plane)) →
            (∀ j, (areaCellConfig h hε m).Adj (ξ (K + j)) (ξ (K + (j + 1)))) →
            (areaCellConfig h hε m).JumpTimesUnbounded (fun j => ξ (K + j)) →
            ∀ (a : ℝ≥0), 0 < a → ∀ W : Set Plane, IsOpen W →
              (∀ z ∈ ball (Complex.orthonormalBasisOneI.repr 0) R, (a : ℝ) • z ∈ W) →
              ∃ t : ℝ≥0,
                (t : ℝ) = (a : ℝ) ^ 2 * (areaCellConfig h hε m).jumpTime (fun j => ξ (K + j))
                  (hitTime {C : (areaCellConfig h hε m).cells |
                    ((C.1 : Set Plane) ∩ frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty}
                    (fun j => ξ (K + j))).toNat ∧
                (t : ℝ≥0∞) < continuousExitTime W 0
                  ((areaCellConfig h hε m).interpolatedWalk p a (fun j => ξ (K + j))) := by
  filter_upwards [ae_exists_first_frontier_hit_scaled_jumpTime_lt_exit_areaCell
    h hε m hlf H hH hconn hc hpos x] with ξ hξ
  intro ρ R d K hρ hρR hd hgap hstart
  obtain ⟨n, hn, hbefore, hlast, htime⟩ := hξ ρ R d K hρ hρR hd hgap hstart
  have heq : hitTime {C : (areaCellConfig h hε m).cells |
      ((C.1 : Set Plane) ∩ frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty}
      (fun j => ξ (K + j)) = (n : ℕ∞) :=
    hitTime_eq_coe_iff.mpr ⟨hn, hbefore⟩
  refine ⟨n, heq, ?_, hn, hbefore, hlast, ?_⟩
  · rw [heq]
    simp
  · rw [heq, ENat.toNat_natCast]
    exact htime

end MatedCRT
end
