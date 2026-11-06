import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedPointBounds
import MatedCRT.Steps.Sec4.SubsequentialConvergencePrepared
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Measurable selection for the prepared form of Lemma 4.6. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Every nonempty closed disc has a countable dense sequence of its own points. -/
theorem exists_denseSeq_closedBall {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ x : ℕ → ℂ, (∀ i, x i ∈ closedBall (0 : ℂ) ρ) ∧
      closedBall (0 : ℂ) ρ ⊆ closure (range x) := by
  let K : Set ℂ := closedBall 0 ρ
  let : Nonempty K := ⟨⟨0, mem_closedBall_self hρ.le⟩⟩
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq K
  refine ⟨fun n => (y n : ℂ), fun n => (y n).2, ?_⟩
  intro x hx
  have hz : (⟨x, hx⟩ : K) ∈ closure (range y) := hy _
  have him := image_closure_subset_closure_image continuous_subtype_val
    (show (x : ℂ) ∈ Subtype.val '' closure (range y) from ⟨⟨x, hx⟩, hz, rfl⟩)
  convert him using 1
  congr 1
  ext z
  simp

/-- The prepared compactness assertion admits an environment-measurable
uniformly convergent subsequence. -/
theorem odometerPreparedSelectionStep (𝒮 : SpaceFillingSLEModel) :
    OdometerPreparedSelectionStep 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0 hc
  obtain ⟨x, hx, hxd⟩ := exists_denseSeq_closedBall hρ
  have hlf := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' (adjacentCellsMeetAeStep 𝒮)
  have hlf' : ∀ n, ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult (e n) ω b c ≠ 0}.Finite := by
    intro n
    filter_upwards [hlf] with ω hω
    exact hω (e n) (he n)
  have hb : ∀ᵐ ω ∂S.P, ∀ i, ∃ M : ℝ, ∀ᶠ n in atTop,
      |rescaledMatedLeastSupersolution S ρ t (e n) ω (x i)| ≤ M := by
    filter_upwards [hc] with ω hω i
    exact hω.eventually_bounded_at (hx i)
  exact hS.exists_envSigma_uniform_odometer_subsequence hγ hγ' e he ρ t ht x hx hxd hlf' hc hb

/-- Lemma 4.6 in prepared form follows from its compactness step. -/
theorem subsequentialConvergencePrepared_of_compactness (𝒮 : SpaceFillingSLEModel)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hc : OdometerPreparedCompactnessStep 𝒮) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_steps 𝒮 h47 h44 h31 h35 hc
    (odometerPreparedSelectionStep 𝒮)

end MatedCRT
