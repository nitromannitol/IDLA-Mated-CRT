import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryDataBounds
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.LocalizedModulus

/-! Transfer of discrete equations to local measurable versions. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- An interior cell and each of its adjacent cells meet the disk. Thus the
degree-normalized Laplacian depends only on values on cells meeting the disk. -/
theorem matedLaplacian_eq_of_eqOn_cellVertices
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hη : Continuous η) (hr : 0 < r)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {u v : ℤ → ℝ} (huv : ∀ a ∈ cellVertices ε η (ball z r), u a = v a)
    {a : ℤ} (ha : a ∈ interiorCellVertices ε η (ball z r)) :
    matedLaplacian m u a = matedLaplacian m v a := by
  have haa := huv a (interiorCellVertices_subset _ _ _ ha)
  unfold matedLaplacian mLaplacian
  congr 1
  apply finsum_congr
  intro b
  by_cases hb : m a b = 0
  · simp [hb]
  · obtain ⟨x, hxa, hxb⟩ := hadj a b hb
    have hball := cell_subset_ball_of_mem_interiorCellVertices hη hr ha hxa
    rw [huv b ⟨x, hxb, hball⟩, haa]

/-- Local measurable versions on cells meeting the closed disk suffice for
the prepared interior modulus, even when the original field is arbitrary
outside those cells. -/
theorem MatedCRTEnv.IsValid.dirichlet_modulus_of_local_versions
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψ : ∃ C : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s)))
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hversion : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), v ω a = F ε ω a)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (t : ℝ) (ht : 0 < t) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < d ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ δ := by
  classical
  let G : ℝ → Ω → ℤ → ℝ := fun ε => if h : 0 < ε then Classical.choose (hversion ε h) else 0
  have hGm : ∀ ε, 0 < ε → ∀ a, Measurable[S.envSigma] fun ω => G ε ω a := by
    intro ε hε a
    simpa [G, hε] using (Classical.choose_spec (hversion ε hε)).1 a
  have hGeq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), G ε ω a = F ε ω a := by
    intro ε hε
    simpa [G, hε] using (Classical.choose_spec (hversion ε hε)).2
  have hGeqn : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (G ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        G ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b) := by
    intro ε hε
    filter_upwards [hGeq ε hε, hF ε hε, hS.isAreaParametrized,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω heq hf hη hadj
    constructor
    · intro a ha
      rw [matedLaplacian_eq_of_eqOn_cellVertices hη.1 hr (hadj ε hε)
        (fun b hb => heq b (Sec7.cellVertices_mono ball_subset_closedBall hb)) ha]
      exact hf.1 a ha
    · intro b hb
      rw [heq b (Sec7.cellVertices_mono sphere_subset_closedBall hb)]
      exact hf.2 b hb
  have hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), F ε ω a = G ε ω a := by
    intro ε hε
    filter_upwards [hGeq ε hε] with ω hω a ha
    exact (hω a ha).symm
  apply hS.rescale_modulus_of_ae_eqOn_cellVertices (closedBall z r) K
    (subset_closure.trans (hKD.trans ball_subset_closedBall)) F G hEq t
  apply hS.dirichlet_modulus_of_measurable_versions h31 h28 hm h218 h217 hγ hγ2 hρ hρ1
    hr hD ψ φ hψ hφ G hGeqn ?_ K hK hKD t ht hδ
  intro ε hε
  exact ⟨G ε, hGm ε hε, Filter.Eventually.of_forall fun _ => rfl⟩

end MatedCRT
