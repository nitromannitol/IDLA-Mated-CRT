import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedBarrierDecay

/-! Harmonic comparison with prescribed discrete boundary values. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- A function on a finite disk has a harmonic comparison which agrees with
it on every boundary cell. -/
theorem exists_harmonic_comparison_on_disk
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0) (u : ℤ → ℝ) :
    ∃ h : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices ε η (ball z r), matedLaplacian m h a = 0) ∧
      (∀ b ∈ cellVertices ε η (sphere z r), u b = h b) := by
  let A := interiorCellVertices ε η (ball z r)
  have hlf := Tightness.isLocallyFiniteMult_of_cells hη hp hε hadj
  have hAfin : A.Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset (fun _ ha => ha.1)
  have hesc := escape_of_adjacent_succ hsucc hAfin
  obtain ⟨h, hoff, hlap⟩ := Tightness.exists_lapSum_eq hlf hAfin hesc u (fun _ => 0)
  refine ⟨h, ?_, ?_⟩
  · intro a ha
    change mLaplacian m h a = 0
    rw [mLaplacian_eq_div hlf, hlap a ha, zero_div]
  · intro b hb
    have hb' : b ∉ A := fun h => h.2 (by simpa [frontier_ball z hr.ne'] using hb)
    exact (hoff b hb').symm

/-- For a positive mesh sequence, one can select harmonic comparisons on a
single almost-sure event, simultaneously for all mesh indices. -/
theorem ae_exists_harmonic_comparisons
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (u : Ω → ℕ → ℤ → ℝ) :
    ∃ h : Ω → ℕ → ℤ → ℝ, ∀ᵐ ω ∂S.P, ∀ n,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (h ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u ω n b = h ω n b) := by
  classical
  have hex : ∀ᵐ ω ∂S.P, ∀ n, ∃ h : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) h a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u ω n b = h b) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω harea hp hadj
    intro n
    exact exists_harmonic_comparison_on_disk (he n) hr harea.1 hp (hadj (e n) (he n))
      (S.mult_succ_ne_zero (he n).le ω) (u ω n)
  let h : Ω → ℕ → ℤ → ℝ := fun ω n => if hx : ∃ h : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) h a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u ω n b = h b)
    then Classical.choose hx else fun _ => 0
  refine ⟨h, ?_⟩
  filter_upwards [hex] with ω hω
  intro n
  simpa [h, dite_eq_left (hω n)] using Classical.choose_spec (hω n)

/-- Projected Dirichlet data admit harmonic comparisons satisfying the
prepared boundary and source conditions along any positive mesh sequence. -/
theorem ae_exists_projected_harmonic_comparisons
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (ψ φ : ℂ → ℝ) {C : ℝ}
    (hψ : ∀ x ∈ ball z r, |ψ x| ≤ C) (u : ℝ → Ω → ℤ → ℝ)
    (hdata : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (u ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      (∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        u ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b)))) :
    ∃ h : Ω → ℕ → ℤ → ℝ, ∀ᵐ ω ∂S.P, ∀ n,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (u (e n) ω) a| ≤ C) ∧
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (h ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u (e n) ω b = h ω n b) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)),
        h ω n b = S.mε (e n) * φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b))) := by
  obtain ⟨h, hh⟩ := ae_exists_harmonic_comparisons hγ hγ2 S hS hr e he (fun ω n => u (e n) ω)
  refine ⟨h, ?_⟩
  filter_upwards [hh, ae_all_iff.mpr (fun n => hdata (e n) (he n)), hS.isAreaParametrized]
    with ω hhω hdω harea
  intro n
  refine ⟨?_, (hhω n).1, (hhω n).2, ?_⟩
  · intro a ha
    rw [(hdω n).1 a ha]
    apply hψ
    exact Sec7.cell_subset_ball_of_mem_interiorCellVertices harea.1 ha
      (Sec7.vertexPoint_mem_cell (he n).le a)
  · intro b hb
    have hb' : b ∈ cellVertices (e n) (S.η ω) (sphere z r) := by
      simpa [frontier_ball z hr.ne'] using hb
    exact ((hhω n).2 b hb').symm.trans ((hdω n).2 b hb')

/-- For projected Dirichlet solutions the boundary-pair modulus follows
from ordinary exit-time boundary decay, without assuming a harmonic
comparison as additional data. -/
theorem ae_projected_boundary_pair_modulus_of_exitTime_boundary_decay
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r))
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (ψ φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z r))
    {C : ℝ} (hC : 0 ≤ C) (hψ : ∀ x ∈ ball z r, |ψ x| ≤ C)
    (u : ℝ → Ω → ℤ → ℝ)
    (hdata : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (u ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      (∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        u ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))))
    (hq : ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
        (S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
          (interiorCellVertices (e n) (S.η ω) (ball z r))
          (vertexOf (e n) (S.η ω) x)).toReal ≤ k) :
    ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
        |rescale (S.mε (e n)) (e n) (S.η ω) (u (e n) ω) x -
          rescale (S.mε (e n)) (e n) (S.η ω) (u (e n) ω) y| ≤ k := by
  obtain ⟨h, hh⟩ := ae_exists_projected_harmonic_comparisons hγ hγ2 S hS hr e he.1
    ψ φ hψ u hdata
  apply ae_boundary_pair_modulus_of_exitTime_boundary_decay hH hm h218 h217
    hγ hγ2 hρ hρ1 S hS hr hD hsimply e he he0 φ hφ
    (fun ω n => u (e n) ω) h hC ?_ hq
  filter_upwards [hh] with ω hω
  exact Eventually.of_forall hω

end MatedCRT

#print axioms MatedCRT.exists_harmonic_comparison_on_disk
#print axioms MatedCRT.ae_exists_harmonic_comparisons
#print axioms MatedCRT.ae_exists_projected_harmonic_comparisons
#print axioms MatedCRT.ae_projected_boundary_pair_modulus_of_exitTime_boundary_decay
