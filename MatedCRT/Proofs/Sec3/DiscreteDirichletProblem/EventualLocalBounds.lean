import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableLocalBounds

/-! # Measurable local bounds under eventual agreement -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- If measurable vertex fields agree eventually with the given fields on
the cells of a bounded domain, an eventual pathwise bound transfers to a
measurable random bound. No agreement is required at earlier meshes. -/
theorem MatedCRTEnv.IsValid.exists_measurable_local_bound_of_eventual_agreement
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (hDb : Bornology.IsBounded D)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (F v : Ω → ℕ → ℤ → ℝ)
    (hvm : ∀ n a, Measurable[S.envSigma] fun ω => v ω n a)
    (hEq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) D, v ω n a = F ω n a)
    (hb : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) D, ε n * |F ω n a| ≤ C) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 1 ≤ C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        ∀ a ∈ cellVertices (ε n) (S.η ω) D, |F ω n a| ≤ C ω / ε n := by
  have hvbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) D, ε n * |v ω n a| ≤ C := by
    filter_upwards [hEq, hb] with ω heq ⟨C, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [heq, hC] with n hn hbound a ha
    rw [hn a ha]
    exact hbound a ha
  have hv : ∀ n, ∃ u : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => u ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices (ε n) (S.η ω) D, u ω a = v ω n a := by
    intro n
    exact ⟨fun ω a => v ω n a, hvm n, Filter.Eventually.of_forall fun _ _ _ => rfl⟩
  obtain ⟨C, hCm, hC, hbound⟩ :=
    hS.exists_measurable_local_bound_of_eventual D hD hDb ε hε v hv hvbound
  refine ⟨C, hCm, hC, ?_⟩
  filter_upwards [hEq, hbound] with ω heq hboundω
  filter_upwards [heq] with n hn a ha
  rw [← hn a ha]
  exact hboundω n a ha

end MatedCRT
