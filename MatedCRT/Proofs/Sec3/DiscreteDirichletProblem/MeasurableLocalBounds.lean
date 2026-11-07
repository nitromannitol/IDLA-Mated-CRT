import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.MeasurableUniformBound
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells

/-! Measurable random bounds for data restricted to a bounded region. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- An eventual pathwise bound on the cells meeting a bounded region admits an
    environment-measurable positive bound, provided the vertex values have
    measurable versions on those cells. -/
theorem MatedCRTEnv.IsValid.exists_measurable_local_bound_of_eventual
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (hDb : Bornology.IsBounded D)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (F : Ω → ℕ → ℤ → ℝ)
    (hF : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices (ε n) (S.η ω) D, v ω a = F ω n a)
    (hb : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) D, ε n * |F ω n a| ≤ C) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 1 ≤ C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ n, ∀ a ∈ cellVertices (ε n) (S.η ω) D,
        |F ω n a| ≤ C ω / ε n := by
  classical
  choose v hvm hva using hF
  choose V hVm hVa using fun n => hS.exists_envSigma_measurable_cellVertices (ε n) D hD
  let f : Ω → ℕ → ℤ → ℝ := fun ω n a =>
    if a ∈ V n ω then ε n * |v n ω a| else 0
  have hfm : ∀ n a, Measurable[S.envSigma] fun ω => f ω n a := by
    intro n a
    let : MeasurableSpace Ω := S.envSigma
    have hmem : MeasurableSet {ω | a ∈ V n ω} :=
      measurableSet_setOfPred.mpr ((measurable_set_mem a).comp (hVm n))
    exact (measurable_const.mul (hvm n a).abs).ite hmem measurable_const
  have hf0 : ∀ ω n a, 0 ≤ f ω n a := by
    intro ω n a
    dsimp [f]
    split_ifs
    · exact mul_nonneg (hε n).le (abs_nonneg _)
    · exact le_rfl
  have hall : ∀ᵐ ω ∂S.P, (∀ n, V n ω = cellVertices (ε n) (S.η ω) D) ∧
      (∀ n, ∀ a ∈ cellVertices (ε n) (S.η ω) D, v n ω a = F ω n a) :=
    (ae_all_iff.mpr hVa).and (ae_all_iff.mpr hva)
  have hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ n a, f ω n a ≤ C := by
    filter_upwards [hall, hb, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hω ⟨C, htail⟩ hη hp
    have hs : ∀ n, ∃ B : ℝ, ∀ a : ℤ, f ω n a ≤ B := by
      intro n
      have hfin := Tightness.cellVertices_finite hη.1 hp (hε n) hDb
      let g : ℤ → ℝ := fun a => ε n * |v n ω a|
      obtain ⟨B, hB⟩ := ((hfin.image g).union (Set.finite_singleton 0)).bddAbove
      refine ⟨B, fun a => ?_⟩
      by_cases ha : a ∈ cellVertices (ε n) (S.η ω) D
      · have : a ∈ V n ω := by simpa only [hω.1 n] using ha
        simpa [f, this, g] using hB (Set.mem_union_left _ ⟨a, ha, rfl⟩)
      · have : a ∉ V n ω := by simpa only [hω.1 n] using ha
        simpa [f, this] using hB (Set.mem_union_right _ (Set.mem_singleton 0))
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail
    choose B hB using hs
    obtain ⟨B₀, hB₀⟩ := ((Finset.finite_toSet (Finset.range N)).image B).bddAbove
    refine ⟨max B₀ (max C 0), fun n a => ?_⟩
    by_cases hn : n < N
    · exact (hB n a).trans ((hB₀ ⟨n, Finset.mem_range.mpr hn, rfl⟩).trans (le_max_left _ _))
    · by_cases ha : a ∈ cellVertices (ε n) (S.η ω) D
      · have hav : a ∈ V n ω := by simpa only [hω.1 n] using ha
        have hle := hN n (Nat.le_of_not_gt hn) a ha
        have : f ω n a ≤ C := by simpa [f, hav, hω.2 n a ha] using hle
        exact this.trans (le_trans (le_max_left _ _) (le_max_right _ _))
      · have hav : a ∉ V n ω := by simpa only [hω.1 n] using ha
        have : f ω n a = 0 := by simp [f, hav]
        rw [this]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨C, hCm, hC, hf⟩ := exists_measurable_uniform_bound S.P S.envSigma f hfm hf0 hbound
  refine ⟨C, hCm, hC, ?_⟩
  filter_upwards [hf, hall] with ω hω hEq n a ha
  apply (le_div_iff₀ (hε n)).2
  have hav : a ∈ V n ω := by simpa only [hEq.1 n] using ha
  simpa [f, hav, hEq.2 n a ha, mul_comm] using hω n a

end MatedCRT
