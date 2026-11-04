import MatedCRT.Proofs.Sec4.ConvergenceDivisible.AEFiniteApproximation
import MatedCRT.Proofs.Sec4.ObstacleSpecialization

/-! # Measurability of the mated discrete least supersolution -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- At a fixed vertex the mated discrete least supersolution is almost
everywhere measurable, provided the mated multigraph is locally finite. -/
theorem MatedCRTEnv.IsValid.aemeasurable_matedLeastSupersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε)
    (ρ t : ℝ) (ht : 0 < t) (a : ℤ)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite) :
    AEMeasurable (fun ω => matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a) S.P := by
  classical
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_interiorCellVertices ε (ball 0 ρ)
    (Or.inl isOpen_ball)
  obtain ⟨W, hW, hWa⟩ := hS.exists_measurable_cellVertices_set ε (closedBall 0 ρ)
    (Or.inr isClosed_closedBall)
  choose f hf hfa using fun b => hS.exists_measurable_matedObstacle ε ρ t b
  let φ : Ω → ℤ → ℝ := fun ω b => f b ω
  let r : Ω → ℤ → ℝ := fun ω b => (mdeg (S.mult ε ω) b : ℝ)⁻¹
  have hr : ∀ b, Measurable fun ω => r ω b := by
    intro b
    exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (hS.measurable_mdeg ε b)).inv
  have hgood : ∀ᵐ ω ∂S.P, V ω ⊆ W ω ∧ (∀ b, 0 ≤ r ω b) ∧
      (∀ b, φ ω b ≤ 0) ∧ (V ω).Finite ∧ (W ω).Finite ∧
      (∀ b ∈ V ω, {c | S.mult ε ω b c ≠ 0}.Finite) ∧
      (∀ b ∈ V ω, 0 < r ω b) := by
    filter_upwards [hVa, hWa, ae_all_iff.mpr hfa, hS.isAreaParametrized,
      etaProperStep_holds 𝒮 γ hγ hγ' Ω S hS, hlf] with ω hv hw hφ hη hp hωlf
    have hφeq : φ ω = matedObstacle (S.mult ε ω) ε (S.η ω) ρ t := by
      funext b
      exact hφ b
    rw [hv, hw, hφeq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun b hb => cellVertices_ball_subset_closedBall (ballInterior_subset_cellVertices_ball hb)
    · intro b
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact matedObstacle_nonpos ht.le hε.le
    · exact ballInterior_finite hη.1 hp hε
    · exact cellVertices_finite_of_isBounded hη.1 hp hε isBounded_closedBall
    · exact fun b _ => hωlf b
    · intro b _
      exact inv_pos.mpr (Nat.cast_pos.mpr (mdeg_pos_of_ne_zero hωlf
        (S.mult_succ_ne_zero hε.le ω b)))
  have hm := hS.aemeasurable_discreteLeastSupersolution_of_ae_finite ε V W hV hW
    r φ hr hf a hgood
  apply hm.congr
  filter_upwards [hVa, hWa, ae_all_iff.mpr hfa] with ω hv hw hφ
  have hφeq : φ ω = matedObstacle (S.mult ε ω) ε (S.η ω) ρ t := by
    funext b
    exact hφ b
  simp [matedLeastSupersolution, matedDeg, ballInterior, r, hv, hw, hφeq]

/-- The rescaled mated least supersolution has a jointly measurable version,
simultaneously for all spatial points. -/
theorem MatedCRTEnv.IsValid.exists_measurable_rescaledMatedLeastSupersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε)
    (ρ t : ℝ) (ht : 0 < t)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite) :
    ∃ F : Ω × ℂ → ℝ, Measurable F ∧ ∀ᵐ ω ∂S.P, ∀ x,
      F (ω, x) = rescaledMatedLeastSupersolution S ρ t ε ω x := by
  classical
  let w : ℤ → Ω → ℝ := fun b ω =>
    matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t b
  have hw : ∀ b, AEMeasurable (w b) S.P := fun b =>
    hS.aemeasurable_matedLeastSupersolution hγ hγ' hε ρ t ht b hlf
  let u : Ω → ℤ → ℝ := fun ω b => (hw b).mk (w b) ω
  have hu : ∀ b, Measurable fun ω => u ω b := fun b => (hw b).measurable_mk
  have huae : ∀ᵐ ω ∂S.P, ∀ b, u ω b = w b ω :=
    ae_all_iff.mpr fun b => (hw b).ae_eq_mk.symm
  obtain ⟨F, hF, hFa⟩ := hS.exists_measurable_rescale hε (S.mε ε) u hu
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFa, huae] with ω h1 h2
  intro x
  rw [h1 x]
  unfold rescaledMatedLeastSupersolution rescale
  rw [h2]

/-- The adjacent-cells input and properness of the curve imply local finiteness
at every positive mesh simultaneously. -/
theorem ae_locallyFinite_mult_of_adjacentCells
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite := by
  filter_upwards [hcell γ hγ hγ' Ω S hS,
    etaProperStep_holds 𝒮 γ hγ hγ' Ω S hS, hS.isAreaParametrized] with ω hc hp hη
  intro ε hε
  exact locallyFinite_of_cells_meet hη.1 hp hε (hc ε hε)

end MatedCRT
