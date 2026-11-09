import MatedCRT.Defs.Setting
import MatedCRT.Proofs.IDLA.WalkerLawMeasurable
import MatedCRT.FirstPass.S5d.CoverEvent

/-!
# FIRST PASS, Proposition 5.1: from the vertex-threshold cover to the IDLA cluster

Transfer step of the proof of Proposition 5.1 (paper lines 2343-2358). Given (i) the cover of `B⁻_δ(Λ_t)` by the cells
of the vertex-threshold sets `O₁ = vertexThresholdSet` with probability tending to one (`tendsToOneOn_cover_vertexThresholdSet`),
and (ii) the conclusion of Lemma 5.2 (`GeneralIDLALowerBoundStmt`, first conjunct) for these sets `O₁`, the first conjunct of
`IDLALowerBoundStmt` follows. The hypotheses of Lemma 5.2 for `O₁` (`0 ∈ O₁`, connectivity, mean-value inequalities) are NOT
discharged here: that is gaps G1a/G1b of `notes/z5.md`, and (ii) is taken as an input.

The outer-probability facts used (subadditivity, monotonicity, the environment bound `idlaJointMeasure_env_le`) are
proved here from the definition `jointOuterProb` (Defs/Notation.lean) and the existing environment bound in
`MatedCRT/Proofs/IDLA/WalkerLawMeasurable.lean` (reused by import).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem jointOuterProb_mono_fp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) {E E' : Set (Ω × X)} (h : E ⊆ E') :
    jointOuterProb P κ E ≤ jointOuterProb P κ E' := by
  unfold jointOuterProb
  split_ifs with hκ
  · exact measure_mono h
  · exact le_rfl

theorem jointOuterProb_union_le_fp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) (E₁ E₂ : Set (Ω × X)) :
    jointOuterProb P κ (E₁ ∪ E₂) ≤ jointOuterProb P κ E₁ + jointOuterProb P κ E₂ := by
  unfold jointOuterProb
  split_ifs with hκ
  · exact measure_union_le _ _
  · simp

/-- Outer-probability transfer: an event contained in `E₁ ∪ (X ×ˢ univ)` has `idlaProb` at most the `idlaProb` of
`E₁` plus the environment probability of `X`. -/
theorem idlaProb_le_of_subset_union_env_fp {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    {B E₁ : Set (Ω × (ℕ → ℕ → ℤ))} {X : Set Ω} (hsub : B ⊆ E₁ ∪ X ×ˢ univ) :
    S.idlaProb ε B ≤ S.idlaProb ε E₁ + S.P X := by
  have henv := hS.idlaJointMeasure_env_le ε X
  have hκ : ∀ E : Set (Ω × (ℕ → ℕ → ℤ)),
      S.idlaProb ε E = jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E :=
    fun E => (S.jointOuterProb_eq_idlaJointMeasure ε E).symm
  rw [hκ B, hκ E₁]
  calc jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) B
      ≤ jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) (E₁ ∪ X ×ˢ univ) :=
        jointOuterProb_mono_fp _ _ hsub
    _ ≤ jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E₁ +
          jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) (X ×ˢ univ) :=
        jointOuterProb_union_le_fp _ _ _ _
    _ ≤ jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E₁ + S.P X :=
        add_le_add le_rfl ((S.jointOuterProb_eq_idlaJointMeasure ε _).le.trans henv)

/-- **Proposition 5.1, first conjunct, from the vertex-threshold cover** (paper lines 2343-2358). Inputs:
`hcover` (cover with probability tending to one, from `tendsToOneOn_cover_vertexThresholdSet`) and `hO1`, the first
conjunct of Lemma 5.2 for the sets `O₁ = vertexThresholdSet`. -/
theorem idlaLowerBound_unstopped_of_vertexThreshold {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ ρ : ℝ} (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (Λ : Ω → ℝ → Set ℂ) (δ t : ℝ) (L : ℝ → Ω → Set ℤ)
    (hcover : TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (vertexThresholdSet ε (S.η ω) (L ε ω) ρ δ)})
    (hO1 : Tendsto (fun ε => S.idlaProb ε {p | ¬ vertexThresholdSet ε (S.η p.1) (L ε p.1) ρ δ ⊆
        idlaCluster p.2 ⌊t / ε⌋₊}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊)}) (𝓝[>] 0) (𝓝 0) := by
  unfold TendsToOneOn at hcover
  have hsum := hO1.add hcover
  rw [add_zero] at hsum
  have hz0 : ∀ x : ℝ≥0∞, (0 : ℝ≥0∞) ≤ x := fun x => zero_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => hz0 _) (Eventually.of_forall fun ε => ?_)
  apply idlaProb_le_of_subset_union_env_fp hS ε
  rintro p ⟨hF, hnc⟩
  by_cases hE : vertexThresholdSet ε (S.η p.1) (L ε p.1) ρ δ ⊆ idlaCluster p.2 ⌊t / ε⌋₊
  · right
    refine ⟨⟨hF, fun (hcov : innerNbhd δ (Λ p.1 t) ⊆
        fillCells ε (S.η p.1) (vertexThresholdSet ε (S.η p.1) (L ε p.1) ρ δ)) =>
      hnc (hcov.trans (IDLALowerBound.fillCells_mono' hE))⟩, mem_univ _⟩
  · left
    exact hE

end MatedCRT
