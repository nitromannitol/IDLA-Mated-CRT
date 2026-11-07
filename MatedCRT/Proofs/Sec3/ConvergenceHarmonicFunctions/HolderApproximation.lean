import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Lipschitz approximation of continuous boundary data -/

namespace MatedCRT

open Set Metric
open scoped NNReal Topology

/-- Lipschitz real functions are uniformly dense on compact metric spaces. -/
theorem exists_lipschitz_approximation {X : Type} [MetricSpace X] [CompactSpace X]
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(X, ℝ)) (K : ℝ≥0), LipschitzWith K g ∧ ∀ x, |g x - f x| < ε := by
  let L : Set C(X, ℝ) := {g | ∃ K : ℝ≥0, LipschitzWith K g}
  have hn : L.Nonempty := ⟨0, ⟨0, LipschitzWith.const 0⟩⟩
  have hinf : ∀ᵉ (g ∈ L) (h ∈ L), g ⊓ h ∈ L := by
    rintro g ⟨K, hg⟩ h ⟨J, hh⟩
    exact ⟨max K J, hg.min hh⟩
  have hsup : ∀ᵉ (g ∈ L) (h ∈ L), g ⊔ h ∈ L := by
    rintro g ⟨K, hg⟩ h ⟨J, hh⟩
    exact ⟨max K J, hg.max hh⟩
  have hsep : L.SeparatesPointsStrongly := by
    intro v x y
    by_cases hxy : x = y
    · subst y
      refine ⟨ContinuousMap.const X (v x), ⟨0, LipschitzWith.const _⟩, ?_, ?_⟩ <;> rfl
    · let c : ℝ := (v y - v x) / dist y x
      have hd : LipschitzWith ‖c‖₊ (fun t : X => v x + c * dist t x) := by
        have hh := (lipschitzWith_smul c).comp (LipschitzWith.dist_left x)
        have := (LipschitzWith.const (v x)).add hh
        simpa only [zero_add, mul_one, smul_eq_mul, Function.comp_def] using this
      let g : C(X, ℝ) := ⟨fun t => v x + c * dist t x, hd.continuous⟩
      refine ⟨g, ⟨‖c‖₊, hd⟩, ?_, ?_⟩
      · simp [g]
      · dsimp [g, c]
        have hne : dist y x ≠ 0 := dist_ne_zero.mpr (Ne.symm hxy)
        field_simp
        ring
  have hclosure := ContinuousMap.sublattice_closure_eq_top L hn hinf hsup hsep
  have hf : f ∈ closure L := by rw [hclosure]; simp
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨K, hK⟩ := hg
  refine ⟨g, K, hK, fun x => ?_⟩
  simpa only [Real.dist_eq, abs_sub_comm] using (ContinuousMap.dist_lt_iff hε).mp hdist x

/-- The projected exit-cell comparison holds for arbitrary continuous data on
the closed disk. -/
theorem correctedProjectedExitCellStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) : CorrectedProjectedExitCellStep 𝒮 := by
  classical
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy
  have hcompact : IsCompact (closedBall z r) := isCompact_closedBall z r
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn hψ
  have hK' : ∀ x ∈ closedBall z r, |ψ x| ≤ K := fun x hx => by
    simpa only [Real.norm_eq_abs] using hK x hx
  apply correctedProjectedExit_of_uniform_approximations 𝒮 h211 hmeps hexc hX h28
    hγ hγ2 hρ hρ1 S hS hr hball hK' _ hy
  intro η hη
  let _ : CompactSpace (closedBall z r) := isCompact_iff_compactSpace.mp hcompact
  let f : C(closedBall z r, ℝ) := ⟨fun x => ψ x, continuousOn_iff_continuous_domRestrict.mp hψ⟩
  obtain ⟨g, C, hC, hg⟩ := exists_lipschitz_approximation f hη
  let φ : ℂ → ℝ := fun x => if hx : x ∈ closedBall z r then g ⟨x, hx⟩ else 0
  have hφ : ∀ x (hx : x ∈ closedBall z r), φ x = g ⟨x, hx⟩ := by
    intro x hx
    dsimp only [φ]
    rw [dite_eq_left hx]
  have hclose : ∀ x ∈ closedBall z r, |ψ x - φ x| ≤ η := by
    intro x hx
    rw [hφ x hx, abs_sub_comm]
    exact (hg ⟨x, hx⟩).le
  have hφbound : ∀ x ∈ closedBall z r, |φ x| ≤ K + η := by
    intro x hx
    have htri := abs_add_le (φ x - ψ x) (ψ x)
    have heq : φ x - ψ x + ψ x = φ x := by ring
    rw [heq, abs_sub_comm] at htri
    linarith [hclose x hx, hK' x hx]
  have hlip : LipschitzOnWith C φ (closedBall z r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx w hw
    simp only [hφ x hx, hφ w hw]
    exact hC.dist_le_mul ⟨x, hx⟩ ⟨w, hw⟩
  have hholder : IsHolderContinuousOn φ (closedBall z r) :=
    ⟨C, 1, by norm_num, le_rfl, hlip.holderOnWith⟩
  exact ⟨φ, K + η, hφbound, hclose, 1, by norm_num,
    holder_ballRetraction hr (by linarith) z hholder⟩

end MatedCRT
