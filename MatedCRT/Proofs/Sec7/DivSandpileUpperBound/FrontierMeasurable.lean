import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RandomSetRegularization
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Interior

/-! Pointwise measurability of boundaries of random open sets.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Filter Topology TopologicalSpace Metric _root_.HarmonicBalls

/-- Pointwise null measurability of a random open set implies the same for its
closure. -/
theorem nullMeasurableSet_mem_closure_of_open_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    (hmem : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ A ω} P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (A ω)) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ closure (A ω)} P := by
  obtain ⟨C, hC, hdense⟩ := exists_countable_dense ℂ
  have hm := nullMeasurableSet_mem_closure_inter_countable P A hC (fun z _ => hmem z) x
  apply hm.congr
  filter_upwards [hopen] with ω hω
  have heq : closure (A ω) = closure (A ω ∩ C) :=
    (closure_minimal (hdense.open_subset_closure_inter hω) isClosed_closure).antisymm
      (closure_mono inter_subset_left)
  simp [heq]

/-- For a random open set with null-measurable point membership, every fixed
point has null-measurable frontier membership. -/
theorem nullMeasurableSet_mem_frontier_of_open_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    (hmem : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ A ω} P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (A ω)) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ frontier (A ω)} P := by
  have hm := (nullMeasurableSet_mem_closure_of_open_ae P A hmem hopen x).diff (hmem x)
  apply hm.congr
  filter_upwards [hopen] with ω hω
  simp [frontier, hω.interior_eq]


/-- Before exit, point membership in the cone harmonic ball is null measurable
from the local obstacle representation and a measurable exit event. -/
theorem nullMeasurableSet_beforeExit_mem_coneFamily
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ x ∈ Λ ω t} S.P := by
  have hm := hexit.inter (hS.nullMeasurableSet_mem_regularizedLocalCluster
    hγ hγ' h27 hρ hρ' ht x)
  apply hm.congr
  filter_upwards [hΛ] with ω hω
  by_cases hT : t < clusterExitTime (Λ ω) ρ
  · have hsub := coneFamily_subset_before_exit hω ht hT
    have heq : Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) :=
      (hω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
    simp [hT, heq]
  · simp [hT]

/-- Before exit, every fixed point has null-measurable membership in the cone
harmonic-ball frontier. -/
theorem nullMeasurableSet_beforeExit_mem_frontier
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ x ∈ frontier (Λ ω t)} S.P := by
  classical
  let A : Ω → Set ℂ := fun ω => if t < clusterExitTime (Λ ω) ρ then Λ ω t else ∅
  have hmem : ∀ z, NullMeasurableSet {ω | z ∈ A ω} S.P := by
    intro z
    have hm := nullMeasurableSet_beforeExit_mem_coneFamily hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit z
    convert hm using 1
    ext ω
    simp [A]
  have hopen : ∀ᵐ ω ∂S.P, IsOpen (A ω) := by
    filter_upwards [hΛ] with ω hω
    dsimp [A]
    split_ifs
    · exact (hω.1 t ht).1
    · exact isOpen_empty
  have hm := hexit.inter (nullMeasurableSet_mem_frontier_of_open_ae S.P A hmem hopen x)
  convert hm using 1
  ext ω
  by_cases hT : t < clusterExitTime (Λ ω) ρ <;> simp [A, hT]

end MatedCRT.Sec7
