import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable

/-! # Measurability of the discrete obstacle cluster -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- Each vertex membership event for the discrete cluster is null-measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_mem_matedDiscreteCluster
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε)
    (ρ t : ℝ) (ht : 0 < t) (a : ℤ)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite) :
    NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t} S.P := by
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_cellVertices_set ε (ball 0 ρ) (Or.inl isOpen_ball)
  obtain ⟨φ, hφ, hφa⟩ := hS.exists_measurable_matedObstacle ε ρ t a
  have hw := hS.aemeasurable_matedLeastSupersolution hγ hγ' hε ρ t ht a hlf
  have hφ' : AEMeasurable (fun ω => matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a) S.P :=
    hφ.aemeasurable.congr hφa
  have hmem : NullMeasurableSet {ω | a ∈ cellVertices ε (S.η ω) (ball 0 ρ)} S.P := by
    apply NullMeasurableSet.congr (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hV)).nullMeasurableSet
    filter_upwards [hVa] with ω hω
    simp [hω]
  exact hmem.inter (nullMeasurableSet_lt hφ' hw)

end MatedCRT
