import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec5.IDLALowerBound.Geometry

/-! # Joint-law form of the general IDLA lower bound

The domains in Lemma 5.2 are measurable for the environment sigma algebra. Its coordinate
events are null-measurable for the ambient probability space, which suffices to transfer the
sectionwise bounds to joint outer measure.
-/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory Filter Topology Metric

/-- Transfer the stopped and unstopped convergence conclusions of Lemma 5.2 to the joint law. -/
theorem MatedCRTEnv.IsValid.joint_generalIDLABounds_of_sectionwise
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (O₁ O₂ : ℝ → Ω → Set ℤ) (K : ℝ → ℝ)
    (hO₁ : ∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₁ ε ω})
    (hO₂ : ∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₂ ε ω})
    (hLower : Tendsto (fun ε => S.idlaProb ε {p | ¬ O₁ ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0))
    (hStopped : Tendsto (fun ε => S.idlaProb ε
      {p | ¬ O₁ ε p.1 ⊆ stoppedIDLACluster (O₂ ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O₁ ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O₁ ε p.1 ⊆ stoppedIDLACluster (O₂ ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · convert hLower using 1
    funext ε
    exact (hS.idlaProb_eq_joint_containment_of_nullMeasurable ε (O₁ ε)
      (fun k => hS.nullMeasurableSet_of_envSigma (hO₁ ε k)) ⌊K ε⌋₊).symm
  · convert hStopped using 1
    funext ε
    exact (hS.idlaProb_eq_joint_stopped_containment_of_nullMeasurable ε (O₁ ε) (O₂ ε)
      (fun k => hS.nullMeasurableSet_of_envSigma (hO₁ ε k))
      (fun k => hS.nullMeasurableSet_of_envSigma (hO₂ ε k)) ⌊K ε⌋₊).symm

/-- The geometric step of Proposition 5.1 transfers a joint-law vertex containment bound to a
cell-union bound. The harmonic-ball family and the exceptional sets need not be measurable. -/
theorem MatedCRTEnv.IsValid.joint_innerBound_of_deep_vertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (F : Set Ω) (X : Ω → Set ℂ) (L : ℝ → Ω → Set ℤ)
    (clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ) (δ ρ : ℝ) (hδ : 0 < δ)
    (hball : ∀ ε ω a, a ∈ L ε ω → (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty)
    (hdeep : Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ {a ∈ L ε p.1 | p.1 ∈ F ∧ δ / 4 < infDist (vertexPoint ε (S.η p.1) a)
        (frontier (fillCells ε (S.η p.1) (L ε p.1)))} ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0))
    (hbad : Tendsto (fun ε => S.P
      ((F ∩ {ω | innerNbhd (δ / 2) (X ω) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪
        {ω | ¬ ∀ a ∈ L ε ω, Bornology.IsBounded (cell ε (S.η ω) a) ∧
          diam (cell ε (S.η ω) a) < δ / 4})) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | p.1 ∈ F ∧ ¬ innerNbhd δ (X p.1) ⊆ fillCells ε (S.η p.1) (clus ε p.1 p.2)})
      (𝓝[>] 0) (𝓝 0) := by
  have h := hdeep.add hbad
  rw [zero_add] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine hS.idlaJointMeasure_le_add_env ε _ _ _ ?_
  intro ω hω xs hx
  simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_or, not_and, not_not] at hω
  obtain ⟨hF, hnot⟩ := hx
  have hin := hω.1 hF
  have hsmall := hω.2
  intro hsub
  apply hnot
  have hb : ∀ a ∈ L ε ω, Bornology.IsBounded (cell ε (S.η ω) a) := fun a ha => (hsmall a ha).1
  have hd : ∀ a ∈ L ε ω, diam (cell ε (S.η ω) a) < δ / 4 := fun a ha => (hsmall a ha).2
  calc
    innerNbhd δ (X ω) ⊆ fillCells ε (S.η ω) {a ∈ L ε ω |
        δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} :=
      IDLALowerBound.innerNbhd_subset_fillCells_deep hε.le hδ hb hd (hball ε ω) hin
    _ ⊆ fillCells ε (S.η ω) {a ∈ L ε ω | ω ∈ F ∧
        δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} :=
      IDLALowerBound.fillCells_mono' fun a ha => ⟨ha.1, hF, ha.2⟩
    _ ⊆ fillCells ε (S.η ω) (clus ε ω xs) := IDLALowerBound.fillCells_mono' hsub

end MatedCRT
