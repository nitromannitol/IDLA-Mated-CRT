import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.Measurability.EnvSigmaCore
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
    (hLower : Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0))
    (hStopped : Tendsto (fun ε => S.idlaSectionProb ε
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

/-- Transfer sectionwise lower bounds when the vertex-set coordinates are null-measurable. -/
theorem MatedCRTEnv.IsValid.joint_generalIDLABounds_of_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (O U : ℝ → Ω → Set ℤ) (K : ℝ → ℝ)
    (hO : ∀ ε k, NullMeasurableSet {ω | k ∈ O ε ω} S.P)
    (hU : ∀ ε k, NullMeasurableSet {ω | k ∈ U ε ω} S.P)
    (hLower : Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0))
    (hStopped : Tendsto (fun ε => S.idlaSectionProb ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · convert hLower using 1
    funext ε
    exact (hS.idlaProb_eq_joint_containment_of_nullMeasurable ε (O ε) (hO ε) ⌊K ε⌋₊).symm
  · convert hStopped using 1
    funext ε
    exact (hS.idlaProb_eq_joint_stopped_containment_of_nullMeasurable ε (O ε) (U ε)
      (hO ε) (hU ε) ⌊K ε⌋₊).symm

/-- A null-measurable envelope transfers sectionwise bounds even for an arbitrary target. -/
theorem MatedCRTEnv.IsValid.joint_generalIDLABounds_of_nullMeasurable_envelope
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (O G U : ℝ → Ω → Set ℤ) (K : ℝ → ℝ)
    (hG : ∀ ε k, NullMeasurableSet {ω | k ∈ G ε ω} S.P)
    (hU : ∀ ε k, NullMeasurableSet {ω | k ∈ U ε ω} S.P)
    (hSel : Tendsto (fun ε => S.P {ω | ¬ O ε ω ⊆ G ε ω}) (𝓝[>] 0) (𝓝 0))
    (hLower : Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ G ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0))
    (hStopped : Tendsto (fun ε => S.idlaSectionProb ε
      {p | ¬ G ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hLower', hStopped'⟩ := hS.joint_generalIDLABounds_of_nullMeasurable G U K hG hU hLower hStopped
  have transfer (clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ)
      (hclus : Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ G ε p.1 ⊆ clus ε p.1 p.2})
        (𝓝[>] 0) (𝓝 0)) :
      Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ clus ε p.1 p.2})
        (𝓝[>] 0) (𝓝 0) := by
    have h := hclus.add hSel
    rw [zero_add] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) (fun ε => ?_)
    refine hS.idlaJointMeasure_le_add_env ε _ _ _ ?_
    intro ω hω xs hx
    have hOG : O ε ω ⊆ G ε ω := by simpa using hω
    exact fun hGC => hx (hOG.trans hGC)
  exact ⟨transfer (fun ε _ xs => idlaCluster xs ⌊K ε⌋₊) hLower',
    transfer (fun ε ω xs => stoppedIDLACluster (U ε ω) xs ⌊K ε⌋₊) hStopped'⟩

/-- A measurable vertex-set envelope permits the general IDLA lower bound to be used for
an arbitrary target vertex set, provided the target lies in the envelope with high probability.
The target itself need not be measurable. -/
theorem MatedCRTEnv.IsValid.joint_generalIDLABounds_of_measurable_envelope
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (O G U : ℝ → Ω → Set ℤ) (K : ℝ → ℝ)
    (hG : ∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ G ε ω})
    (hU : ∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ U ε ω})
    (hSel : Tendsto (fun ε => S.P {ω | ¬ O ε ω ⊆ G ε ω}) (𝓝[>] 0) (𝓝 0))
    (hLower : Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ G ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0))
    (hStopped : Tendsto (fun ε => S.idlaSectionProb ε
      {p | ¬ G ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hLower', hStopped'⟩ := hS.joint_generalIDLABounds_of_sectionwise G U K hG hU hLower hStopped
  have transfer (clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ)
      (hclus : Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ G ε p.1 ⊆ clus ε p.1 p.2})
        (𝓝[>] 0) (𝓝 0)) :
      Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ clus ε p.1 p.2})
        (𝓝[>] 0) (𝓝 0) := by
    have h := hclus.add hSel
    rw [zero_add] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) (fun ε => ?_)
    refine hS.idlaJointMeasure_le_add_env ε _ _ _ ?_
    intro ω hω xs hx
    have hOG : O ε ω ⊆ G ε ω := by simpa using hω
    exact fun hGC => hx (hOG.trans hGC)
  exact ⟨transfer (fun ε _ xs => idlaCluster xs ⌊K ε⌋₊) hLower',
    transfer (fun ε ω xs => stoppedIDLACluster (U ε ω) xs ⌊K ε⌋₊) hStopped'⟩

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
