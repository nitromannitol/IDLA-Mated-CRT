import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.Measurability.EnvSigma

/-! # Joint-law form of the general IDLA lower bound

The domains in Lemma 5.2 are measurable for the environment sigma algebra. Its coordinate
events are null-measurable for the ambient probability space, which suffices to transfer the
sectionwise bounds to joint outer measure.
-/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory Filter Topology

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

end MatedCRT
