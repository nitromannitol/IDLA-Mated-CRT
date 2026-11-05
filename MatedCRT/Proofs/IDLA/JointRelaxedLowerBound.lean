import MatedCRT.Proofs.IDLA.JointLowerBound
import MatedCRT.Proofs.IDLA.RandomDomainGreen
import MatedCRT.Steps.Sec5.IDLALowerBound

/-! # Joint-law form of the relaxed IDLA lower bound -/

namespace MatedCRT

open Set MeasureTheory Filter Topology Metric

/-- A null-measurable stopping domain allows the relaxed lower bound to be
transferred to the joint law, even when the target domain is not measurable. -/
theorem MatedCRTEnv.IsValid.joint_relaxedIDLABounds
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (O U : ℝ → Ω → Set ℤ) (K : ℝ → ℝ) (q : ℝ) (s : Ω → ℝ)
    (hU : ∀ ε k, NullMeasurableSet {ω | k ∈ U ε ω} S.P)
    (hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O ε ω ⊆ U ε ω ∧
      U ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ))
    (hq : 0 < q) (hs : Measurable[S.envSigma] s) (hspos : ∀ ω, 0 < s ω)
    (hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O ε ω,
      (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
        greenFn (S.mult ε ω) (U ε ω) a a})) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) := by
  let G : ℝ → Ω → Set ℤ := fun ε ω => {a | a ∈ U ε ω ∧
    (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
      K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
    ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
      greenFn (S.mult ε ω) (U ε ω) a a}
  have hG : ∀ ε a, NullMeasurableSet {ω | a ∈ G ε ω} S.P := fun ε a =>
    hS.nullMeasurableSet_greenGoodVertices ε (K ε) q s (hS.aemeasurable_of_envSigma hs)
      (U ε) (hU ε) a
  have hGU : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, G ε ω ⊆ U ε ω ∧
      U ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro ε hε
    filter_upwards [hO ε hε] with ω hω
    exact ⟨fun _ ha => ha.1, hω.2⟩
  have hgoodG : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ G ε ω,
      (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
        greenFn (S.mult ε ω) (U ε ω) a a}) := by
    simp only [ProbTendsToOne]
    have heq : (fun ε => S.P {ω | ∀ a ∈ G ε ω,
      (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
        greenFn (S.mult ε ω) (U ε ω) a a}ᶜ) = fun _ => 0 := by
      funext ε
      have : {ω | ∀ a ∈ G ε ω,
        (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
          K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
        ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
          greenFn (S.mult ε ω) (U ε ω) a a} = Set.univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact fun a ha => ha.2
      rw [this, compl_univ, measure_empty]
    rw [heq]
    exact tendsto_const_nhds
  obtain ⟨hL, hT⟩ := h52 γ hγ hγ2 ρ hρ hρ1 Ω S hS G U K q s hGU hq hs hspos hgoodG
  have hsel : Tendsto (fun ε => S.P {ω | ¬ O ε ω ⊆ G ε ω}) (𝓝[>] 0) (𝓝 0) := by
    unfold ProbTendsToOne at hgood
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    apply measure_mono_ae
    filter_upwards [hO ε hε] with ω hω
    intro hn hg
    exact hn fun x hx => ⟨hω.1 hx, hg x hx⟩
  exact hS.joint_generalIDLABounds_of_nullMeasurable_envelope O G U K hG hU hsel hL hT

/-- Only positive mesh sizes need a null-measurable stopping domain. -/
theorem MatedCRTEnv.IsValid.joint_relaxedIDLABounds_of_pos
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (O U : ℝ → Ω → Set ℤ) (K : ℝ → ℝ) (q : ℝ) (s : Ω → ℝ)
    (hU : ∀ ε, 0 < ε → ∀ k, NullMeasurableSet {ω | k ∈ U ε ω} S.P)
    (hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O ε ω ⊆ U ε ω ∧
      U ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ))
    (hq : 0 < q) (hs : Measurable[S.envSigma] s) (hspos : ∀ ω, 0 < s ω)
    (hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O ε ω,
      (1 + s ω) * ∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (U ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : U ε ω, greenFn (S.mult ε ω) (U ε ω) b a) /
        greenFn (S.mult ε ω) (U ε ω) a a})) :
    Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaJointMeasure ε
      {p | ¬ O ε p.1 ⊆ stoppedIDLACluster (U ε p.1) p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0) := by
  classical
  let V : ℝ → Ω → Set ℤ := fun ε ω => if 0 < ε then U ε ω else ∅
  have hV : ∀ ε a, NullMeasurableSet {ω | a ∈ V ε ω} S.P := by
    intro ε a
    by_cases he : 0 < ε
    · simpa [V, he] using hU ε he a
    · simp [V, he]
  have hOV : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O ε ω ⊆ V ε ω ∧
      V ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro ε he
    simpa [V, he] using hO ε he
  have hgoodV : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O ε ω,
      (1 + s ω) * ∑' b : V ε ω, greenFn (S.mult ε ω) (V ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (V ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : V ε ω, greenFn (S.mult ε ω) (V ε ω) b a) /
        greenFn (S.mult ε ω) (V ε ω) a a}) := by
    unfold ProbTendsToOne at hgood ⊢
    apply hgood.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (he : 0 < ε)
    have hv : V ε = U ε := by funext ω; simp [V, he]
    rw [hv]
  obtain ⟨h1, h2⟩ := hS.joint_relaxedIDLABounds hγ hγ2 hρ hρ1 h52 O V K q s hV hOV hq hs hspos hgoodV
  refine ⟨h1, ?_⟩
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (he : 0 < ε)
  simp [V, he]

end MatedCRT
