import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DegreeMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EdgeMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentMeasurability

/-! # Environmental edge multiplicities and degrees of the mated-CRT map

`S.mult ε ω` is the edge count of the Brownian path `S.bm ω`. The environmental path of
`MatedCRTEnv.IsValid.exists_envSigma_measurable_bm` agrees with `S.bm` almost surely and is measurable for
`σ(h, η)`. The closed-condition argument of `MatedCRTEnv.IsValid.measurable_mult` then gives a `σ(h, η)`-measurable
version of each edge multiplicity, and the finite sum defining the degree gives one of each degree. -/

namespace MatedCRT

open Set MeasureTheory

/-- The edge count of the map built from a path `B` is measurable for the σ-algebra on `Ω`
for which `B` is measurable. -/
theorem measurable_bmEdgeCount_comp {Ω : Type} [MeasurableSpace Ω] (B : Ω → C(ℝ, ℝ × ℝ))
    (hB : Measurable B) (ε : ℝ) (j k : ℤ) :
    Measurable (fun ω => bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k) := by
  classical
  have hL : MeasurableSet {ω | bmAdjacent ε (fun t => (B ω t).1) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.fst continuous_fst).measurableSet.preimage hB
  have hR : MeasurableSet {ω | bmAdjacent ε (fun t => (B ω t).2) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.snd continuous_snd).measurableSet.preimage hB
  unfold bmEdgeCount
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    apply Measurable.ite (hL.union hR)
    · by_cases hdist : 1 < max j k - min j k
      · simp only [hdist, true_and]
        exact Measurable.ite (hL.inter hR) measurable_const measurable_const
      · simp [hdist]
    · exact measurable_const

/-- Each edge multiplicity has a `σ(h, η)`-measurable version, equal to `S.mult ε · j k` almost surely. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_mult {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (j k : ℤ) :
    ∃ M : Ω → ℕ, Measurable[S.envSigma] M ∧ ∀ᵐ ω ∂S.P, M ω = S.mult ε ω j k := by
  obtain ⟨B, hB, hBae⟩ := hS.exists_envSigma_measurable_bm
  refine ⟨fun ω => bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k,
    @measurable_bmEdgeCount_comp Ω S.envSigma B hB ε j k, ?_⟩
  filter_upwards [hBae] with ω hω
  simp only [MatedCRTEnv.mult, hω]

/-- Each degree has a `σ(h, η)`-measurable version, equal to `mdeg (S.mult ε ·) j` almost surely. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_mdeg {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (j : ℤ) :
    ∃ D : Ω → ℕ, Measurable[S.envSigma] D ∧ ∀ᵐ ω ∂S.P, D ω = mdeg (S.mult ε ω) j := by
  obtain ⟨B, hB, hBae⟩ := hS.exists_envSigma_measurable_bm
  refine ⟨fun ω => mdeg (fun a b => bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) a b) j,
    @measurable_finsum_nat Ω ℤ S.envSigma _ (fun ω k => bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k)
      (fun k => @measurable_bmEdgeCount_comp Ω S.envSigma B hB ε j k), ?_⟩
  filter_upwards [hBae] with ω hω
  simp only [MatedCRTEnv.mult, hω]

end MatedCRT
