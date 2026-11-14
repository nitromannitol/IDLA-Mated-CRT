import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfReference
import MatedCRT.FirstPass.Derived.InterpWalkLawJointConvergence
import MatedCRT.FirstPass.Derived.CoordCircleGoodSet
import MatedCRT.FirstPass.Derived.LQGApproxLawKernel
import MatedCRT.FirstPass.Derived.LQGApproxLawConvergence
import MatedCRT.FirstPass.Derived.LBMLawFieldAssembly
import MatedCRT.FirstPass.Derived.LBMMedianIdentification

/-!
# Theorem 2.11 from the continuity of the Liouville Brownian law field and the convergence on reference environments

This file assembles the field `Φ` of laws of the rescaled Liouville Brownian motion used by
`randomWalkToLBMStmt_of_reference_convergence`, with the coordinates `R = LQGMetric.pairJ ⊤` of the field as data.

* `quantumConeCoordLaw γ`: the law of the field coordinates `pairJ ⊤ h` of a valid mated-CRT environment at `γ`
  (the coordinate law of the `γ`-quantum cone). It is selected by `Classical.epsilon` among the laws that are the
  field-coordinate law of **every** valid environment at `γ`; such a law exists as soon as one valid environment
  with a measurable version of its field exists (`MatedCRTEnv.IsValid.map_pairJ_eq`), so the definition does not
  depend on an environment (`MatedCRTEnv.IsValid.map_pairJ_eq_quantumConeCoordLaw`).
* `lbmExitMedian γ = lawFieldExitMedian (quantumConeCoordLaw γ) K_γ`: the lower median of the exit time from
  `B_{1/2}` under the annealed law `q_γ(dx) K_γ(x)(0)(dp)`, where `K_γ = lbmLawFieldSelection γ coordCircleGood` is
  the Borel selection of the Liouville Brownian motion law field from the approximating kernels on the explicit good
  set of field coordinates.
* `lbmPathLawField γ x = rescaledLBMLawField K lbmExitMedian γ x`: the time scaling `t ↦ q(m_γ t)` of `K_γ(x)`
  (Berestycki–Gwynne (2020), (1.6)); it is Borel in `x` (`measurable_lbmPathLawField`).
* `MatedCRTEnv.IsValid.ae_lbmLawFieldSelection_eq`: given the continuity of the Liouville Brownian motion law field
  in the starting point (Berestycki–Gwynne (2020), Proposition 6.1 and Lemma 7.17), almost surely `K_γ` at the
  field coordinates is the law of Liouville Brownian motion at every starting point.
* `hLBM_lbmPathLawField`: the hypothesis `hLBM` of `randomWalkToLBMStmt_of_reference_convergence` for
  `R = pairJ ⊤` and `Φ = lbmPathLawField`, from that continuity.
* `randomWalkToLBMStmt_of_cone_inputs`: Theorem 2.11 from the scaling inputs, that continuity, and the uniform
  convergence in probability of the selected-cell walk laws on the reference environments (Berestycki–Gwynne
  (2020), Theorem 1.2).

Terminology: positive continuous additive functional (the LQG clock), its right-continuous inverse and the time
change of planar Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian motion*, Definition 2.17); the
`γ`-quantum cone (Duplantier–Miller–Sheffield (2014), Definition 4.10).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-! ### The field-coordinate law of the quantum cone -/

/-- **The coordinate law of the `γ`-quantum cone field.** A law `q` on the field coordinates that is the law of
`pairJ ⊤ ∘ H` for every valid mated-CRT environment `S` at `γ` and every measurable version `H` of its field,
selected by `Classical.epsilon` (an arbitrary law if no valid environment exists at `γ`). -/
noncomputable def quantumConeCoordLaw (γ : ℝ) : Measure (LQGMetric.CoordJ → ℝ) :=
  Classical.epsilon fun q : Measure (LQGMetric.CoordJ → ℝ) =>
    ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
        S.P.map (fun ω => LQGMetric.pairJ ⊤ (H ω)) = q

/-- In every valid environment at `γ`, the law of the coordinates of a measurable version of the field is the
coordinate law `quantumConeCoordLaw γ` of the `γ`-quantum cone. -/
theorem MatedCRTEnv.IsValid.map_pairJ_eq_quantumConeCoordLaw {Ω : Type} [MeasurableSpace Ω]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    S.P.map (fun ω => LQGMetric.pairJ ⊤ (H ω)) = quantumConeCoordLaw γ := by
  have hspec := Classical.epsilon_spec (p := fun q : Measure (LQGMetric.CoordJ → ℝ) =>
    ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
        S.P.map (fun ω => LQGMetric.pairJ ⊤ (H ω)) = q) ⟨S.P.map (fun ω => LQGMetric.pairJ ⊤ (H ω)), by
      intro 𝒮' Ω' _ S' hS' H' hH' hrep'
      exact hS'.map_pairJ_eq hS hH' hH hrep' hrep⟩
  exact hspec 𝒮 Ω S hS H hH hrep

/-! ### The Liouville Brownian motion law field and its normalization -/

/-- At every dyadic radius `2^{-n}` (`dyadicScale n`), the circle-average process of coordinates in the good set
`coordCircleGood` is continuous in the center. -/
theorem continuous_coordCircleAverage_dyadicScale_of_mem :
    ∀ x ∈ coordCircleGood, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n)) := by
  intro x hx n
  have h : dyadicScale n = (2 : ℝ) ^ (-(n : ℤ)) := by
    rw [dyadicScale, zpow_neg, zpow_natCast, inv_pow]
  rw [h]
  exact continuous_coordCircleAverage_of_mem hx n

/-- The Borel selection `K_γ` of the Liouville Brownian motion law field on the good set of coordinates is Borel. -/
theorem measurable_lbmLawFieldSelection_coordCircleGood (γ : ℝ) :
    Measurable (lbmLawFieldSelection γ coordCircleGood) :=
  measurable_lbmLawFieldSelection measurableSet_coordCircleGood continuous_coordCircleAverage_dyadicScale_of_mem

/-- **The median normalization `m_γ`.** The lower median of the exit time from `B_{1/2}` under the annealed law
`q_γ(dx) K_γ(x)(0)(dp)`, with `q_γ = quantumConeCoordLaw γ` and `K_γ = lbmLawFieldSelection γ coordCircleGood`. -/
noncomputable def lbmExitMedian (γ : ℝ) : ℝ :=
  lawFieldExitMedian (quantumConeCoordLaw γ) (lbmLawFieldSelection γ coordCircleGood)

/-- **The field of laws of the rescaled Liouville Brownian motion.** At the field coordinates `x` and the starting
point `z`, the law `(q ↦ [t ↦ q(m_γ t)])_* K_γ(x)(z)` (Berestycki–Gwynne (2020), (1.6)). -/
noncomputable def lbmPathLawField (γ : ℝ) :
    (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  rescaledLBMLawField (fun γ => lbmLawFieldSelection γ coordCircleGood) lbmExitMedian γ

/-- The field of laws of the rescaled Liouville Brownian motion is Borel in the field coordinates. -/
theorem measurable_lbmPathLawField : ∀ γ, Measurable (lbmPathLawField γ) :=
  measurable_rescaledLBMLawField measurable_lbmLawFieldSelection_coordCircleGood lbmExitMedian

/-- **Identification of the Borel law field.** Let `S` be a valid environment and `H` a measurable version of its
field. If almost surely the law of the Liouville Brownian motion path from `z` is defined for every `z` and depends
continuously on `z` (Berestycki–Gwynne (2020), Proposition 6.1 and Lemma 7.17), then almost surely, for every
starting point `z`, the selection `K_γ` at the coordinates `pairJ ⊤ (H ω)` takes at `z` the value of the law of
Liouville Brownian motion from `z`. -/
theorem MatedCRTEnv.IsValid.ae_lbmLawFieldSelection_eq {Ω : Type} [MeasurableSpace Ω]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hL4 : ∀ᵐ ω ∂S.P, ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
      Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z)) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ, ∃ hg : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
      lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω)) z =
        planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) hg := by
  filter_upwards [hS.ae_pairJ_mem_coordCircleGood hH hrep, hS.ae_isLQGClock_coordCircleAverage hrep, hL4]
    with ω hmem hclk hcont
  obtain ⟨hg, hc⟩ := hcont
  have hsel : lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω)) =
      ⟨fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z), hc⟩ :=
    lbmLawFieldSelection_eq fun j =>
      tendsto_approxLawKernel continuous_coordCircleAverage_dyadicScale_of_mem hmem
        (hclk (complexDenseSeq j)).1 (hclk (complexDenseSeq j)).2
  exact fun z => ⟨hg z, DFunLike.congr_fun hsel z⟩

/-- **The hypothesis `hLBM` for the rescaled Liouville Brownian law field.** If in every valid environment at
`0 < γ < 2` the law of the Liouville Brownian motion path from `z` is almost surely defined for every `z` and
continuous in `z` (`hL4`, Berestycki–Gwynne (2020), Proposition 6.1 and Lemma 7.17), then in every valid
environment, for every measurable version `H` of the field, every `z` and every bounded Lipschitz path functional
`F`, almost surely the expectation of `F` of the rescaled Liouville Brownian motion `t ↦ b(F_ω(b)⁻¹(S.m₀ t))` from
`z` is the integral of `F` against `lbmPathLawField γ (pairJ ⊤ (H ω)) z`. The normalization `S.m₀` is the median
`lbmExitMedian γ` (`MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian`, `quantumConeCoordLaw`). -/
theorem hLBM_lbmPathLawField {𝒮 : SpaceFillingSLEModel}
    (hL4 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P,
        ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
          Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, FirstPass.Derived.blPathFunctionalBCF hF q
            ∂(lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : Measure (ContinuousPath ℂ)) := by
  intro γ hγ0 hγ2 Ω _ S hS H hH hrep z F hF
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (hL4 γ hγ0 hγ2 Ω S hS)
  have hm : S.m₀ = lbmExitMedian γ := by
    rw [hS.m₀_eq_lawFieldExitMedian hH (measurable_lbmLawFieldSelection_coordCircleGood γ)
      (hΛ.mono fun ω h => h 0), hS.map_pairJ_eq_quantumConeCoordLaw hH hrep, lbmExitMedian]
  filter_upwards [hΛ, hS.isLQGClock] with ω hω hclock
  obtain ⟨hg, hK⟩ := hω z
  rw [hm]
  exact integral_rescaledLBMPath_eq_timeScaleLawField z (lbmExitMedian γ) (hclock z).2 hg hK hF

/-! ### Theorem 2.11 -/

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the continuity of the Liouville Brownian law
field and the convergence of the selected-cell walk laws on the reference environments.** Given the scaling inputs
of `randomWalkToLBMStmt_of_reference_convergence`,

* (`hL4`) in every valid environment at `0 < γ < 2`, almost surely the law of the Liouville Brownian motion path
  from `z` is defined for every `z` and continuous in `z` (Berestycki–Gwynne (2020), Proposition 6.1 and
  Lemma 7.17), and
* (`hBG`) in every valid environment on `ℝ` at `0 < γ < 2`, with measurable versions `H₀`, `η₀` of its field and
  space-filling SLE curve, the selected-cell walk laws converge to `lbmPathLawField γ (pairJ ⊤ H₀)` uniformly on
  compact sets in probability (Berestycki–Gwynne (2020), Theorem 1.2),

the embedded random walk on the mated-CRT map converges to Liouville Brownian motion in every valid environment. -/
theorem randomWalkToLBMStmt_of_cone_inputs {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hL4 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P,
        ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
          Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z))
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    RandomWalkToLBMStmt 𝒮 :=
  FirstPass.Derived.randomWalkToLBMStmt_of_reference_convergence hEnvS hN4 hν href hU
    (LQGMetric.pairJ ⊤) measurable_pairJ_top lbmPathLawField measurable_lbmPathLawField
    (hLBM_lbmPathLawField hL4)
    (fun γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep η₀ hη₀m hη₀ f =>
      FirstPass.Derived.tendsto_integral_interpWalkLaw_of_selCellLaw hS₀ measurable_pairJ_top hH₀ hη₀m hη₀
        (hBG γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep η₀ hη₀m hη₀) f)

end MatedCRT
