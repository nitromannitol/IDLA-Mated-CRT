import MatedCRT.FirstPass.Derived.RegClockUniformIntegrable
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.CoreRigidityInputsNoContourTriple
import MatedCRT.FirstPass.Closure.AppendixBRewire

/-!
# The occupation identity of the Liouville clock, unconditionally

The Revuz measure of the Liouville clock of a planar Brownian motion killed on exiting a disc `D = B_r(z)` is the
`γ`-LQG measure weighted by the Green function of `D` (Garban-Rhodes-Vargas 2016, Thm 2.7(1); Berestycki 2015,
§§2-3). In the Lean form used by the counted theorems, for the field `h^ℂ - γ log|·|` with `h^ℂ` a whole-plane GFF,
the occupation measure of the limit clock along a dyadic subsequence agrees almost surely with the Green-weighted
GMC measure `gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r` on every countable family of measurable subsets of `D`.

`ae_mem_occupationAgreementEvent_of_killedOccupation` reduces this identity to three inputs, all of which are
theorems:
* the occupation identity of the killed planar Brownian motion (`killedBrownianOccupationOnBall`);
* uniform integrability of the regularized clock integrals along the dyadic scales
  (`uniformIntegrable_setLIntegral_regClockMeasure_dyadic`);
* finiteness of the Green-weighted `γ`-LQG mass of a disc whose pole is the logarithmic singularity
  (`ae_gmcGreenMeasure_ball_lt_top_pole_zero`).

Together with the field-level law identity on the unit disk (`coneWholePlaneFieldLawStep_holds`), this proves the
occupation identity of the median-rescaled Liouville Brownian motion on the `γ`-quantum cone
(`FrozenLBMGreenOccupationRescaled`) for every model, with no hypothesis.

## Main statements

* `MatedCRT.KilledOccupation.coneUnitDiskGFFLaw_holds`: eq:gff in circle-average form.
* `MatedCRT.KilledOccupation.frozenLBMGreenOccupationRescaled_holds`: the occupation identity of Appendix B.
* `MatedCRT.KilledOccupation.ae_mem_occupationAgreementEvent_holds`: the Revuz identity of the Liouville clock of
  `h^ℂ - γ log|·|`, exactly the binder `hGFF` of the counted forms.
* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz`:
  the counted forms of Theorems 1.4 and 1.6 with `hGFF` supplied. Same conclusions.
-/

open MeasureTheory ProbabilityTheory
open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.KilledOccupation

/-- **eq:gff in circle-average form.** For every valid environment, the circle averages of the `γ`-quantum cone on
the unit disk have the law of those of `h^ℂ - γ log|·|` for a whole-plane GFF `h^ℂ`: the field-level law identity
`coneWholePlaneFieldLawStep_holds` read through `coneUnitDiskGFFLaw_of_fieldLaw`. -/
theorem coneUnitDiskGFFLaw_holds : ConeUnitDiskGFFLaw :=
  coneUnitDiskGFFLaw_of_fieldLaw ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds

/-- **Occupation identity of the median-rescaled Liouville Brownian motion on the `γ`-quantum cone** (Appendix B of
the paper), for every model, with no hypothesis. -/
theorem frozenLBMGreenOccupationRescaled_holds (𝒮 : SpaceFillingSLEModel) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw_derived 𝒮 coneUnitDiskGFFLaw_holds

/-- **Revuz identity of the Liouville clock of `h^ℂ - γ log|·|`** (Garban-Rhodes-Vargas 2016, Thm 2.7(1)). For
`0 < γ < 2`, a disc `D = B_r(z) ⊆ B_ρ(0)`, `y ∈ D`, a whole-plane GFF `h^ℂ`, and dyadic scales `ε_k = 2^{-n k}` below
`1 - ρ` along which the annealed clock gaps are summable, almost surely the occupation measure of the limit clock of a
planar Brownian motion from `y` killed on exiting `D` agrees with the Green-weighted `γ`-LQG measure on every
countable family of measurable subsets of `D`. -/
theorem ae_mem_occupationAgreementEvent_holds :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → HarmonicBalls.dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (HarmonicBalls.dyadicScale (n k))
            (HarmonicBalls.dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => HarmonicBalls.dyadicScale (n k)) z r
              (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C :=
  ae_mem_occupationAgreementEvent_of_killedOccupation (fun z r _ => killedBrownianOccupationOnBall z r)
    (fun _ hγ hγ2 _ _ _ _ _ _ _ hball _ _ _ _ _ _ hP hwp _ hn hn0 _ _ hg hg0 hgK hgs =>
      uniformIntegrable_setLIntegral_regClockMeasure_dyadic (hP := hP) hwp hγ hγ2 hball hn hn0 hg hg0 hgK hgs)
    (fun _ hγ hγ2 ρ _ hρ1 _ _ _ _ h0 _ _ _ _ _ _ hG =>
      ae_gmcGreenMeasure_ball_lt_top_pole_zero hG hγ hγ2 (by linarith : ρ < (1 + ρ) / 2)
        (by linarith : (1 + ρ) / 2 < 1) h0)

end MatedCRT.KilledOccupation

namespace MatedCRT

section CountedRigidityInputsNoContourTripleRevuz

/-- **Theorem 1.4** in the counted form
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM`,
with the Revuz identity of the Liouville clock (`hGFF`) supplied by
`KilledOccupation.ae_mem_occupationAgreementEvent_holds`. Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hCP : LatticeProb.CorrelatedBM.CauchyPointPolarInput)
    (hGHM : GHMConeDimInput)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM ν
    h1 h2 hN4 h10 h11 hCP hGHM KilledOccupation.ae_mem_occupationAgreementEvent_holds hscale

/-- **Theorem 1.6** in the counted form
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM`,
with the Revuz identity of the Liouville clock (`hGFF`) supplied by
`KilledOccupation.ae_mem_occupationAgreementEvent_holds`. Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hCP : LatticeProb.CorrelatedBM.CauchyPointPolarInput)
    (hGHM : GHMConeDimInput)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM ν
    h1 h2 hN4 h10 h11 hCP hGHM KilledOccupation.ae_mem_occupationAgreementEvent_holds hscale

end CountedRigidityInputsNoContourTripleRevuz

end MatedCRT
