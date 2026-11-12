import MatedCRT.Steps.Sec2.VolumeGrowthHalf
import MatedCRT.Proofs.Field.WholePlaneCircleBridge
import LatticeProb.LQG.GMCDyadicLimit
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# The coupling of the quantum cone with a whole-plane GFF from a pathwise realization

`ConeWholePlaneCouplingStep` (`Steps/Sec2/VolumeGrowthHalf.lean:135`; IDLA eq. (2.4), DMS14 Definition 4.10) asks,
for the circle average embedding `h` of the `γ`-quantum cone, for the circle average process `H` of a whole-plane GFF
`h̃` in Leonardo Bonanno's interface (`LQGDimension.IsGFFCircleAverage`) on the same sample space, together with its
`γ`-LQG measure (`MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf`), such that a.s. the circle averages of `h` in `B_1` are those
of `h̃ - γ log |·|`.

Only the field is genuinely needed: given on the same sample space a whole-plane GFF `(h̃C, h̃circ)` normalized by
`h̃_1(0) = 0` (`IsWholePlaneGFF`) whose shifted circle averages agree a.s. with those of `h` on every circle `∂B_r(z)`
with `cl B_r(z) ⊆ B_1`, the LQG measure of `h̃` exists (Duplantier-Sheffield 2011 Proposition 1.1, proved in
Lattice-Probability as `LatticeProb.Gauss.IsWholePlaneGFF.exists_isLQGMeasure`, read through the definitional bridges
`LPBridge.isWholePlaneGFF_iff` and `LPBridge.isLQGMeasure_iff`), and an a.s. continuous version of its
circle averages carries Bonanno's interface and the same LQG measure
(`MatedCRT.Field.IsWholePlaneGFF.exists_bonanno_gmc_version`).

## Main results

* `coneWholePlaneCouplingStep_of_realization`: `ConeWholePlaneCouplingStep` from the pathwise realization of the cone
  on `B_1` as a whole-plane GFF minus `γ log |·|`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **The coupling of the quantum cone with a whole-plane GFF, from a pathwise realization of the field.** If for
every circle average embedding `(hC, hcirc)` of the `γ`-quantum cone there is, on the same sample space, a whole-plane
GFF `(hC', hcirc')` normalized by `h̃_1(0) = 0` such that a.s. `h_r(z) = h̃_r(z) - γ · (average of log |·| over
∂B_r(z))` for every circle with `cl B_r(z) ⊆ B_1`, then `ConeWholePlaneCouplingStep` holds: the LQG measure of the
whole-plane GFF exists and Bonanno's circle average version carries it. -/
theorem coneWholePlaneCouplingStep_of_realization
    (hreal : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∃ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' ∧
        ∀ᵐ ω ∂P, ∀ (r : ℝ) (z : ℂ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 →
          hcirc ω r z = fieldCircleAverage γ (hcirc' ω) r z) :
    MatedCRT.ConeWholePlaneCouplingStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨hC', hcirc', hG, hae⟩ := hreal γ hγ hγ2 Ω P hC hcirc μ hcone
  obtain ⟨μ', hμ'⟩ := ((LPBridge.isWholePlaneGFF_iff P hC' hcirc').1 hG).exists_isLQGMeasure hγ hγ2
  obtain ⟨H, hH, hA, hHae⟩ := MatedCRT.Field.IsWholePlaneGFF.exists_bonanno_gmc_version hG
    ((LPBridge.isLQGMeasure_iff P γ hcirc' μ').2 hμ')
  refine ⟨H, μ', hH, hA, ?_⟩
  filter_upwards [hae, hHae] with ω h1 h2 r z hr hsub
  have hfun : (fun s w => H s w ω) = hcirc' ω := by
    funext s w
    exact h2 s w
  rw [h1 r z hr hsub, hfun]

end MatedCRT.FirstPass.Derived
