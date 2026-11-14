import MatedCRT.FirstPass.Derived.BLPathFunctionalDUnif
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly

/-!
# The quenched walk integral of a path functional as an integral against the quenched path law

For the quenched random walk on the mated-CRT map started at the vertex `k`, the statement of
Berestycki–Gwynne (2020), Thm. 1.2, integrates a bounded Lipschitz path functional `F` of the interpolated embedded
walk `interpolatedWalk ε η (m^ε)` against the walk law `srwLaw`.  This file identifies that integral with the integral
of the bounded continuous function `blPathFunctionalBCF` (a function of the continuous path) against the quenched
path law `walkPathLaw` (the image of `srwLaw` under `interpPathCM`), which is the form needed for the
Lévy–Prokhorov comparison with the interpolated law `interpWalkLaw`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The statement's integral is an integral against the quenched path law.** If the vertex positions `v ω` are
`vertexPoint ε η`, then
`∫ F (interpolatedWalk ε η (m^ε) x) d srwLaw(k) = ∫ blPathFunctionalBCF d walkPathLaw(k)(ω)`. -/
theorem integral_interpolatedWalk_eq_integral_walkPathLaw {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (η : ℝ → ℂ)
    (v : Ω → ℤ → ℂ) (hv : v ω = vertexPoint ε η) (k : ℤ) :
    ∫ x, F (interpolatedWalk ε η (S.mε ε) x) ∂srwLaw (S.mult ε ω) k =
      ∫ q, blPathFunctionalBCF hF q ∂(walkPathLaw S v (S.mε_nonneg ε) ε k ω : Measure (ContinuousPath ℂ)) := by
  have hmeas := measurable_interpPathCM (v ω) (S.mε_nonneg ε)
  have hlaw : (walkPathLaw S v (S.mε_nonneg ε) ε k ω : Measure (ContinuousPath ℂ)) =
      Measure.map (interpPathCM (v ω) (S.mε_nonneg ε)) (srwLaw (S.mult ε ω) k) := rfl
  rw [hlaw, integral_map hmeas.aemeasurable (blPathFunctionalBCF hF).continuous.aestronglyMeasurable]
  have h2 : interpPathCM (v ω) (S.mε_nonneg ε) = interpPathCM (vertexPoint ε η) (S.mε_nonneg ε) := by
    rw [hv]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  rw [h2]
  rfl

end MatedCRT.FirstPass.Derived
