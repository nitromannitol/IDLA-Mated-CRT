import MatedCRT.FirstPass.Derived.ConeReferenceLQG
import MatedCRT.FirstPass.Derived.ConeBMConditionedExists
import MatedCRT.FirstPass.Frozen.S2i
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-!
# Existence of a standard Borel model of the γ-quantum cone

`ConeReferenceExistsStep` (`FirstPass/Frozen/S2i.lean`): for `0 < γ < 2` there is a standard Borel probability
space carrying a `γ`-quantum cone together with its γ-LQG measure (`IsConeField`).  The model is the product of
the canonical sample space `ℕ → ℝ` of a whole-plane GFF with continuous circle averages and the space
`C(ℝ≥0, ℝ)` of continuous paths carrying the law `ν` of the Brownian motion conditioned to stay positive; the
field is the whole-plane GFF `h^ℂ - γ log |·|` on the unit disk, with its radial part outside the disk replaced
by the path.
-/

open MeasureTheory MarkovProcess HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **Existence of a standard Borel model of the `γ`-quantum cone with its LQG measure**
(`ConeReferenceExistsStep`) is a theorem. -/
theorem coneReferenceExistsStep_holds : ConeReferenceExistsStep := by
  intro γ hγ hγ2
  obtain ⟨P₁, hC₁, c₁, hP₁, hh, hcont, hmeas⟩ := MatedCRT.Field.wholePlaneGFF_exists_nat_continuous
  have hlt : γ < lqgQ γ := gamma_lt_lqgQ hγ hγ2
  obtain ⟨ν, hν⟩ := MatedCRT.ConeBMConditioned.exists_isBMConditionedPositive (sub_pos.2 hlt)
  have hν1 : IsProbabilityMeasure ν := hν.1
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_derived P₁ γ γ hC₁ c₁ hh hγ hγ2 hlt
  have hsb : StandardBorelSpace (ContinuousPath ℝ) := ContinuousPath.standardBorelSpace_borel
  refine ⟨(ℕ → ℝ) × ContinuousPath ℝ, inferInstance, inferInstance, P₁.prod ν,
    fun p => coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2, fun p => coneRefCircle γ (c₁ p.1) p.2,
    fun p => coneRefMeasure γ (c₁ p.1) p.2 (μ₀ p.1), ?_⟩
  unfold IsConeField
  exact ⟨inferInstance, isQuantumCone_coneRef hh γ hcont hmeas hν,
    isLQGMeasure_coneRef γ hcont hμ₀⟩

end MatedCRT.FirstPass.Derived
