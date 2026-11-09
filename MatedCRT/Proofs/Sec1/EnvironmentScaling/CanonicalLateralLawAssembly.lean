import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proofs.Sec1.EnvironmentScaling.LateralCircleMeasurability

/-!
# Canonical lateral law: coordinate identification, whole-plane and cone laws, radial independence

Sources: env-steps.tex:128-143 (the lateral observables `ℓ(φ)`, `ℓ(r,z)`; the meaning of `IsWholePlaneGFF`) and
env-steps.tex:240-257 (radial integrability and finiteness of the lateral integrals, circles through zero, determination
by countably many radial evaluations, the Gaussian covariance determining the lateral law, and independence in the cone
predicate). Definitions: `Defs/QuantumCone.lean` (`IsQuantumCone`, `radialProcess`, `quantumConeRadialLaw`,
`lateralProcess`). Field inputs: `IsWholePlaneGFF.lateral_law_eq` (Field.lean:128) and `IsQuantumCone.lateral_law_eq`
(Field.lean:152). Measurability of the countable array: `LateralCircleMeasurability.lean`.

* `ae_circleArray_eq_normalized`, `ae_actualCircleCoords_eq_lateralArray`: coordinate identification. Almost surely, for all
  `n` at once, the countable array along circles `cc n = (r_n, z_n)` with `r_n > 0` is the actual lateral circle coordinate
  `h_{r_n}(z_n) - (2π)⁻¹ ∫_{[0,2π]} h_{|z_n + r_n e^{iθ}|}(0) dθ` (env-steps.tex:128-135).
* `ae_circleArray_integrableOn`: for circles through `0` the angular integral is almost surely a Lebesgue integral, under
  the explicit premise `RadialLogMajorant` (env-steps.tex:248-251; not derived here).
* `map_actualCircleCoords_eq_of_isWholePlaneGFF`, `map_lateralArray_eq_of_isWholePlaneGFF`,
  `map_lateralArray_eq_of_isQuantumCone`: for any countable family `c` of admissible observables (pairings and circles), the
  law of the measurable lateral array does not depend on the representing field; the actual circle coordinates have a
  canonical law too. The Gaussian covariance enters only through `lateral_law_eq`.
* `indepFun_radial_lateralArray_of_isQuantumCone`, `map_radial_lateralArray_of_isQuantumCone`: the radial process and the
  lateral array of a cone are independent (the `indep` clause, taken as given), and their joint law is the product of the
  radial law `quantumConeRadialLaw γ ν` and the canonical law of the whole-plane lateral array.

Not claimed here: continuity of `ℓ` in `(r, z)` (a continuous-path version); the derivation of `RadialLogMajorant`
(sublinear radial growth, entrance-chain domination); the Riemann-sum argument of env-steps.tex:249-250 (the countable
determination is that of `CirclePairing.radialVersion`, ConePairing.lean); the derivation of the cone's `lateral_law`
clause from the covariance. These stay explicit hypotheses or are left unformalized.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open HarmonicBalls

namespace MatedCRT.Sec1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The circle observables `h_{r_n}(z_n)` along a countable family `cc n = (r_n, z_n)` of positive radii. -/
def circleAdmissible (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1) : ℕ → GFFObservable.Admissible :=
  fun n => (⟨GFFObservable.circle (cc n).1 (cc n).2, hcc n⟩ : {o : GFFObservable // o.IsAdmissible})

/-- **Coordinate identification.** Almost surely, for all `n` at once, the countable lateral array along `cc` equals the
actual lateral circle coordinate written with the angular integral (env-steps.tex:128-135):
`ℓ(r_n, z_n) = h_{r_n}(z_n) - (2π)⁻¹ ∫_{[0,2π]} h_{|z_n + r_n e^{iθ}|}(0) dθ`. -/
theorem ae_circleArray_eq_normalized {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1) :
    ∀ᵐ ω ∂P, ∀ n, lateralArray hC hcirc (circleAdmissible cc hcc) ω n =
      hcirc ω (cc n).1 (cc n).2 - (2 * Real.pi)⁻¹ *
        ∫ θ in Icc 0 (2 * Real.pi), hcirc ω ‖(cc n).2 + ((cc n).1 : ℂ) * exp (I * (θ : ℂ))‖ 0 := by
  filter_upwards [ae_lateralArray_eq (hC := hC) hcont (circleAdmissible cc hcc)] with ω hω
  intro n
  rw [hω]
  exact lateralCircleCoord_eq_normalized hcirc (cc n).1 (cc n).2 ω

/-- **Actual circle coordinates are a.s. the countable array.** The lateral circle coordinates
`ℓ(r_n, z_n) = h_{r_n}(z_n) - Real.circleAverage (x ↦ h_{|x|}(0)) z_n r_n` form, almost surely, the countable lateral
array along `cc`, at all coordinates at once. -/
theorem ae_actualCircleCoords_eq_lateralArray {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1) :
    (fun ω n => lateralCircleCoord hcirc (cc n).1 (cc n).2 ω) =ᵐ[P]
      lateralArray hC hcirc (circleAdmissible cc hcc) := by
  filter_upwards [ae_lateralArray_eq (hC := hC) hcont (circleAdmissible cc hcc)] with ω hω
  exact hω.symm

/-- **Finite angular integrals on circles through zero.** For each `n` with `‖z_n‖ = r_n`, under the radial log majorant at
`r_n` (the explicit premise `RadialLogMajorant`, env-steps.tex:248-251), the angular integrand is almost surely integrable
on `[0, 2π]`, so the angular integral of `ae_circleArray_eq_normalized` is a genuine finite integral. -/
theorem ae_circleArray_integrableOn {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1)
    (hlog : ∀ n, ‖(cc n).2‖ = (cc n).1 → RadialLogMajorant hcirc P (cc n).1) :
    ∀ᵐ ω ∂P, ∀ n, ‖(cc n).2‖ = (cc n).1 →
      IntegrableOn (fun θ : ℝ => hcirc ω ‖(cc n).2 + ((cc n).1 : ℂ) * exp (I * (θ : ℂ))‖ 0)
        (Icc 0 (2 * Real.pi)) := by
  refine ae_all_iff.2 fun n => ?_
  by_cases h : ‖(cc n).2‖ = (cc n).1
  · filter_upwards [ae_integrableOn_lateralCircle_through_zero hcont (hcc n) h (hlog n h)] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ fun ω hn => absurd hn h

/-- **The countable lateral array has one law for two representations (explicit law identity).** Given the identity of the
laws of the lateral processes (the `lateral_law` identity, here a hypothesis), the measurable countable arrays along any
countable family `c` of admissible observables have the same law: the array is a.s. the lateral process at the coordinates
`c n`. -/
theorem map_lateralArray_eq_of_lateral_law_measurable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmp' : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ)
    (hmc' : ∀ r z, 0 < r → Measurable fun ω => hcirc' ω r z)
    (hcont' : ∀ᵐ ω ∂P', ContinuousOn (fun p : ℝ × ℂ => hcirc' ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlaw : P.map (fun ω => MatedCRT.lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => MatedCRT.lateralProcess (hC' ω) (hcirc' ω)))
    (c : ℕ → GFFObservable.Admissible) :
    P.map (lateralArray hC hcirc c) = P'.map (lateralArray hC' hcirc' c) := by
  rw [Measure.map_congr (ae_lateralArray_eq (hC := hC) hcont c),
    Measure.map_congr (ae_lateralArray_eq (hC := hC') hcont' c)]
  exact map_lateralArray_eq_of_lateral_law hmp hmc hcont hmp' hmc' hcont' hlaw c

/-- **Canonical law of the actual lateral circle coordinates of a whole-plane GFF.** Two whole-plane GFF representations
give the same law for the actual lateral circle coordinates along `cc`. The covariance of the whole-plane GFF fixes the
lateral law (`IsWholePlaneGFF.lateral_law_eq`, Field.lean:128); the coordinates are a.s. the countable array
(`ae_actualCircleCoords_eq_lateralArray`). -/
theorem map_actualCircleCoords_eq_of_isWholePlaneGFF {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {hcirc₁ : Ω₁ → ℝ → ℂ → ℝ}
    {hC₂ : Ω₂ → (ℂ → ℝ) → ℝ} {hcirc₂ : Ω₂ → ℝ → ℂ → ℝ}
    (h₁ : IsWholePlaneGFF P₁ hC₁ hcirc₁) (h₂ : IsWholePlaneGFF P₂ hC₂ hcirc₂)
    (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1) :
    P₁.map (fun ω n => lateralCircleCoord hcirc₁ (cc n).1 (cc n).2 ω) =
      P₂.map (fun ω n => lateralCircleCoord hcirc₂ (cc n).1 (cc n).2 ω) := by
  rw [Measure.map_congr (ae_actualCircleCoords_eq_lateralArray (hC := hC₁) h₁.ae_continuousOn_circle cc hcc),
    Measure.map_congr (ae_actualCircleCoords_eq_lateralArray (hC := hC₂) h₂.ae_continuousOn_circle cc hcc)]
  exact map_lateralArray_eq_of_lateral_law_measurable h₁.measurable_pairing h₁.measurable_circle
    h₁.ae_continuousOn_circle h₂.measurable_pairing h₂.measurable_circle h₂.ae_continuousOn_circle
    (MatedCRT.Sec1.IsWholePlaneGFF.lateral_law_eq h₁ h₂) (circleAdmissible cc hcc)

/-- **Canonical law of the countable lateral array of a whole-plane GFF.** Two whole-plane GFF representations give the same
law for the measurable countable array along any countable family `c` of admissible observables (pairings and circles). -/
theorem map_lateralArray_eq_of_isWholePlaneGFF {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {hcirc₁ : Ω₁ → ℝ → ℂ → ℝ}
    {hC₂ : Ω₂ → (ℂ → ℝ) → ℝ} {hcirc₂ : Ω₂ → ℝ → ℂ → ℝ}
    (h₁ : IsWholePlaneGFF P₁ hC₁ hcirc₁) (h₂ : IsWholePlaneGFF P₂ hC₂ hcirc₂)
    (c : ℕ → GFFObservable.Admissible) :
    P₁.map (lateralArray hC₁ hcirc₁ c) = P₂.map (lateralArray hC₂ hcirc₂ c) :=
  map_lateralArray_eq_of_lateral_law_measurable h₁.measurable_pairing h₁.measurable_circle
    h₁.ae_continuousOn_circle h₂.measurable_pairing h₂.measurable_circle h₂.ae_continuousOn_circle
    (MatedCRT.Sec1.IsWholePlaneGFF.lateral_law_eq h₁ h₂) c

/-- **Canonical law of the countable lateral array of a γ-quantum cone.** Two quantum cones with the same `γ` give the same
law for the countable lateral array along any countable family `c` of admissible observables
(`IsQuantumCone.lateral_law_eq`, Field.lean:152). -/
theorem map_lateralArray_eq_of_isQuantumCone {γ : ℝ} {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {hcirc₁ : Ω₁ → ℝ → ℂ → ℝ}
    {hC₂ : Ω₂ → (ℂ → ℝ) → ℝ} {hcirc₂ : Ω₂ → ℝ → ℂ → ℝ}
    (h₁ : IsQuantumCone γ P₁ hC₁ hcirc₁) (h₂ : IsQuantumCone γ P₂ hC₂ hcirc₂)
    (c : ℕ → GFFObservable.Admissible) :
    P₁.map (lateralArray hC₁ hcirc₁ c) = P₂.map (lateralArray hC₂ hcirc₂ c) :=
  map_lateralArray_eq_of_lateral_law_measurable h₁.measurable_pairing h₁.measurable_circle
    h₁.ae_continuousOn_circle h₂.measurable_pairing h₂.measurable_circle h₂.ae_continuousOn_circle
    (MatedCRT.Sec1.IsQuantumCone.lateral_law_eq h₁ h₂) c

/-- **Radial/lateral independence passes to the countable array.** The `indep` clause of `IsQuantumCone` (independence in
the cone predicate, env-steps.tex:255-256) gives the independence of the radial process and the countable lateral array:
the array is a.s. a measurable function of the lateral process (`ae_lateralArray_eq`). -/
theorem indepFun_radial_lateralArray_of_isQuantumCone {γ : ℝ} {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc) (c : ℕ → GFFObservable.Admissible) :
    IndepFun (fun ω => radialProcess (hcirc ω)) (lateralArray hC hcirc c) P := by
  have hψ : Measurable fun f : GFFObservable.Admissible → ℝ => fun n : ℕ => f (c n) :=
    Measurable.of_eval fun n => measurable_pi_apply (c n)
  have h0 : IndepFun (fun ω => radialProcess (hcirc ω))
      (fun ω n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n)) P :=
    hQ.indep.comp measurable_id hψ
  exact h0.congr EventuallyEq.rfl
    ((ae_lateralArray_eq (hC := hC) hQ.ae_continuousOn_circle c).mono fun ω hω => hω.symm)

/-- **Joint law of the radial process and the countable lateral array of a γ-quantum cone.** By independence
(`indepFun_radial_lateralArray_of_isQuantumCone`), the joint law is the product of the marginals: the radial law
`quantumConeRadialLaw γ ν` (the `radial_law` clause, with the conditioned Brownian motion `ν`), and the law of the countable
lateral array along `c`, which is the canonical law of the whole-plane lateral array (the `lateral_law` clause,
env-steps.tex:255-257). The `lateral_law` clause is used as given; it is not derived from the covariance here. With `c` a
family of circles (`circleAdmissible cc hcc`) this is the joint law of the radial process and the actual circle coordinates. -/
theorem map_radial_lateralArray_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc)
    (c : ℕ → GFFObservable.Admissible) :
    ∃ ν, IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
        (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
        P.map (fun ω => (radialProcess (hcirc ω), lateralArray hC hcirc c ω)) =
          (quantumConeRadialLaw γ ν).prod (P'.map (lateralArray hC' hcirc' c)) := by
  obtain ⟨ν, hν, hrad⟩ := hQ.radial_law
  obtain ⟨Ω', inst, P', hC', hcirc', hP', hW, hlaw⟩ := hQ.lateral_law
  refine ⟨ν, hν, Ω', inst, P', hC', hcirc', hP', hW, ?_⟩
  have hradM : Measurable fun ω => radialProcess (hcirc ω) := by
    unfold radialProcess
    exact Measurable.prodMk
      (measurable_pi_iff.2 fun t => hQ.measurable_circle (Real.exp (-(t : ℝ))) 0 (Real.exp_pos _))
      (measurable_pi_iff.2 fun s => hQ.measurable_circle (Real.exp (s : ℝ)) 0 (Real.exp_pos _))
  have hlatM : Measurable (lateralArray hC hcirc c) :=
    measurable_lateralArray hQ.measurable_pairing hQ.measurable_circle c
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hradM.aemeasurable hlatM.aemeasurable).1
    (indepFun_radial_lateralArray_of_isQuantumCone hQ c)
  rw [hjoint, hrad, map_lateralArray_eq_of_lateral_law_measurable hQ.measurable_pairing hQ.measurable_circle
    hQ.ae_continuousOn_circle hW.measurable_pairing hW.measurable_circle hW.ae_continuousOn_circle hlaw c]

end MatedCRT.Sec1
