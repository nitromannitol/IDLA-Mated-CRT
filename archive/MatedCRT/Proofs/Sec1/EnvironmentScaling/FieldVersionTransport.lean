import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-!
# Transport of radial and lateral versions

The simultaneous positive-circle identification
transports the actual radial and lateral processes.  No joint measurability of
the supplied circle representative is used.  The spatial origin and its
possible angular preimage are null in the integrals defining the lateral part.

The imported field bridge uses Leonardo Bonanno's LatticeProb field results via
`HarmonicBalls.Proofs.Sec8.WholePlaneObservableLaw`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open HarmonicBalls

namespace MatedCRT.Sec1

/-- Positive-circle agreement determines the radial process pathwise. -/
theorem radialProcess_eq_of_positive_circles {a b : ℝ → ℂ → ℝ}
    (h : ∀ r, 0 < r → ∀ z, a r z = b r z) :
    radialProcess a = radialProcess b := by
  apply Prod.ext <;> funext t <;> exact h _ (Real.exp_pos _) 0

/-- Positive-circle and test-pairing agreement determines every lateral
observable. The spatial origin and the angular point at the origin are null. -/
theorem lateralProcess_eq_of_positive_circles
    {hC hC' : (ℂ → ℝ) → ℝ} {a b : ℝ → ℂ → ℝ}
    (hp : ∀ φ, IsTestFunction univ φ → hC φ = hC' φ)
    (hc : ∀ r, 0 < r → ∀ z, a r z = b r z) :
    lateralProcess hC a = lateralProcess hC' b := by
  funext ⟨o, ho⟩
  cases o with
  | pairing φ =>
    change hC φ - ∫ x, φ x * a ‖x‖ 0 = hC' φ - ∫ x, φ x * b ‖x‖ 0
    rw [hp φ ho]
    congr 1
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℂ)] with x hx
    rw [hc ‖x‖ (norm_pos_iff.mpr hx) 0]
  | circle r z =>
    change a r z - Real.circleAverage (fun x => a ‖x‖ 0) z r =
      b r z - Real.circleAverage (fun x => b ‖x‖ 0) z r
    rw [hc r ho z]
    congr 1
    exact Real.circleAverage_congr_codiscreteWithin
      (CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ 0 fun x hx => hc ‖x‖ (norm_pos_iff.mpr hx) 0)
      ho.ne'

/-- Simultaneous agreement transports the actual process laws and independence,
including when the supplied representative is not jointly measurable. -/
theorem radial_lateral_laws_of_ae_versions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {a b : Ω → ℝ → ℂ → ℝ}
    (h : ∀ᵐ ω ∂P, (∀ φ, IsTestFunction univ φ → hC ω φ = hC' ω φ) ∧
      (∀ r, 0 < r → ∀ z, a ω r z = b ω r z)) :
    P.map (fun ω => radialProcess (a ω)) = P.map (fun ω => radialProcess (b ω)) ∧
    P.map (fun ω => lateralProcess (hC ω) (a ω)) =
      P.map (fun ω => lateralProcess (hC' ω) (b ω)) ∧
    (IndepFun (fun ω => radialProcess (a ω)) (fun ω => lateralProcess (hC ω) (a ω)) P ↔
      IndepFun (fun ω => radialProcess (b ω)) (fun ω => lateralProcess (hC' ω) (b ω)) P) := by
  have hr : (fun ω => radialProcess (a ω)) =ᵐ[P] (fun ω => radialProcess (b ω)) :=
    h.mono fun _ hω => radialProcess_eq_of_positive_circles hω.2
  have hl : (fun ω => lateralProcess (hC ω) (a ω)) =ᵐ[P]
      (fun ω => lateralProcess (hC' ω) (b ω)) :=
    h.mono fun _ hω => lateralProcess_eq_of_positive_circles hω.1 hω.2
  exact ⟨Measure.map_congr hr, Measure.map_congr hl,
    ⟨fun hi => hi.congr hr hl, fun hi => hi.congr hr.symm hl.symm⟩⟩

/-- A cone remains a cone after a simultaneous change of its admissible
pairings and positive circles. Only coordinate measurability of the new
representative is required. -/
theorem IsQuantumCone.of_ae_positive_versions
    {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {a b : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC a)
    (hpair : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ)
    (hcircle : ∀ r z, 0 < r → Measurable fun ω => b ω r z)
    (h : ∀ᵐ ω ∂P, (∀ φ, IsTestFunction univ φ → hC ω φ = hC' ω φ) ∧
      (∀ r, 0 < r → ∀ z, a ω r z = b ω r z)) :
    IsQuantumCone γ P hC' b := by
  obtain ⟨hr, hl, hi⟩ := radial_lateral_laws_of_ae_versions h
  refine ⟨hpair, hcircle, ?_, ?_, hi.mp hcone.indep, ?_⟩
  · filter_upwards [hcone.ae_continuousOn_circle, h] with ω hcont hω
    apply hcont.congr
    intro p hp
    exact (hω.2 p.1 hp.1 p.2).symm
  · obtain ⟨ν, hν, hνlaw⟩ := hcone.radial_law
    exact ⟨ν, hν, hr.symm.trans hνlaw⟩
  · obtain ⟨Ξ, mΞ, Q, gC, g, hQ, hG, hGlaw⟩ := hcone.lateral_law
    exact ⟨Ξ, mΞ, Q, gC, g, hQ, hG, hl.symm.trans hGlaw⟩

end MatedCRT.Sec1
