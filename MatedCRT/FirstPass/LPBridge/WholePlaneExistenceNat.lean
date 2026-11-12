import MatedCRT.Proofs.Field.WholePlaneExistence
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFFStd

/-!
# A whole-plane GFF on a standard Borel space, in the Harmonic-Balls interface

`wholePlaneGFF_exists_nat` is `wholePlaneGFF_exists` with the sample space made explicit: the pairings `hC` and circle
averages `hcirc` of the whole-plane GFF normalized so that `h^ℂ_1(0) = 0` are defined on the Polish space `ℕ → ℝ`
with its product σ-algebra (the sample space of the white-noise construction in `LatticeProb`), so on a standard Borel
space. The proof is that of `wholePlaneGFF_exists`, starting from `LQGMetric.GFFExist.exists_normalizedWPGFF_nat`.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set HarmonicBalls

/-- **A whole-plane GFF exists on `ℕ → ℝ`** (Harmonic-Balls `IsWholePlaneGFF`). -/
theorem wholePlaneGFF_exists_nat :
    ∃ (P : Measure (ℕ → ℝ)) (hC : (ℕ → ℝ) → (ℂ → ℝ) → ℝ)
      (hcirc : (ℕ → ℝ) → ℝ → ℂ → ℝ), IsProbabilityMeasure P ∧ IsWholePlaneGFF P hC hcirc := by
  obtain ⟨P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF_nat
  obtain ⟨H, hmeas, hcont, hae, hgauss, hcov⟩ :=
    normalizedGFF_exists_measurable_joint_circle_version hh
  refine ⟨P, pairingOf h, fun ω r z => H r z ω, hP, ?_⟩
  refine
    { measurable_pairing := ?_
      measurable_circle := ?_
      isGaussianProcess := ?_
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := hcont }
  · intro φ hφ
    simp only [pairingOf, hφ, ↓reduceDIte]
    exact (LQGMetric.measurable_evalDist (toTestC hφ)).comp hh.1.measurable
  · intro r z _
    exact hmeas r z
  · refine (hgauss.comp_right admIdx).congr fun o => Eventually.of_forall fun ω => ?_
    obtain ⟨o, ho⟩ := o
    cases o with
    | pairing φ =>
      have hφ : IsTestFunction Set.univ φ := ho
      simp only [GFFObservable.eval, pairingOf, hφ, ↓reduceDIte]
      rfl
    | circle r z => rfl
  · intro o ho
    cases o with
    | pairing φ =>
      have hφ : IsTestFunction Set.univ φ := ho
      simp only [GFFObservable.eval, pairingOf, hφ, ↓reduceDIte]
      exact (normalizedGFF_allPairings_gaussian hh).2 (toTestC hφ)
    | circle r z =>
      have hr : 0 < r := ho
      simp only [GFFObservable.eval]
      rw [integral_congr_ae (hae r hr z)]
      exact LQGMetric.CircleAvg.integral_cInc hh.1 hr one_pos z 0
  · intro o o' ho ho'
    cases o with
    | pairing ρ =>
      have hρ : IsTestFunction Set.univ ρ := ho
      cases o' with
      | pairing φ =>
        have hφ : IsTestFunction Set.univ φ := ho'
        simp only [GFFObservable.eval, pairingOf, hρ, hφ, ↓reduceDIte]
        exact normalizedGFF_pairing_covariance_eq_project hh (toTestC hρ) (toTestC hφ)
      | circle s w =>
        have hs : 0 < s := ho'
        simp only [GFFObservable.eval, pairingOf, hρ, ↓reduceDIte]
        rw [LQGMetric.CircleAvg.covariance_congr_ae EventuallyEq.rfl (hae s hs w), covariance_comm,
          normalizedGFF_circleIncrement_pairing_covariance_eq_project hh (toTestC hρ) hs w]
        exact (wholePlaneGFFCov_pairing_circle_symm (toTestC hρ) w hs).symm
    | circle r z =>
      have hr : 0 < r := ho
      cases o' with
      | pairing φ =>
        have hφ : IsTestFunction Set.univ φ := ho'
        simp only [GFFObservable.eval, pairingOf, hφ, ↓reduceDIte]
        rw [LQGMetric.CircleAvg.covariance_congr_ae (hae r hr z) EventuallyEq.rfl,
          normalizedGFF_circleIncrement_pairing_covariance_eq_project hh (toTestC hφ) hr z]
        rfl
      | circle s w =>
        have hs : 0 < s := ho'
        exact hcov r s hr hs z w

end MatedCRT.Field
