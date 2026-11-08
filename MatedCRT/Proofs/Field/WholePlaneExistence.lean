import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# A whole-plane GFF exists, in the Harmonic-Balls interface

Leonardo Bonanno's normalized whole-plane GFF (`LQGMetric.GFFExist.exists_normalizedWPGFF`, in the LatticeProb port)
is transferred to the Harmonic-Balls structure `HarmonicBalls.IsWholePlaneGFF`, which has one pairing for every test
function and one circle average for every radius `r > 0`:

* the pairing with a Harmonic-Balls test function `φ` is Bonanno's pairing `⟨h, φ⟩`; on other functions the
  pairing is `0`, since `IsWholePlaneGFF` constrains only the admissible observables;
* the circle averages are the joint continuous version `HarmonicBalls.normalizedGFF_exists_measurable_joint_circle_version`
  (a.s. continuous on `(0, ∞) × ℂ`, a.s. equal to the circle averages, jointly Gaussian with all pairings).

The Gaussianity, the centering and the covariances (including pairings with nonzero integral) are those of
`HarmonicBalls.normalizedGFF_allPairings_gaussian`, `HarmonicBalls.normalizedGFF_pairing_covariance_eq_project`,
`HarmonicBalls.normalizedGFF_circleIncrement_pairing_covariance_eq_project`, `LQGMetric.CircleAvg.integral_cInc`
and `HarmonicBalls.wholePlaneGFFCov_pairing_circle_symm`.

This proves only the existence of a whole-plane GFF. The existence of its γ-LQG measure (Duplantier-Sheffield 2011,
Proposition 1.1) is a separate input, so `WholePlaneLQGExistenceStep` is not proved here.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set HarmonicBalls

/-- A Harmonic-Balls test function, as an element of Bonanno's space `𝓓(ℂ)` of test functions. -/
def toTestC {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) : LQGMetric.TestC :=
  ⟨φ, hφ.1, hφ.2.1, by simp⟩

open Classical in
/-- The pairing `⟨h, φ⟩` of Bonanno's field `h` with a function `φ`: its value on a test function, and `0` otherwise. -/
noncomputable def pairingOf {Ω : Type} (h : Ω → LQGMetric.DistC) (ω : Ω) (φ : ℂ → ℝ) : ℝ :=
  if hφ : IsTestFunction Set.univ φ then h ω (toTestC hφ) else 0

/-- The index map from the admissible observables to the index set of Bonanno's joint family
(pairings with test functions, and circle averages with positive radius). -/
def admIdx : GFFObservable.Admissible → LQGMetric.TestC ⊕ (Set.Ioi (0 : ℝ) × ℂ)
  | ⟨.pairing φ, hφ⟩ => Sum.inl (toTestC (show IsTestFunction Set.univ φ from hφ))
  | ⟨.circle r z, hr⟩ => Sum.inr (⟨r, show 0 < r from hr⟩, z)

/-- **A whole-plane GFF exists** (Harmonic-Balls `IsWholePlaneGFF`, from Bonanno's normalized GFF). -/
theorem wholePlaneGFF_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P ∧ IsWholePlaneGFF P hC hcirc := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  obtain ⟨H, hmeas, hcont, hae, hgauss, hcov⟩ :=
    normalizedGFF_exists_measurable_joint_circle_version hh
  refine ⟨Ω, mΩ, P, pairingOf h, fun ω r z => H r z ω, hP, ?_⟩
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
