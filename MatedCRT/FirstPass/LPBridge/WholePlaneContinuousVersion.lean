import MatedCRT.FirstPass.LPBridge.GFFInterface
import MatedCRT.FirstPass.LPBridge.WholePlaneExistenceNat

/-!
# A whole-plane GFF whose circle averages are continuous at every sample

`HarmonicBalls.IsWholePlaneGFF` asks that the circle average process `(r, z) ↦ h^ℂ_r(z)` be continuous on
`(0, ∞) × ℂ` for almost every sample. Setting the circle averages to `0` on a measurable null set that contains the
exceptional samples gives another whole-plane GFF, with the same pairings and almost surely the same circle averages,
whose circle averages are continuous on `(0, ∞) × ℂ` at *every* sample. Its circle averages are then jointly
measurable in `(r, z, ω)`, since a process that is continuous in `(r, z)` and measurable in `ω` for each `(r, z)` is
jointly measurable (`measurable_uncurry_of_continuous_of_measurable`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Set HarmonicBalls

/-- **Everywhere continuous version of a whole-plane GFF.** If `(hC, hcirc)` is a whole-plane GFF on `(Ω, P)`, there
are circle averages `hcirc'`, equal to `hcirc` almost surely at each fixed `(r, z)`, such that `(hC, hcirc')` is a
whole-plane GFF, `(r, z) ↦ hcirc' ω r z` is continuous on `(0, ∞) × ℂ` for every `ω`, and `hcirc'` is jointly
measurable in `(r, z, ω)` on `(0, ∞) × ℂ`. -/
theorem wholePlaneGFF_exists_continuous_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hwp : IsWholePlaneGFF P hC hcirc) :
    ∃ hcirc' : Ω → ℝ → ℂ → ℝ,
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => hcirc' ω p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      (∀ r z, ∀ᵐ ω ∂P, hcirc' ω r z = hcirc ω r z) ∧
      IsWholePlaneGFF P hC hcirc' ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × Ω => hcirc' q.2 q.1.1 q.1.2) := by
  classical
  -- a measurable null set containing the exceptional samples
  have hbad : P {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)} = 0 :=
    ae_iff.1 hwp.ae_continuousOn_circle
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null hbad
  have hN : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hNnull
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z => if ω ∈ N then 0 else hcirc ω r z
  have hae : ∀ r z, ∀ᵐ ω ∂P, hcirc' ω r z = hcirc ω r z := fun r z =>
    hN.mono fun ω hω => by simp [hcirc', hω]
  have hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => hcirc' ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [hcirc', hω] using continuousOn_const
    · have hω' : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
        by_contra hnot
        exact hω (hNsub hnot)
      simpa [hcirc', hω] using hω'
  have hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc' ω r z := fun r z hr =>
    Measurable.ite hNmeas measurable_const (hwp.measurable_circle r z hr)
  have hev : ∀ o : GFFObservable.Admissible,
      (fun ω => o.1.eval (hC ω) (hcirc' ω)) =ᵐ[P] fun ω => o.1.eval (hC ω) (hcirc ω) := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact Filter.EventuallyEq.refl _ _
    | circle r z => exact hae r z
  refine ⟨hcirc', hcont, hae, ?_, ?_⟩
  · refine
      { measurable_pairing := hwp.measurable_pairing
        measurable_circle := hmeas
        isGaussianProcess := hwp.isGaussianProcess.congr fun o => (hev o).symm
        integral_eq_zero := ?_
        covariance_eq := ?_
        ae_continuousOn_circle := Filter.Eventually.of_forall hcont }
    · intro o ho
      rw [integral_congr_ae (hev ⟨o, ho⟩)]
      exact hwp.integral_eq_zero o ho
    · intro o o' ho ho'
      rw [MatedCRT.GFFInterface.cov_congr_ae (hev ⟨o, ho⟩) (hev ⟨o', ho'⟩)]
      exact hwp.covariance_eq o o' ho ho'
  · -- joint measurability
    have hcs : ∀ ω, Continuous fun i : Ioi (0 : ℝ) × ℂ => hcirc' ω i.1 i.2 := by
      intro ω
      have h1 := (hcont ω).comp_continuous (f := fun i : Ioi (0 : ℝ) × ℂ => ((i.1 : ℝ), i.2))
        (by fun_prop) (fun i => ⟨i.1.2, mem_univ _⟩)
      exact h1
    exact measurable_uncurry_of_continuous_of_measurable (u := fun (i : Ioi (0 : ℝ) × ℂ) ω =>
      hcirc' ω i.1 i.2) hcs fun i => hmeas i.1 i.2 i.1.2

/-- **A whole-plane GFF on `ℕ → ℝ` with everywhere continuous circle averages.** The sample space `ℕ → ℝ` is Polish,
the circle averages `(r, z) ↦ hcirc ω r z` are continuous on `(0, ∞) × ℂ` for every `ω`, and `hcirc` is jointly
measurable in `(r, z, ω)` on `(0, ∞) × ℂ`. -/
theorem wholePlaneGFF_exists_nat_continuous :
    ∃ (P : Measure (ℕ → ℝ)) (hC : (ℕ → ℝ) → (ℂ → ℝ) → ℝ) (hcirc : (ℕ → ℝ) → ℝ → ℂ → ℝ),
      IsProbabilityMeasure P ∧ IsWholePlaneGFF P hC hcirc ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × (ℕ → ℝ) => hcirc q.2 q.1.1 q.1.2) := by
  obtain ⟨P, hC, hcirc, hP, hwp⟩ := wholePlaneGFF_exists_nat
  obtain ⟨hcirc', hcont, -, hwp', hmeas⟩ := wholePlaneGFF_exists_continuous_version hwp
  exact ⟨P, hC, hcirc', hP, hwp', hcont, hmeas⟩

end MatedCRT.Field
