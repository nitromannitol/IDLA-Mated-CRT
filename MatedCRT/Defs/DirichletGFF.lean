import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Green

/-!
# Dirichlet Gaussian free field observables

The covariance uses the Duplantier--Sheffield normalization of the planar
Dirichlet Green function as in Berestycki, *Diffusion in planar Liouville
quantum gravity*, arXiv:1301.3356, Section 1.2, p. 949. The Green function
in `HarmonicBalls` is normalized by `-ΔG = δ`, so the field covariance is
`2πG`. This description applies where the domain admits the indicated Green
kernel; it does not assert existence for an arbitrary open set.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open HarmonicBalls

/-- Test-function pairings supported in `D` and circle averages whose closed
circle disk lies in `D`. -/
def IsDirichletGFFObservable (D : Set ℂ) : GFFObservable → Prop
  | .pairing φ => IsTestFunction D φ
  | .circle r z => 0 < r ∧ Metric.closedBall z r ⊆ D

/-- The test and circle-average observables used for a Dirichlet GFF. -/
def DirichletGFFObservable (D : Set ℂ) :=
  {o : GFFObservable // IsDirichletGFFObservable D o}

/-- Covariance of two field observables in the Duplantier--Sheffield
normalization, obtained by smearing `2π` times the Green function. -/
noncomputable def dirichletGFFCovariance (D : Set ℂ) (o o' : GFFObservable) : ℝ :=
  o.smear fun x => o'.smear fun y => (2 * Real.pi) * greenFunction D x y

/-- A zero-boundary Gaussian free field with jointly specified test-function
pairings and circle averages. The circle-average continuity is the standard
continuous modification on the set of circles contained in `D`. -/
structure IsDirichletGFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop where
  /-- All admissible observables form a Gaussian process. -/
  gaussian : IsGaussianProcess
    (fun o : DirichletGFFObservable D => fun ω => o.1.eval (h ω) (hcirc ω)) P
  /-- Each admissible observable is centered. -/
  centered : ∀ o, IsDirichletGFFObservable D o →
    ∫ ω, o.eval (h ω) (hcirc ω) ∂P = 0
  /-- The covariance is the Dirichlet Green kernel smeared against the observables. -/
  covariance : ∀ o o', IsDirichletGFFObservable D o → IsDirichletGFFObservable D o' →
    cov[fun ω => o.eval (h ω) (hcirc ω),
      fun ω => o'.eval (h ω) (hcirc ω); P] = dirichletGFFCovariance D o o'
  /-- The circle averages have the standard continuous modification. -/
  continuous_circle : ∀ᵐ ω ∂P,
    ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}

end MatedCRT
