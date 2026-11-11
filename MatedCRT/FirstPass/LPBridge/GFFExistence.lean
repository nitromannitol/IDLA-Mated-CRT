import MatedCRT.Proofs.Field.WholePlaneExistence

/-!
# Existence of a Harmonic-Balls whole-plane Gaussian free field

The field conjuncts of the mated-CRT environment that concern only the whole-plane Gaussian free field `h^ℂ`
(its pairings `hC` with test functions and its circle averages `hcirc` of positive radius) are realised by a witness
on a probability space. The witness is the proved `MatedCRT.Field.wholePlaneGFF_exists`, which transfers the
normalized whole-plane GFF of Bonanno's `LatticeProb` port (`LQGMetric.GFFExist.exists_normalizedWPGFF`) to the
Harmonic-Balls structure `HarmonicBalls.IsWholePlaneGFF`: pairings jointly Gaussian with the covariance kernel
`wholePlaneGFFCov`, centred, with `h^ℂ_1(0) = 0` and a.s. continuous circle averages in `(r, z)`
(Duplantier–Sheffield 2011, Section 3.1, eq. (3.2)).
-/

namespace MatedCRT.GFFExistence

open MeasureTheory

/-- **Existence of the whole-plane Gaussian free field** in the Harmonic-Balls interface: there are a probability
space `(Ω, P)`, pairings `hC` with test functions and circle averages `hcirc` of positive radius which form a
whole-plane GFF normalized so that `h^ℂ_1(0) = 0` (`HarmonicBalls.IsWholePlaneGFF`). -/
theorem exists_harmonicBalls_isWholePlaneGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P ∧ HarmonicBalls.IsWholePlaneGFF P hC hcirc :=
  MatedCRT.Field.wholePlaneGFF_exists

#print axioms exists_harmonicBalls_isWholePlaneGFF

end MatedCRT.GFFExistence
