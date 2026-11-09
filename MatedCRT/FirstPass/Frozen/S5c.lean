import HarmonicBalls.Steps.SecA.Basic

/-!
# FIRST PASS frozen inputs for Lemma 5.3 (G-5-3 Section 1)

EXTERNAL classical potential theory only; no statement about this paper's clusters, odometers or harmonic balls.
-/

namespace MatedCRT

open _root_.HarmonicBalls

/-- FIRST-PASS FROZEN. Classical potential theory: a continuous function `w` on an open set `U` with nonpositive
distributional Laplacian (`LaplacianLE w 0 U`) is superharmonic in the mean-value sense (`IsSuperharmonicOn U w`):
its circle averages on closed disks inside `U` do not exceed its value at the centre (Armitage-Gardiner, Ch. 3,
superharmonic functions; Weyl-type regularity of distributional superharmonic functions). Standard; locator pending.
Used by: firstPass_5_3 (MatedCRT/FirstPass/S5c/Superharmonic.lean). -/
def FPSuperharmonicOfLaplacianLE : Prop :=
  ∀ (U : Set ℂ) (w : ℂ → ℝ), IsOpen U → ContinuousOn w U → LaplacianLE w 0 U → IsSuperharmonicOn U w

end MatedCRT
