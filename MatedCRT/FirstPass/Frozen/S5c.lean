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
superharmonic functions; Weyl-type regularity of distributional superharmonic functions). Locator: Harvey–Lawson,
*The equivalence of viscosity and distributional subsolutions for convex subequations—a strong Bellman principle*,
arXiv:1301.4914v1, Theorem 9.3(B) with (9.2), applied to `-w` (a distributional subsolution is subharmonic in the
sub-mean-value sense); locator from notes/fp-gaps/CHATGPT-frozen-locators.md:44 (table row `FPSuperharmonicOfLaplacianLE`).
Used by: firstPass_5_3 (MatedCRT/FirstPass/S5c/Superharmonic.lean). -/
def FPSuperharmonicOfLaplacianLE : Prop :=
  ∀ (U : Set ℂ) (w : ℂ → ℝ), IsOpen U → ContinuousOn w U → LaplacianLE w 0 U → IsSuperharmonicOn U w

end MatedCRT
