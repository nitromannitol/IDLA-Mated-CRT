# Harmonic-ball strict growth and the obstacle gap

Source audit, 2026-11-06. **Verdict: UNRESOLVED** for each of the two Lean propositions and for the weaker stopping proposition. None of CITED, PROVED-HERE, or FALSE is justified by the evidence below. In particular, no counterexample to an LQG assertion is claimed.

## Strict growth

The harmonic-balls paper explicitly says that it cannot show strict monotonicity and asks to prove or disprove exactly the inclusion `closure Λ_s ⊆ Λ_t` for `0 < s < t` (Problem in `../Harmonic-Balls-LQG/paper/lqg_harmonic_ball-corrected.tex:271-275`). Its Theorem 1.1 (`:152-158`) asserts increasing and Hausdorff-continuous balls, not this inclusion. Lemma 3.2 (`:643-647`) gives only inclusion of the unregularized clusters. Theorem 5.5 (`:863-869`) identifies harmonic balls with *regularized* clusters. The corrected mated-CRT paper Theorem 2.3 (`paper/idla_mated_crt-corrected.tex:508-520`) likewise gives monotonicity and the regularized characterization, not strict growth.

`ConeHarmonicBallStrictGrowthStep` (`MatedCRT/Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:109`) is an interval and quantum-cone formulation of this open issue; the cited whole-plane problem does not logically prove that the cone statement is false. The half-ball assertion `ConeHalfBallClosureInsideStep` (`MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:19`) is weaker: strict growth implies it by choosing an intermediate time (`:27-39`). The open problem does not establish that the weaker assertion is false or open in the literature, and no independent proof of it was found here. Mated-CRT Lemma 2.4 (`paper/idla_mated_crt-corrected.tex:533-543`) asserts existence and uniqueness of a stopped family; it does not explicitly assert closure containment at all earlier times.

## Obstacle gap

Theorem 2.3(c) of mated-CRT (`paper/idla_mated_crt-corrected.tex:515-520`) and Theorem 5.5 of the harmonic-balls paper (`:863-869`) identify `Λ_t` with `interior (closure C_t)`, where `C_t` is the strict noncoincidence set. They do not state `Λ_t ⊆ C_t`. The latter is the missing assertion `HarmonicBallStrictObstacleGapStep` (`MatedCRT/Proofs/Sec4/DivSandpileLowerBound/Final.lean:29-38`). Mated-CRT's proof of Proposition 4.2 (`paper/idla_mated_crt-corrected.tex:1633-1657`) infers a uniform strict gap from the regularized identity and continuity. This inference alone is invalid: for `C = B(0,1) \ {1/2}`, the continuous nonnegative function `f(z) = max(0, 1 - |z|) * |z - 1/2|²` has `{f > 0} = C`, but `interior (closure C) = B(0,1)` contains the zero `1/2`. Even locally, `f(z) = |z|²` has positive Laplacian and an interior zero, so positivity of the measure and the sign of the obstacle equation do not by themselves eliminate contact points. These are counterexamples to the stated inference, not to the full LQG obstacle problem.

The harmonic-balls paper defines the actual cluster as the noncoincidence set (`:579-598`), distinguishes it from its regularization (`:843-850`), and derives full support and regularity properties (`:133-135`, `:3522-3542`). No result found there proves their equality. A proof from the full obstacle characterization, or a counterexample satisfying *all* its hypotheses, remains needed. The strict-growth and strict-gap claims concern different inclusions; neither has been shown here to imply the other.

## Exact unresolved inputs

- `MatedCRT.ConeHalfBallClosureInsideStep : Prop`, or the stronger `MatedCRT.ConeHarmonicBallStrictGrowthStep : Prop`.
- `MatedCRT.HarmonicBallStrictObstacleGapStep : MatedCRT.SpaceFillingSLEModel → Prop`.

The two are currently internal steps, not identified published literature inputs. Their displayed definitions give the complete quantified Lean statements. A literature source, a rigorous proof using existing results, or a valid counterexample is required before either can be discharged.
