import MatedCRT.FirstPass.Closure.AppendixA
import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section5
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.Closure.Section7
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results of the first pass (task fp-Closure-counted-results, worker z1)

`closed_<id>` restates `firstPass_<id>` for each numbered result counted PROVED-FP, with hypotheses reduced to
FIRST-PASS FROZEN Props, External Props, cited results and the other paper's harmonic-balls statements.
Closed here (23 by alias, 2 by explicit composition): 2.4, 2.5, 2.6, 2.13, 2.17, 2.19, 3.1, 3.3, 3.4, 3.6,
4.3, 4.4, 4.5, 4.7, 5.2, 5.4, 6.4, 6.5, 6.10, 7.2, 7.3, A.1-A.4.
3.5 (corrected, `closed_3_5`) and 3.7 (`closed_3_7`, via `firstPass_3_7_corrected`) are closed modulo the corrected
Lemma 3.6 input `h36` (`CorrectedHarmonicConvergenceStmt`; no provider yet, see reports/z1.md). The frozen `hfinite` is
discharged by the proved `frozenFiniteDomainDirichletRepresentation_proved`, and the per-model inputs come from the
extended SLE reference package (Closure/SLEPackage.lean); Closure/Section3.lean.
Not closed (gaps, see the report): 1.4, 1.6, 2.3, 4.1, 4.6, 4.8, 5.3, 6.1, 7.1, 8.1.
-/
