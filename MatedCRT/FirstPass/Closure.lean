import MatedCRT.FirstPass.Closure.AppendixA
import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section5
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.Closure.Section7
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results of the first pass

`closed_<id>` restates `firstPass_<id>` for each numbered result, with hypotheses reduced to
Frozen Props, External Props, cited results and the harmonic-balls statements of the HarmonicBalls package.
Closed here (23 by alias, 2 by explicit composition): 2.4, 2.5, 2.6, 2.13, 2.17, 2.19, 3.1, 3.3, 3.4, 3.6,
4.3, 4.4, 4.5, 4.7, 5.2, 5.4, 6.4, 6.5, 6.10, 7.2, 7.3, A.1-A.4.
Every closed theorem of Section 2 to 7 that uses the SLE reference package takes ONE hypothesis
`hC : CertifiedReferenceModel ν 𝒮` (FirstPass/SLERef/Certified.lean) and projects its per-model inputs. The old
`slePkg_*` helpers (Closure/SLEPackage.lean) are superseded and no longer called. Section 3 closes 3.5 and 3.7 with the
corrected Lemma 3.6 input from `firstPass_3_6_convergence_corrected` (`closed_3_6_corrected`, convergence conjunct
only); their remaining hypothesis is the frozen `hexc`. The frozen `hfinite` is discharged by
`frozenFiniteDomainDirichletRepresentation_proved`.
Not closed (gaps, see the report): 1.4, 1.6, 2.3, 4.1, 4.6, 4.8, 5.3, 6.1, 7.1, 8.1.
-/
