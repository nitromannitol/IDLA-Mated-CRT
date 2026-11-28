import MatedCRT.Assembly.Reference
import MatedCRT.Assembly.ProvedSteps
import MatedCRT.FirstPass.Closure.Clean51And54
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section7
import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Corrected

/-!
# Lemmas 5.4, 7.2 and 7.4 at the canonical model

The wrappers of `MatedCRT/Assembly/CanonicalResults.lean` for the three numbered results whose counted forms were
not yet stated at the canonical space-filling SLE model `ProbeMi.canonicalSLEModel ν`:

* `lLowerBound_canonical`: Lemma 5.4 from `CanonicalHypotheses ν`. The counted form `closed_5_4_clean` takes the
  certified reference model, which holds at the canonical model (`certifiedReferenceModel_canonical`), and the canonical
  form of Berestycki-Gwynne, Lemma 5.6, which holds for every model (`frozenBG20GreenCrudeCanonical_holds`).
* `massBoundOdometerAboveScale_canonical`: Lemma 7.2 (corrected form, above the scale) from `CanonicalHypotheses ν`:
  `closed_7_2` takes only the certified reference model.
* `crudeUpperBound_canonical`: Lemma 7.4 with no hypothesis. It follows from the corrected Lemma 4.4
  (`closed_4_4`) and the degree bound (`degreeBoundInput_holds`, from the tail of Lemma 2.5 of Gwynne-Miller-Sheffield,
  arXiv:1705.11161), both of which hold for every space-filling SLE model.

The numbering is that of the paper (`paper/idla_mated_crt-corrected.tex`).
-/

open MeasureTheory

namespace MatedCRT

/-- **Lemma 5.4** (lower bound for `L`) at the canonical model, from `CanonicalHypotheses ν`. -/
theorem lLowerBound_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    LLowerBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  FirstPassClosure.closed_5_4_clean ν (certifiedReferenceModel_canonical ν H)
    (frozenBG20GreenCrudeCanonical_holds _)

/-- **Lemma 7.2** (mass bound for the odometer above the scale) at the canonical model, from `CanonicalHypotheses ν`:
the corrected statement `MassBoundOdometerAboveScaleStmt` (above the scale), as in the counted form `closed_7_2`
(`docs/campaign/COUNTED.md`). -/
theorem massBoundOdometerAboveScale_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    MassBoundOdometerAboveScaleStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_7_2 ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 7.4** (crude upper bound for the odometer along `V`-paths) at the canonical model. Lemma 7.4 is a cited
lemma whose proof is given in this repository. Its two inputs, the corrected Lemma 4.4 (`closed_4_4`) and the degree
bound (`degreeBoundInput_holds`), hold for every space-filling SLE model, hence there is no hypothesis
`CanonicalHypotheses ν`. -/
theorem crudeUpperBound_canonical (ν : ℝ → Measure SLEPathCode) :
    CrudeUpperBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  crudeUpperBound_of_corrected closed_4_4 (degreeBoundInput_holds _)

end MatedCRT
