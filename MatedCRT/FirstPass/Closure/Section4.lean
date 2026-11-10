import MatedCRT.FirstPass.S3S4

/-!
# Closed results, Section 4 (task fp-Closure-counted-results, worker z1)

Closed: 4.3 (`closed_4_3`), 4.4 (`closed_4_4`, corrected form), 4.5 (`closed_4_5`, corrected form), 4.7 (`closed_4_7`).
Not closed: 4.1 (printed Lemma 3.5 `DiscreteDirichletProblemStmt`), 4.6 and 4.8 (same input, and 3.7). See the report.
-/

namespace MatedCRT

/-- Lemma 4.3 (discrete basic properties), closed. No hypotheses beyond `𝒮`. -/
alias closed_4_3 := firstPass_4_3

/-- Lemma 4.4 (discrete Laplacian bound), closed in the corrected form `DiscreteLaplacianBoundCorrectedStmt`. -/
alias closed_4_4 := firstPass_4_4_corrected

/-- Lemma 4.5 (discrete conservation of mass), closed in the corrected form `DiscreteConservationOfMassCorrectedStmt`. -/
alias closed_4_5 := firstPass_4_5_corrected

/-- Lemma 4.7 (equiboundedness), closed. Hypotheses: `VolumeGrowthStmt`, `ExitTimeUpperBoundStmt 𝒮` (cited),
`MepsScalingInput 𝒮` (External). -/
alias closed_4_7 := firstPass_4_7

end MatedCRT
