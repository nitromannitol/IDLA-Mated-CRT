import MatedCRT.FirstPass.S2g.SourceReduction
import MatedCRT.FirstPass.S2g.GoodSetReduction

/-! # The source pathwise gate `SourceHalfBallPathwiseStep` from the Draft statements (fp-S2g, q1)

`SourceHalfBallPathwiseStep` (`GoodSetReduction.lean`) asks, for every `γ ∈ (0,2)` and every whole-plane source `μ` of
`IsLQGMeasureOfField P γ γ`, that `ConePathwiseHalfBallInputs (μ ω)` holds almost surely. It is discharged here by
`ae_conePathwiseHalfBallInputs_of_draft` (`SourceReduction.lean`) from Draft statements of the Harmonic Balls and mated-CRT
papers and the frozen initial confinement `FrozenHBInitialConfinement` (HB Props 5.1-5.2). -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- The side condition `γ < lqgQ γ` of the Draft statements, on `(0,2)`: `lqgQ γ = 2/γ + γ/2`, and `γ/2 < 2/γ` iff `γ² < 4`. -/
theorem lt_lqgQ_of_mem_Ioo {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ0]
    nlinarith
  linarith

/-- **`SourceHalfBallPathwiseStep` from the Draft statements (q1, fp-S2g).** The pathwise half-ball inputs of every
whole-plane source hold almost surely, given the Draft statements (Lemma 3.5, Proposition 5.3, Theorem 5.5, Theorem 1.1,
Proposition 5.6, the obstacle clauses of the mated-CRT paper) and the frozen initial confinement. -/
theorem sourceHalfBallPathwiseStep_of_draft (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement) :
    SourceHalfBallPathwiseStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hP hW hL
  exact ae_conePathwiseHalfBallInputs_of_draft hγ0 hγ2 (lt_lqgQ_of_mem_Ioo hγ0 hγ2) hW hL hOpen hSup hCons hMono
    hCompat hBdry hExist hThm11 hProp56 hconf

end MatedCRT
