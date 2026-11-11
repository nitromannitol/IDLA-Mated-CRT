import MatedCRT.Proofs.Field.LawTransferCovariance

/-!
# Interface bridge between the two whole-plane GFF structures

Two structures describe a whole-plane Gaussian free field `h^ℂ` (Duplantier–Sheffield 2011, normalised as in
Bonanno's `LQGMetric` interface; the covariance kernel is `-log|x - y|` on mean-zero test functions):

* `HarmonicBalls.IsWholePlaneGFF P hC hcirc` records the pairings `hC ω φ` with smooth compactly supported test
  functions and the circle averages `hcirc ω r z`, together with their joint Gaussianity, centring, covariance
  `wholePlaneGFFCov`, and the almost sure continuity of the circle averages in `(r, z)`;
* `LQGMetric.IsWholePlaneGFF h P` records one random distribution `h : Ω → LQGMetric.DistC` whose pairings with
  mean-zero test functions form a centred Gaussian process with covariance `LQGMetric.logCov`.

The bridge proved here goes from the Harmonic Balls interface to Bonanno's: a distribution-valued random field `H`
on the same probability space whose mean-zero test pairings agree almost surely with `hC` is a whole-plane GFF in
Bonanno's sense. The converse is not stated: a Harmonic Balls structure built from a Bonanno field would need the
circle averages and their continuity in `(r, z)`, which `LQGMetric.IsWholePlaneGFF` does not fix.
-/

namespace MatedCRT.GFFInterface

open MeasureTheory ProbabilityTheory Set

/-- The covariance of two real random variables is unchanged when each is modified on a null set. -/
lemma cov_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- **Harmonic Balls to Bonanno.** Let `(hC, hcirc)` be a whole-plane GFF in the Harmonic Balls interface and let
`H : Ω → LQGMetric.DistC` be measurable with `hC ω φ = H ω φ` for almost every `ω` and every test function `φ`.
Then `H` is a whole-plane GFF in the interface `LQGMetric.IsWholePlaneGFF`.

Field by field: measurability is the hypothesis `hH`; the Gaussian family of mean-zero pairings is the image of the
Harmonic Balls Gaussian family under the index map `φ ↦ pairing φ`, transported by almost sure equality; centring
and covariance transfer along the same almost sure equality, and the covariance is the Harmonic Balls kernel
`wholePlaneGFFCov` on pairings, which equals Bonanno's `logCov` on mean-zero test functions
(`MatedCRT.Field.wholePlaneGFFCov_eq_logCov`). -/
theorem isWholePlaneGFF_of_harmonicBalls {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ) :
    LQGMetric.IsWholePlaneGFF H P := by
  have hae (φ : LQGMetric.TestC) : (fun ω => hC ω φ) =ᵐ[P] fun ω => H ω φ :=
    hrep.mono fun ω hω => hω φ
  let f : LQGMetric.TestC0 → HarmonicBalls.GFFObservable.Admissible :=
    fun φ => ⟨.pairing φ.1, MatedCRT.Field.isTestFunction_of_TestC φ.1⟩
  refine
    { measurable := hH
      gaussian := ?_
      centered := ?_
      covariance_eq := ?_ }
  · exact (hwp.isGaussianProcess.comp_right f).congr fun φ => hae φ.1
  · intro φ
    calc ∫ ω, H ω φ.1 ∂P = ∫ ω, hC ω φ.1 ∂P := integral_congr_ae (hae φ.1).symm
      _ = 0 := hwp.integral_eq_zero (.pairing φ.1) (MatedCRT.Field.isTestFunction_of_TestC φ.1)
  · intro φ ψ
    calc cov[fun ω => H ω φ.1, fun ω => H ω ψ.1; P]
        = cov[fun ω => hC ω φ.1, fun ω => hC ω ψ.1; P] :=
          cov_congr_ae (hae φ.1).symm (hae ψ.1).symm
      _ = HarmonicBalls.wholePlaneGFFCov (.pairing φ.1) (.pairing ψ.1) :=
          hwp.covariance_eq (.pairing φ.1) (.pairing ψ.1)
            (MatedCRT.Field.isTestFunction_of_TestC φ.1) (MatedCRT.Field.isTestFunction_of_TestC ψ.1)
      _ = LQGMetric.logCov φ.1 ψ.1 :=
          MatedCRT.Field.wholePlaneGFFCov_eq_logCov (MatedCRT.Field.isTestFunction_of_TestC φ.1)
            (MatedCRT.Field.isTestFunction_of_TestC ψ.1) φ.2 ψ.2

end MatedCRT.GFFInterface
