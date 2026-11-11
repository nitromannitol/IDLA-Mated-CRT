import MatedCRT.FirstPass.S2y.ConeFieldPairing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# `ConeCircleDecoderStep`: Borel decoder from in-probability pairing approximants

Section 4 of the decoder write-up (lines 362–578) proves that
every pairing of a quantum cone is almost surely a measurable function of its circle average process, in three steps:
4.1 a measurable approximant of each pairing from countably many circle coordinates (Riemann sums over the plane);
4.2 convergence in probability of the approximants to the pairing;
4.3 extraction of a Borel decoder from an almost surely convergent subsequence and `limsup`.

This file proves 4.3 in general (`exists_borel_decoder_of_tendstoInMeasure`) and the reduction
`coneCircleDecoderStep_of_pairingApprox`: `ConeCircleDecoderStep` follows from approximants `A φ n` that are
measurable (4.1, named binder `hA`) and converge in probability to every pairing of every quantum cone (4.2, named
binder `hconv`). Not yet proved here: `hA` (section 1 `measurable_planeQuad_eval` of `S2y/ConeRadialCodes.lean`) and `hconv` (the whole-plane GFF L² computation and the radial approximate identity).
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped NNReal ENNReal

/-- **Borel decoder extraction.** An in-probability limit of measurable functionals `F n` of an
observable `X` is almost surely equal to a measurable functional of `X`: take an almost surely convergent subsequence
and the pointwise `limsup` of the subsequence. -/
theorem exists_borel_decoder_of_tendstoInMeasure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} (X : Ω → E) (F : ℕ → E → ℝ) (hF : ∀ n, Measurable (F n)) (g : Ω → ℝ)
    (hconv : TendstoInMeasure P (fun n ω => F n (X ω)) atTop g) :
    ∃ D : E → ℝ, Measurable D ∧ (fun ω => D (X ω)) =ᵐ[P] g := by
  obtain ⟨ns, -, hae⟩ := hconv.exists_seq_tendsto_ae
  refine ⟨fun e => limsup (fun i => F (ns i) e) atTop, Measurable.limsup fun i => hF (ns i), ?_⟩
  filter_upwards [hae] with ω hω
  exact hω.limsup_eq

/-- **Reduction of `ConeCircleDecoderStep` to pairing approximants.** Named binders: `hA` is the
measurability of the approximants as functionals of the circle average process (§4.1); `hconv` is the convergence in
probability of the approximants to the pairings of every quantum cone (§4.2). -/
theorem coneCircleDecoderStep_of_pairingApprox
    (A : (ℂ → ℝ) → ℕ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hA : ∀ (φ : ℂ → ℝ) (n : ℕ), Measurable (A φ n))
    (hconv : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        TendstoInMeasure P (fun n ω => A φ n (circleProcess (hcirc ω))) atTop (fun ω => hC ω φ)) :
    ConeCircleDecoderStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc hP hQ φ hφ
  obtain ⟨D, hD, hae⟩ := exists_borel_decoder_of_tendstoInMeasure (fun ω => circleProcess (hcirc ω))
    (A φ) (hA φ) (fun ω => hC ω φ) (hconv γ hγ hγ2 Ω P hC hcirc hP hQ φ hφ)
  exact ⟨D, hD, hae⟩

end MatedCRT.LQGMeasure

#print axioms MatedCRT.LQGMeasure.exists_borel_decoder_of_tendstoInMeasure
#print axioms MatedCRT.LQGMeasure.coneCircleDecoderStep_of_pairingApprox
