import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.LPStaging.Prob.CameronMartinEquivalence
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.Proofs.Sec8.ExteriorLaplacianIndependence
import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne

/-!
# Bridge: mutual absolute continuity of the whole-plane pairing laws under a smooth shift

`FPPairingLawIG4` (`FirstPass/Frozen/S4S5b.lean`) asserts that, for a whole-plane GFF `(Q, hC, hcirc)`, a real `α`
and a smooth compactly supported `g`, the law of the pairings modulo constants of `h + g` is mutually absolutely
continuous with the law of the pairings modulo constants of `h`.

The proof is the Cameron–Martin argument. The shift `g` is a Cameron–Martin direction: its covariance preimage is the
zero-mean test function `f_g = -(2π)⁻¹ Δg`, since `∫ φ(x) (∫ f_g(y) K(x,y) dy) dx = ∫ g φ` for zero-mean `φ`, with
`K` the whole-plane covariance kernel `wholePlaneCov` (`integral_laplacian_mul_wholePlaneCov`). The pairings with
zero-mean test functions form a centred Gaussian family `X₀` with `covShift X₀ Q (single f_g 1) φ = ∫ g φ`, and the
constant `α`-part of `fieldPairing` is a deterministic translation. The general Cameron–Martin equivalence
`LatticeProb.gaussian_map_shift_absolutelyContinuous` then gives the two absolute continuities.

Literature locator: Cameron–Martin theorem; Miller–Sheffield (arXiv:1302.4738v2, Prop. 2.9, eq. (2.8)) as cited in
`FPPairingLawIG4`.
-/

open MeasureTheory Filter Topology Set Laplacian ProbabilityTheory HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace PairingLawIG4

/-- The zero-mean Cameron–Martin direction `f_g = -(2π)⁻¹ Δg` of a smooth compactly supported `g`. -/
noncomputable def cmDirection (g : ℂ → ℝ) : ℂ → ℝ := fun x => -(2 * Real.pi)⁻¹ * Δ g x

theorem isTestFunction_cmDirection {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    IsTestFunction univ (cmDirection g) := by
  refine ⟨?_, ?_, subset_univ _⟩
  · exact contDiff_const.mul (contDiff_laplacian_of_smooth hg.1)
  · exact (hasCompactSupport_laplacian hg.2.1).mul_left

theorem integral_cmDirection {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    ∫ x, cmDirection g x = 0 := by
  unfold cmDirection
  rw [integral_const_mul, integral_laplacian_eq_zero (hg.1.of_le (by norm_cast)) hg.2.1, mul_zero]

/-- The covariance of a zero-mean test function `φ` with the Cameron–Martin direction of `g` is the pairing `∫ g φ`. -/
theorem wholePlaneGFFCov_pairing_cmDirection {g φ : ℂ → ℝ} (hg : IsTestFunction univ g)
    (hφ : IsTestFunction univ φ) (hφz : ∫ x, φ x = 0) :
    wholePlaneGFFCov (.pairing φ) (.pairing (cmDirection g)) = ∫ x, g x * φ x := by
  have hg2 : ContDiff ℝ 2 g := hg.1.of_le (by norm_cast)
  have hK : ∀ x, (∫ y, cmDirection g y * wholePlaneCov x y) = g x - (∫ y, Δ g y * wholePlaneNormalization y) / (2 * Real.pi) := by
    intro x
    have h1 : ∀ y, cmDirection g y * wholePlaneCov x y = -(2 * Real.pi)⁻¹ * (Δ g y * wholePlaneCov x y) := by
      intro y
      unfold cmDirection
      ring
    simp_rw [h1]
    rw [integral_const_mul, integral_laplacian_mul_wholePlaneCov hg2 hg.2.1 x]
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    ring
  show ∫ x, φ x * ∫ y, cmDirection g y * wholePlaneCov x y = ∫ x, g x * φ x
  simp_rw [hK]
  have hgc : Continuous g := hg.1.continuous
  have hφc : Continuous φ := hφ.1.continuous
  have h2 : ∀ x, φ x * (g x - (∫ y, Δ g y * wholePlaneNormalization y) / (2 * Real.pi))
      = g x * φ x - ((∫ y, Δ g y * wholePlaneNormalization y) / (2 * Real.pi)) * φ x := by
    intro x
    ring
  simp_rw [h2]
  rw [integral_sub, integral_const_mul, hφz, mul_zero, sub_zero]
  · exact (hgc.mul hφc).integrable_of_hasCompactSupport (hg.2.1.mul_right)
  · exact ((hφc.integrable_of_hasCompactSupport hφ.2.1).const_mul _)

end PairingLawIG4

open PairingLawIG4

/-- The pairings modulo constants of `h + g` and of `h` have mutually absolutely continuous laws, for a whole-plane GFF
and a smooth compactly supported `g` (`FPPairingLawIG4`, unconditional). -/
theorem fpPairingLawIG4_holds : FPPairingLawIG4 := by
  intro Ω _ Q hC hcirc hQ α g hg
  let X0 : LocalZeroMeanTest (univ : Set ℂ) → Ω → ℝ := fun φ ω => hC ω φ.1
  let f0 : LocalZeroMeanTest (univ : Set ℂ) :=
    ⟨cmDirection g, isTestFunction_cmDirection hg, integral_cmDirection hg⟩
  let σ : LocalZeroMeanTest (univ : Set ℂ) →₀ ℝ := Finsupp.single f0 1
  let c : LocalZeroMeanTest (univ : Set ℂ) → ℝ := fun φ => -α * ∫ x, φ.1 x * Real.log ‖x‖
  have hX0 : IsGaussianProcess X0 Q :=
    hQ.isGaussianProcess.comp_right
      (fun φ : LocalZeroMeanTest (univ : Set ℂ) =>
        (⟨GFFObservable.pairing φ.1, φ.2.1⟩ : GFFObservable.Admissible))
  have hmeas : ∀ φ, Measurable (X0 φ) := fun φ => hQ.measurable_pairing φ.1 φ.2.1
  have hcent : ∀ φ : LocalZeroMeanTest (univ : Set ℂ), ∫ ω, X0 φ ω ∂Q = 0 :=
    fun φ => hQ.integral_eq_zero (.pairing φ.1) φ.2.1
  have hcov : ∀ φ : LocalZeroMeanTest (univ : Set ℂ),
      QuantumZipper.CameronMartin.covShift X0 Q σ φ = ∫ x, g x * φ.1 x := by
    intro φ
    have hs : σ.support = {f0} := by simp [σ]
    have hσf : σ f0 = 1 := by simp [σ]
    unfold QuantumZipper.CameronMartin.covShift QuantumZipper.CameronMartin.covK
    rw [hs, Finset.sum_singleton, hσf, one_mul]
    have hadm : (GFFObservable.pairing f0.1).IsAdmissible := f0.2.1
    have hcovX : cov[X0 φ, X0 f0; Q] = wholePlaneGFFCov (.pairing φ.1) (.pairing f0.1) :=
      hQ.covariance_eq (.pairing φ.1) (.pairing f0.1) φ.2.1 hadm
    exact hcovX.trans (wholePlaneGFFCov_pairing_cmDirection hg φ.2.1 φ.2.2)
  let S : Ω → (LocalZeroMeanTest (univ : Set ℂ) → ℝ) :=
    fun ω j => X0 j ω + QuantumZipper.CameronMartin.covShift X0 Q σ j
  let Xp : Ω → (LocalZeroMeanTest (univ : Set ℂ) → ℝ) := fun ω j => X0 j ω
  let T : (LocalZeroMeanTest (univ : Set ℂ) → ℝ) → (LocalZeroMeanTest (univ : Set ℂ) → ℝ) :=
    fun v j => v j + c j
  have hA : ∀ ω, localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω = T (S ω) := by
    intro ω
    funext φ
    simp only [localModConstPairings, fieldPairing, addFunPairing, T, S, X0, c, hcov φ]
    ring
  have hB : ∀ ω, localModConstPairings α hC univ ω = T (Xp ω) := by
    intro ω
    funext φ
    simp only [localModConstPairings, fieldPairing, T, Xp, X0, c]
    ring
  have hproj : ∀ j : LocalZeroMeanTest (univ : Set ℂ),
      Measurable fun v : LocalZeroMeanTest (univ : Set ℂ) → ℝ => v j := fun j => measurable_pi_apply j
  have hTm : Measurable T := Measurable.of_eval fun j => by
    simp only [T]
    exact (hproj j).add_const (c j)
  have hSm : Measurable S := Measurable.of_eval fun j => (hmeas j).add_const _
  have hXm : Measurable Xp := Measurable.of_eval fun j => hmeas j
  have hEq1 : Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) = (Q.map S).map T := by
    rw [Measure.map_map hTm hSm]
    congr 1
    funext ω
    exact hA ω
  have hEq2 : Q.map (localModConstPairings α hC univ) = (Q.map Xp).map T := by
    rw [Measure.map_map hTm hXm]
    congr 1
    funext ω
    exact hB ω
  obtain ⟨h1, h2⟩ := LatticeProb.gaussian_map_shift_absolutelyContinuous hX0 hmeas hcent σ
  have h1' : Q.map S ≪ Q.map Xp := h1
  have h2' : Q.map Xp ≪ Q.map S := h2
  rw [hEq1, hEq2]
  exact ⟨LatticeProb.map_absolutelyContinuous_of_absolutelyContinuous h1' hTm,
    LatticeProb.map_absolutelyContinuous_of_absolutelyContinuous h2' hTm⟩

end MatedCRT
