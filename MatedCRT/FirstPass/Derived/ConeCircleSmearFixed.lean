import MatedCRT.FirstPass.S2y.LateralAssembly250

/-!
# The circle smear identity for the quantum cone at a fixed radius

For the circle average embedding of the `γ`-quantum cone (`IsQuantumCone`), a test function `φ` and `ε ∈ (0, 1]`,
almost surely `∫ φ(z) h_ε(z) dz = (h, circleKernel φ ε)` (`CircleSmearIdentity`), provided that almost surely the
fourth power of the radial part `s ↦ h_s(0)` (its jointly measurable version `radialVersion`) is integrable on every
`(0, n]`.

Route. For the whole-plane GFF the identity is `circleSmear_ae_eq`. On every sample with continuous circle averages
and a locally `L⁴` radial part, it is equivalent to the identity
`lateralSmearOf φ ε ℓ = ℓ (pairing (circleKernel φ ε))` for the lateral process `ℓ = lateralProcess hC hcirc`:
the lateral circle smear is `∫ φ h_ε - ∫ (circleKernel φ ε)(x) h_{|x|}(0) dx` (`lateralSmearOf_eq_integral_sub`,
from `lateralSmearOf_eq_pathwise` applied to the constant pairing `∫ φ h_ε`), and the lateral pairing is
`(h, circleKernel φ ε) - ∫ (circleKernel φ ε)(x) h_{|x|}(0) dx` (`lateralProcess_pairing_eq`). The lateral identity
is an event of the product σ-algebra of the lateral process (`measurable_lateralSmearOf`), so it transfers from the
whole-plane GFF to the cone through `IsQuantumCone.lateral_law`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped Real ENNReal

namespace MatedCRT.LQGMeasure

/-- The lateral circle smear reads only the circle observables of the lateral process, which do not depend on the
pairing functional. -/
lemma lateralSmearOf_lateralProcess_congr (A B : (ℂ → ℝ) → ℝ) (c : ℝ → ℂ → ℝ) (φ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    lateralSmearOf φ ε hε (lateralProcess A c) = lateralSmearOf φ ε hε (lateralProcess B c) := by
  unfold lateralSmearOf
  congr 1

/-- **Pathwise lateral circle smear.** On a sample with continuous circle averages and a locally `L⁴` radial version,
for `φ` continuous with compact support and `ε ∈ (0, 1]`, the lateral circle smear is
`∫ φ h_ε - ∫ (circleKernel φ ε)(x) h_{|x|}(0) dx`, whatever the pairing functional `hC`. -/
lemma lateralSmearOf_eq_integral_sub {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hB : ∀ n : ℕ, IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ)))
    (hm : Measurable (MatedCRT.CirclePairing.radialVersion hcirc ω))
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    lateralSmearOf φ ε hε (lateralProcess (hC ω) (hcirc ω)) =
      (∫ z, φ z * hcirc ω ε z) -
        ∫ x, circleKernel φ ε x * MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖ := by
  have hA : ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Ioi 0) :=
    (MatedCRT.CirclePairing.continuousOn_radial hω).congr fun s hs => radialVersion_eq_of_cont hω hs
  have hR3 : ∫ z, φ z * hcirc ω ε z = (fun (ω' : Ω) (_ : ℂ → ℝ) => ∫ z, φ z * hcirc ω' ε z) ω (circleKernel φ ε) :=
    rfl
  have key : lateralSmearOf φ ε hε (lateralProcess (fun _ => ∫ z, φ z * hcirc ω ε z) (hcirc ω)) =
      (∫ z, φ z * hcirc ω ε z) -
        ∫ x, circleKernel φ ε x * MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖ :=
    lateralSmearOf_eq_pathwise (hC := fun (ω' : Ω) (_ : ℂ → ℝ) => ∫ z, φ z * hcirc ω' ε z) (ω := ω) hω hA hB hm
      hφc hφs hε hε1 hR3
  rw [lateralSmearOf_lateralProcess_congr (hC ω) (fun _ => ∫ z, φ z * hcirc ω ε z) (hcirc ω) φ hε]
  exact key

/-- **The circle smear identity for the quantum cone at a fixed radius**, from the almost sure local `L⁴`
integrability of the radial part: for every test function `φ` and `ε ∈ (0, 1]`, almost surely
`∫ φ(z) h_ε(z) dz = (h, circleKernel φ ε)`. -/
theorem IsQuantumCone.circleSmear_ae_eq_of_radialL4 {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc)
    (hL4 : ∀ᵐ ω ∂P, ∀ n : ℕ,
      IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ)))
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CircleSmearIdentity P hC hcirc φ ε := by
  obtain ⟨Ω', _, P', hC', hcirc', hP', hG, hlaw⟩ := hQ.lateral_law
  have := hP'
  have hκ : IsTestFunction univ (circleKernel φ ε) := isTestFunction_circleKernel hφ hε.le
  have hSm : MeasurableSet {ℓ : GFFObservable.Admissible → ℝ |
      lateralSmearOf φ ε hε ℓ = ℓ ⟨.pairing (circleKernel φ ε), hκ⟩} :=
    measurableSet_eq_fun (measurable_lateralSmearOf φ ε hε) (measurable_pi_apply _)
  have hΛ : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.CirclePairing.aemeasurable_lateralProcess hQ.measurable_pairing hQ.measurable_circle
      hQ.ae_continuousOn_circle
  have hΛ' : AEMeasurable (fun ω' => lateralProcess (hC' ω') (hcirc' ω')) P' :=
    MatedCRT.CirclePairing.aemeasurable_lateralProcess hG.measurable_pairing hG.measurable_circle
      hG.ae_continuousOn_circle
  -- the lateral identity for the whole-plane GFF
  have hR3 : ∀ᵐ ω' ∂P', ∫ z, φ z * hcirc' ω' ε z = hC' ω' (circleKernel φ ε) := circleSmear_ae_eq hG hφ hε hε1
  have hGS : ∀ᵐ ω' ∂P', lateralSmearOf φ ε hε (lateralProcess (hC' ω') (hcirc' ω')) =
      lateralProcess (hC' ω') (hcirc' ω') ⟨.pairing (circleKernel φ ε), hκ⟩ := by
    filter_upwards [hG.ae_continuousOn_circle, ae_integrableOn_radialVersion_pow_four hG, hR3] with ω' hω hB hR
    have hm : Measurable (MatedCRT.CirclePairing.radialVersion hcirc' ω') := measurable_radialVersion_slice hG ω'
    rw [lateralSmearOf_eq_integral_sub hω hB hm hφ.1.continuous hφ.2.1 hε hε1, lateralProcess_pairing_eq hω hκ, hR]
  -- transfer to the cone through the law of the lateral process
  have hmapG : ∀ᵐ ℓ ∂(P'.map fun ω' => lateralProcess (hC' ω') (hcirc' ω')),
      lateralSmearOf φ ε hε ℓ = ℓ ⟨.pairing (circleKernel φ ε), hκ⟩ := (ae_map_iff hΛ' hSm).2 hGS
  rw [← hlaw] at hmapG
  have hcone := (ae_map_iff hΛ hSm).1 hmapG
  -- the cone side, pathwise
  unfold CircleSmearIdentity
  have hcone' : ∀ᵐ ω ∂P, lateralSmearOf φ ε hε (lateralProcess (hC ω) (hcirc ω)) =
      lateralProcess (hC ω) (hcirc ω) ⟨.pairing (circleKernel φ ε), hκ⟩ := hcone
  filter_upwards [hcone', hQ.ae_continuousOn_circle, hL4] with ω hS hω hB
  have hm : Measurable (fun s : ℝ => MatedCRT.CirclePairing.radialVersion hcirc ω s) := by
    have key := (MatedCRT.CirclePairing.measurable_radialVersion hQ.measurable_circle).comp
      (measurable_const.prodMk measurable_id : Measurable (fun s : ℝ => (ω, s)))
    simp only [Function.comp_def] at key
    exact key
  have h1 := lateralSmearOf_eq_integral_sub (hC := hC) hω hB hm hφ.1.continuous hφ.2.1 hε hε1
  have h2 := lateralProcess_pairing_eq (hC := hC) hω hκ
  rw [hS, h2] at h1
  linarith

end MatedCRT.LQGMeasure
