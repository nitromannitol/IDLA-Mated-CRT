import MatedCRT.FirstPass.S2y.ConeFieldScaling
import MatedCRT.Proofs.Sec1.EnvironmentScaling.IntegrableReferenceObservables

/-!
# `ConeFieldScalingStep` without the pairing realization `hpair`

`coneFieldScalingStep_proved` (ConeFieldScaling.lean) takes the same-carrier pairing realization `hpair` as a
binder. Here the pairings of the rescaled cone are built from the circle average process (Duplantier-Sheffield,
arXiv:1409.7055, Proposition 4.13(i); the hpair write-up, section B):
`hC' ω φ := D φ (circleProcess (c ω))` with `D φ` a measurable decoder of the pairing `φ` from the circle average
process of the cone.

Proved here, without any extra input: the measurability of the circle process of a measurable version, the radial
process as a measurable functional of the circle process, the transfer of the radial law through the circle law
identity `QuantumConeScalingInput`, and the continuity of the rescaled circle process.

Two named inputs replace `hpair`:
* `ConeCircleDecoderStep` (section B.2, the pairing decoder): a pairing of a cone is an almost sure measurable
  function of its circle average process;
* `ConeLateralTransferStep` (section B.3, not written there in full): for any such decoder family and any measurable
  version of the rescaled circle process, the joint law of (circle process, lateral process) of the decoded field
  equals that of the original cone. Section B.3 treats only the pairings and the circle values; the lateral part
  also contains the radial integral `∫ φ(x) h_{|x|}(0) dx` and the circle averages of the radial part over spheres
  (`lateralEval`, Defs/QuantumCone.lean), which are not finite-coordinate functionals of the circle process.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.LQGMeasure

/-- The radial part of a circle average profile `q`: `t ↦ q(e^{-t}, 0)` and `s ↦ q(e^{s}, 0)`, `t, s ≥ 0`
(the pair of paths of `radialProcess`, Defs/QuantumCone.lean). -/
noncomputable def radialOfCircle (q : Set.Ioi (0 : ℝ) × ℂ → ℝ) : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun t => q (⟨Real.exp (-(t : ℝ)), Real.exp_pos _⟩, 0), fun s => q (⟨Real.exp (s : ℝ), Real.exp_pos _⟩, 0))

theorem radialProcess_eq_radialOfCircle (hcirc : ℝ → ℂ → ℝ) :
    radialProcess hcirc = radialOfCircle (circleProcess hcirc) :=
  rfl

theorem measurable_radialOfCircle : Measurable radialOfCircle :=
  (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

/-- The circle process of a family of random circle profiles, measurable in `ω` at each `(r, z)` with `r > 0`, is a
random element of the product σ-algebra on `Ioi 0 × ℂ → ℝ`. -/
theorem measurable_circleProcess_of {Ω : Type} [MeasurableSpace Ω] {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) :
    Measurable fun ω => circleProcess (c ω) :=
  measurable_pi_iff.mpr fun p : Set.Ioi (0 : ℝ) × ℂ => hcm p.1.1 p.2 p.1.2

/-- The rescaled circle average process `(r, z) ↦ h_{Rr}(Rz) + Q log R - γ⁻¹ log b` (`rescaledCircle`) is
continuous on `(0, ∞) × ℂ` when `h` is, and `R > 0`. -/
theorem continuousOn_rescaledCircle (γ b R : ℝ) {h : ℝ → ℂ → ℝ} (hR : 0 < R)
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × ℂ => rescaledCircle γ h R b p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hmap : MapsTo (fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (Set.Ioi 0 ×ˢ Set.univ)
      (Set.Ioi 0 ×ˢ Set.univ) := by
    intro p hp
    exact ⟨mul_pos hR hp.1, Set.mem_univ _⟩
  have hcont : ContinuousOn (fun p : ℝ × ℂ => (R * p.1, (R : ℂ) * p.2)) (Set.Ioi 0 ×ˢ Set.univ) :=
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)).continuousOn
  exact (((hh.comp hcont hmap).add continuousOn_const).sub continuousOn_const)

/-- **Named input (section B.2, the pairing decoder).** For every quantum cone and every test function `φ`, the
pairing `hC · φ` agrees almost surely with a measurable function of the circle average process: `(h, φ)` is
recovered from the circle averages `h_r(z)` (Duplantier-Sheffield, arXiv:1409.7055, Definition 4.10 and Lemma 4.9;
Duplantier-Sheffield, arXiv:0808.1560, Section 3.1). Not written in full in the answer (its convergence step is a
sketch). -/
def ConeCircleDecoderStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
    ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      ∃ D : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ, Measurable D ∧
        (fun ω => D (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ)

/-- **Named input (section B.3, lateral transfer; not in the answer).** For a quantum cone `(hC, hcirc)`, a
measurable version `c` of the rescaled circle process (`c = rescaledCircle` a.s.), and a family `D` of pairing
decoders of the cone (`D φ ∘ circleProcess ∘ hcirc = hC φ` a.s.), the joint law of the circle process and of the
lateral process of the decoded field `ω ↦ (φ ↦ D φ (circleProcess (c ω)))` over `c` equals the joint law of
`(circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))`. Its truth needs the radial integral and the sphere
averages of the radial part to be almost surely universal measurable functionals of the circle average process. -/
def ConeLateralTransferStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc → ∀ b : ℝ, 0 < b →
    ∀ (c : Ω → ℝ → ℂ → ℝ) (D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, c ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) →
      (∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable (D φ) ∧
        (fun ω => D φ (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ)) →
      P.map (fun ω => (circleProcess (c ω), lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) =
        P.map (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))

/-- **`ConeFieldScalingStep` from the decoder inputs, without `hpair`.** Same conclusion as
`coneFieldScalingStep_proved`: the rescaled version `c` of the circle process is a measurable circle process of a
quantum cone whose pairings are the decoded `hC' ω φ := D φ (circleProcess (c ω))`. -/
theorem coneFieldScalingStep_of_decoder (hscale : QuantumConeScalingInput) (hdec : ConeCircleDecoderStep)
    (hlat : ConeLateralTransferStep) : ConeFieldScalingStep := by
  intro γ hγ hγ2 Ω inst P hC hcirc hP hcone b hb
  have := hP
  obtain ⟨c, hcm, hc⟩ := exists_measurable_rescaledCircle_version hscale hγ hγ2 hcone hb
  have hpos := MatedCRT.Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hcone hb
  have hD : ∀ φ : ℂ → ℝ, ∃ D : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ,
      IsTestFunction Set.univ φ → (Measurable D ∧ (fun ω => D (circleProcess (hcirc ω))) =ᵐ[P] fun ω => hC ω φ) := by
    intro φ
    by_cases hφ : IsTestFunction Set.univ φ
    · obtain ⟨D, hDm, hDa⟩ := hdec γ hγ hγ2 Ω P hC hcirc hP hcone φ hφ
      exact ⟨D, fun _ => ⟨hDm, hDa⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hφ⟩
  choose D hDprop using hD
  have hcirc_c : Measurable fun ω => circleProcess (c ω) := measurable_circleProcess_of hcm
  have hcirc_h : Measurable fun ω => circleProcess (hcirc ω) :=
    measurable_circleProcess_of hcone.measurable_circle
  have hlawc : P.map (fun ω => circleProcess (c ω)) = P.map (fun ω => circleProcess (hcirc ω)) := by
    calc P.map (fun ω => circleProcess (c ω))
        = P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) :=
          Measure.map_congr (hc.mono fun ω hω => congrArg circleProcess hω)
      _ = P.map (fun ω => circleProcess (hcirc ω)) := hscale γ hγ hγ2 Ω P hC hcirc hP hcone b hb
  have hradc : P.map (fun ω => radialProcess (c ω)) = P.map (fun ω => radialProcess (hcirc ω)) := by
    have e : ∀ X : Ω → ℝ → ℂ → ℝ, (fun ω => radialProcess (X ω)) =
        radialOfCircle ∘ (fun ω => circleProcess (X ω)) := fun X => rfl
    rw [e c, e hcirc, ← Measure.map_map measurable_radialOfCircle hcirc_c,
      ← Measure.map_map measurable_radialOfCircle hcirc_h, hlawc]
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
    filter_upwards [hcone.ae_continuousOn_circle, hc, hpos] with ω hω hcω hpω
    rw [hcω]
    exact continuousOn_rescaledCircle γ b _ hpω hω
  have hlatc := hlat γ hγ hγ2 Ω P hC hcirc hP hcone b hb c D hcm hc hDprop
  have hpair_h : AEMeasurable (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hcirc_h.aemeasurable.prodMk (MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hcone)
  have hlath_ae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hcone
  -- the decoded lateral process is a.e. measurable by the same argument, applied to the fields proved above
  have hlatc_ae : AEMeasurable (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) P :=
    MatedCRT.CirclePairing.aemeasurable_lateralProcess (hC := fun ω φ => D φ (circleProcess (c ω)))
      (hcirc := c) (fun φ hφ => (hDprop φ hφ).1.comp hcirc_c) hcm hcont
  have hpair_c : AEMeasurable (fun ω => (circleProcess (c ω),
      lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) P :=
    hcirc_c.aemeasurable.prodMk hlatc_ae
  have hlat_law : P.map (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) =
      P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) := by
    calc P.map (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))
        = P.map (Prod.snd ∘ fun ω => (circleProcess (c ω),
            lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) := rfl
      _ = ((P.map (fun ω => (circleProcess (c ω),
            lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)))).map Prod.snd) :=
          (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpair_c).symm
      _ = ((P.map (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))).map Prod.snd) := by
          rw [hlatc]
      _ = P.map (Prod.snd ∘ fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) :=
          AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpair_h
      _ = P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) := rfl
  have Φ : Measurable (fun x : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
      (radialOfCircle x.1, x.2)) :=
    (measurable_radialOfCircle.comp measurable_fst).prodMk measurable_snd
  have hJ : P.map (fun ω => (radialProcess (c ω), lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) =
      P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) := by
    calc P.map (fun ω => (radialProcess (c ω), lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)))
        = P.map ((fun x : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
            (radialOfCircle x.1, x.2)) ∘ fun ω => (circleProcess (c ω),
              lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) := rfl
      _ = ((P.map (fun ω => (circleProcess (c ω),
            lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)))).map
            (fun x : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
              (radialOfCircle x.1, x.2))) :=
          (AEMeasurable.map_map_of_aemeasurable Φ.aemeasurable hpair_c).symm
      _ = ((P.map (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))).map
            (fun x : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
              (radialOfCircle x.1, x.2))) := by rw [hlatc]
      _ = P.map ((fun x : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
            (radialOfCircle x.1, x.2)) ∘ fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) :=
          AEMeasurable.map_map_of_aemeasurable Φ.aemeasurable hpair_h
      _ = P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) := rfl
  have hradh_meas : Measurable fun ω => radialProcess (hcirc ω) :=
    measurable_radialOfCircle.comp hcirc_h
  have hradc_meas : Measurable fun ω => radialProcess (c ω) :=
    measurable_radialOfCircle.comp hcirc_c
  have hindep_c : IndepFun (fun ω => radialProcess (c ω))
      (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hradc_meas.aemeasurable hlatc_ae, hJ]
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map hradh_meas.aemeasurable hlath_ae).1 hcone.indep
    rw [hprod, hradc, hlat_law]
  refine ⟨fun ω φ => D φ (circleProcess (c ω)), c, ?_, hc⟩
  refine ⟨fun φ hφ => (hDprop φ hφ).1.comp hcirc_c, hcm, hcont, ?_, hindep_c, ?_⟩
  · obtain ⟨ν, hν, hνmap⟩ := hcone.radial_law
    exact ⟨ν, hν, hradc.trans hνmap⟩
  · obtain ⟨Ω', i', P', hC'', hcirc'', hP', hW, hL⟩ := hcone.lateral_law
    exact ⟨Ω', i', P', hC'', hcirc'', hP', hW, hlat_law.trans hL⟩

end MatedCRT.LQGMeasure
