import MatedCRT.FirstPass.Derived.CircleSmearDecoder
import MatedCRT.FirstPass.Derived.RescaledCircleSmear
import MatedCRT.FirstPass.S2y.ConeDecoder240
import MatedCRT.FirstPass.S2y.ConeFieldPairing
import MatedCRT.Defs.Setting

/-!
# The rescaled cone field from the circle smears

For the `γ`-quantum cone `h` of an environment and `b > 0`, let `R_b` be the cone scale radius and
`h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b` the rescaled field (eq:quantum-cone-scaling; Duplantier-Miller-Sheffield,
Proposition 4.13(i)). Let `c` be a measurable version of the circle average process of `h^b`.

* `isQuantumCone_decoded`: for any family `D` of measurable pairing decoders of the cone
  (`D φ (circle process of h) = (h, φ)` a.s. for each test function `φ`), the decoded field
  `ω ↦ (φ ↦ D φ (circle process of c ω))` and `c` form a `γ`-quantum cone. This is the argument of
  `coneFieldScalingStep_of_decoder` with the decoder family as a parameter, and the lateral transfer
  `coneLateralTransferStep_proved240`.
* `rescaledConeField_of_circleSmear`: if a.s. `(h, φ) = lim_{ε → 0+} ∫ φ(z) h_ε(z) dz` for all test functions `φ` at
  once, then the circle smear limit `hC' ω φ := Λ_φ(c ω)` (`circleSmearLimit`) satisfies: a.s. for all test `φ`,
  `hC' ω φ` is the pairing of `h^b` with `φ`; each `hC' · φ` is measurable; and `(hC', c)` is a `γ`-quantum cone (in
  particular its lateral part is independent of the radial part and has the law of the lateral part of a whole-plane
  GFF).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls

open MatedCRT.LQGMeasure

namespace MatedCRT.FirstPass.Derived

/-- A test function composed with the dilation `x ↦ R⁻¹ x` (`R ≠ 0`) is a test function. -/
theorem isTestFunction_univ_comp_inv_mul {φ : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0) (hφ : IsTestFunction univ φ) :
    IsTestFunction univ (fun x => φ ((R⁻¹ : ℂ) * x)) := by
  have hRc : (R⁻¹ : ℂ) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 hR)
  obtain ⟨hcd, hcs, -⟩ := hφ
  refine ⟨hcd.comp (contDiff_const.mul contDiff_id), ?_, subset_univ _⟩
  have hfun : (fun x => φ ((R⁻¹ : ℂ) * x)) = φ ∘ Homeomorph.mulLeft₀ _ hRc := rfl
  rw [hfun]
  exact hcs.comp_homeomorph _

/-- **The decoded rescaled field is a quantum cone.** For a `γ`-quantum cone `(hC, hcirc)`, `b > 0`, a measurable
version `c` of the rescaled circle average process, and a family `D` of measurable pairing decoders of the cone,
`(ω ↦ (φ ↦ D φ (circleProcess (c ω))), c)` is a `γ`-quantum cone. -/
theorem isQuantumCone_decoded (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [hP : IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ} (hb : 0 < b)
    {c : Ω → ℝ → ℂ → ℝ} (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hc : ∀ᵐ ω ∂P, c ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)
    (D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hD : ∀ φ : ℂ → ℝ, IsTestFunction univ φ → Measurable (D φ) ∧
      (fun ω => D φ (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ)) :
    IsQuantumCone γ P (fun ω φ => D φ (circleProcess (c ω))) c := by
  have hpos := MatedCRT.Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hcone hb
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
    exact MatedCRT.LQGMeasure.continuousOn_rescaledCircle γ b _ hpω hω
  have hlatc := coneLateralTransferStep_proved240 hscale γ hγ hγ2 Ω P hC hcirc hP hcone b hb c D hcm hc hD
  have hpair_h : AEMeasurable (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hcirc_h.aemeasurable.prodMk (MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hcone)
  have hlath_ae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hcone
  have hlatc_ae : AEMeasurable (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) P :=
    MatedCRT.CirclePairing.aemeasurable_lateralProcess (hC := fun ω φ => D φ (circleProcess (c ω)))
      (hcirc := c) (fun φ hφ => (hD φ hφ).1.comp hcirc_c) hcm hcont
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
  refine ⟨fun φ hφ => (hD φ hφ).1.comp hcirc_c, hcm, hcont, ?_, hindep_c, ?_⟩
  · obtain ⟨ν, hν, hνmap⟩ := hcone.radial_law
    exact ⟨ν, hν, hradc.trans hνmap⟩
  · obtain ⟨Ω', i', P', hC'', hcirc'', hP', hW, hL⟩ := hcone.lateral_law
    exact ⟨Ω', i', P', hC'', hcirc'', hP', hW, hlat_law.trans hL⟩

/-- **The circle smear limit is a pairing decoder of the cone**, on the event where the circle smears converge to the
pairings for all test functions. -/
theorem circleSmearLimit_decodes {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc)
    (hL : ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, IsTestFunction univ φ →
      Tendsto (fun ε => ∫ z, φ z * hcirc ω ε z) (𝓝[>] 0) (𝓝 (hC ω φ)))
    (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    Measurable (circleSmearLimit φ) ∧
      (fun ω => circleSmearLimit φ (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ) := by
  refine ⟨measurable_circleSmearLimit φ, ?_⟩
  filter_upwards [hL, hcone.ae_continuousOn_circle] with ω hω hcω
  exact circleSmearLimit_circleProcess_eq_of_tendsto hφ.1.continuous hφ.2.1 hcω (hω φ hφ)

/-- **The rescaled cone field from the circle smears** (clauses 1-4 of `RescaledConeFieldStep`). Assume that a.s.
`(h, φ) = lim_{ε → 0+} ∫ φ(z) h_ε(z) dz` for all test functions `φ` at once. For `b > 0` and a measurable version `c`
of the circle average process of `h^b`, the circle smear limits `hC' ω φ := Λ_φ(c ω)` satisfy: a.s. for all test
functions `φ`, `hC' ω φ = (h^b, φ)`; each `hC' · φ` is measurable; and `(hC', c)` is a `γ`-quantum cone. -/
theorem rescaledConeField_of_circleSmear (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc)
    (hL : ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, IsTestFunction univ φ →
      Tendsto (fun ε => ∫ z, φ z * hcirc ω ε z) (𝓝[>] 0) (𝓝 (hC ω φ)))
    {b : ℝ} (hb : 0 < b) {c : Ω → ℝ → ℂ → ℝ} (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hc : ∀ᵐ ω ∂P, c ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) :
    (∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, IsTestFunction univ φ →
      circleSmearLimit φ (circleProcess (c ω)) =
        rescaledPairing γ (hC ω) (coneScaleRadius γ (hcirc ω) b) b φ) ∧
    (∀ φ : ℂ → ℝ, IsTestFunction univ φ → Measurable fun ω => circleSmearLimit φ (circleProcess (c ω))) ∧
    IsQuantumCone γ P (fun ω φ => circleSmearLimit φ (circleProcess (c ω))) c := by
  have hpos := MatedCRT.Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hcone hb
  refine ⟨?_, fun φ _ => (measurable_circleSmearLimit φ).comp (measurable_circleProcess_of hcm),
    isQuantumCone_decoded hscale hγ hγ2 hcone hb hcm hc (fun φ => circleSmearLimit φ)
      (circleSmearLimit_decodes hcone hL)⟩
  filter_upwards [hL, hcone.ae_continuousOn_circle, hc, hpos] with ω hω hcω hcω' hpω φ hφ
  set R := coneScaleRadius γ (hcirc ω) b
  have hφR := isTestFunction_univ_comp_inv_mul hpω.ne' hφ
  have hlim := tendsto_integral_mul_rescaledCircle (γ := γ) (b := b) hpω hφ.1.continuous hφ.2.1 hcω
    (hω _ hφR)
  rw [hcω']
  exact circleSmearLimit_circleProcess_eq_of_tendsto hφ.1.continuous hφ.2.1
    (MatedCRT.LQGMeasure.continuousOn_rescaledCircle γ b _ hpω hcω) hlim

end MatedCRT.FirstPass.Derived
