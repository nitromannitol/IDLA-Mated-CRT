import MatedCRT.FirstPass.S2y.ConeCircleDecoder
import MatedCRT.FirstPass.S2y.ConeLateral240
import MatedCRT.FirstPass.S2y.ConeApproxIdentity
import MatedCRT.FirstPass.S2y.ConeLateralTransfer
import MatedCRT.FirstPass.S2y.ConeCircInt240
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The pairing decoder of a quantum cone from the named inputs H1, H2, M (chat 240 §2 and §4; fp-S2y-decoder-assembly, z8)

`ConeCircleDecoderStep` (`S2y/ConeFieldPairing.lean`) is proved from three explicit named binders, in the
convergence-in-probability route of chat 240 §2:

* `H1` (lateral smear, chat 240 §2.1): the circle smears at radius `pairingRadius n` of the lateral observables
  `lateralEval (.circle ·)` converge in probability to the lateral pairing `lateralEval (.pairing φ)`;
* `H2` (radial Riemann convergence, chat 240 §2.3): for almost every `ω`, the Riemann sums of
  `z ↦ φ(z) · circleAverage (x ↦ h_{|x|}(0)) z ε_n` converge to their integral;
* `M` (measurability, chat 240 §2.3): the radial parts `ω ↦ ∫ φ(z) · circleAverage(a_ω)(z, ε_n) dz` are
  almost everywhere strongly measurable (joint measurability of `(ω, z, θ) ↦ h_{‖z + ε e^{iθ}‖}(0)`).

The local integrability of the radial part `a_ω(x) = h_{|x|}(0)` is proved here (`ae_measurable_locallyIntegrable_radial`,
from the Brownian bound `ae_lintegral_radial_lt_top` and polar coordinates). The approximate identity
`tendsto_integral_mul_circleAverage` (`S2y/ConeApproxIdentity.lean`) gives the a.s. convergence of the radial parts
(Duplantier-Sheffield, arXiv:1409.7055, Section 3.1; Armitage-Gardiner, circle averages). The deterministic splitting
`circleSmearCode_circleProcess_split` (`S2y/ConeLateral240.lean`) and the `limsup` extraction
`coneCircleDecoderStep_of_pairingApprox` (`S2y/ConeCircleDecoder.lean`) close the chain.

Also here: the lateral transfer `ConeLateralTransferStep` with the sphere-average input proved unconditionally
(`radialSphereCode_ae_eq`, `S2y/ConeCircInt240.lean`), and `ConeFieldScalingStep` without `hpair` and without
`hcircInt`.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped Real ENNReal

namespace MatedCRT.LQGMeasure

/-- A function `G` continuous on `(0, ∞)` gives a measurable radial function `x ↦ G ‖x‖` on `ℂ`. -/
lemma measurable_comp_norm_of_continuousOn {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Ioi 0)) :
    Measurable (fun x : ℂ => G ‖x‖) := by
  classical
  have hm : Measurable ((Set.Ioi (0 : ℝ)).piecewise G (fun _ => G 0)) :=
    ContinuousOn.measurable_piecewise hG continuousOn_const measurableSet_Ioi
  have hEq : (fun x : ℂ => G ‖x‖) = fun x : ℂ => (Set.Ioi (0 : ℝ)).piecewise G (fun _ => G 0) ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · simp [hx, Set.piecewise]
    · have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      simp [Set.piecewise, hpos]
  rw [hEq]
  exact hm.comp measurable_norm

/-- **Local integrability of a radial function on `ℂ` (polar coordinates).** If `G` is continuous on `(0, ∞)` and
`∫_{(0,1]} y |G y| dy < ∞`, then `x ↦ G ‖x‖` is locally integrable on `ℂ`. Compact sets lie in a ball `B(0, R0)`,
`R0 ≥ 1`, where `integrableOn_Ioc_mul_abs` and `integrable_radial_indicator` (`S2y/ConeRadialCodes.lean`) apply. -/
lemma locallyIntegrable_comp_norm_of_lintegral {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Ioi 0))
    (hfin : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |G y|) < ⊤) :
    LocallyIntegrable (fun x : ℂ => G ‖x‖) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR0 : 1 ≤ max R 1 := le_max_right _ _
  have hF := integrable_radial_indicator (R0 := max R 1) (integrableOn_Ioc_mul_abs hG hR0 hfin)
  refine Integrable.mono' hF.integrableOn (measurable_comp_norm_of_continuousOn hG).aestronglyMeasurable ?_
  refine (ae_restrict_mem hK.isClosed.measurableSet).mono fun x hx => ?_
  have hxR : ‖x‖ ≤ max R 1 := le_trans (mem_closedBall_zero_iff.mp (hR hx)) (le_max_left _ _)
  rw [Set.indicator_of_mem (Set.mem_Iic.mpr hxR)]
  exact (Real.norm_eq_abs _).le

/-- **H3 (a.s. regularity of the radial part).** For a quantum cone, almost surely the radial part
`x ↦ h_{|x|}(0)` of the circle average process is measurable and locally integrable on `ℂ`. The Brownian input is
`ae_lintegral_radial_lt_top` (`S2y/ConeRadialCodes.lean`): `∫_{[0,∞)} e^{-2t} |h_{e^{-t}}(0)| dt < ∞` a.s. -/
theorem ae_measurable_locallyIntegrable_radial {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Measurable (fun x : ℂ => hcirc ω ‖x‖ 0) ∧
      LocallyIntegrable (fun x : ℂ => hcirc ω ‖x‖ 0) volume := by
  obtain ⟨T, hT, hPT, hgood⟩ := MatedCRT.exists_measurable_good_set hQ.ae_continuousOn_circle
  obtain ⟨ν, hν, hrad⟩ := hQ.radial_law
  have hlint := MatedCRT.ae_lintegral_radial_lt_top hQ.measurable_circle hν.1 hrad hT hPT hgood
  have hTae : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    exact hPT
  filter_upwards [hlint, hTae] with ω hω hωT
  have hcg := hgood ω hωT
  have hG : ContinuousOn (fun y : ℝ => hcirc ω y 0) (Set.Ioi 0) :=
    hcg.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy, Set.mem_univ _⟩)
  simp only [Set.indicator_of_mem hωT] at hω
  have hfin : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |hcirc ω y 0|) < ⊤ := by
    rw [lintegral_Ioc_eq_radial (fun y => hcirc ω y 0)]
    exact hω
  exact ⟨measurable_comp_norm_of_continuousOn hG, locallyIntegrable_comp_norm_of_lintegral hG hfin⟩

/-- Convergence in probability is stable under sums of real-valued sequences (Mathlib of this version has no
`TendstoInMeasure.add`). Only the measures of the two error events are compared; no measurability is needed. -/
lemma tendstoInMeasure_add_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} {l : Filter ι}
    {f g : ι → Ω → ℝ} {f' g' : Ω → ℝ} (hf : TendstoInMeasure P f l f') (hg : TendstoInMeasure P g l g') :
    TendstoInMeasure P (fun i ω => f i ω + g i ω) l (fun ω => f' ω + g' ω) := by
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hsum := (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun i => zero_le) (fun i => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  change ε ≤ edist (f i x + g i x) (f' x + g' x) at hx
  rcases le_or_gt (ε / 2) (edist (f i x) (f' x)) with h1 | h1
  · exact Or.inl h1
  rcases le_or_gt (ε / 2) (edist (g i x) (g' x)) with h2 | h2
  · exact Or.inr h2
  exfalso
  have hlt : edist (f i x + g i x) (f' x + g' x) < ε := calc
    edist (f i x + g i x) (f' x + g' x) ≤ edist (f i x) (f' x) + edist (g i x) (g' x) :=
      edist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add h1 h2
    _ = ε := ENNReal.add_halves ε
  exact absurd hx (not_le.mpr hlt)

/-- **Pairing convergence from H1, H2, M (chat 240 §2).** Named binders:
* `H1` (lateral smear in probability, chat 240 §2.1), for every quantum cone and every test function;
* `H2` (a.s. Riemann convergence of the radial circle smear, chat 240 §2.3), for every `n`;
* `M` (a.e. strong measurability in `ω` of the radial parts at each level `n`).
Conclusion: the circle-smear approximants of `hC · φ` converge in probability to `hC · φ`, for every quantum cone. -/
theorem quantumCone_pairingApprox_tendstoInMeasure_of_H1_H2_M
    (H1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        TendstoInMeasure P
          (fun n ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
            (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)))
          atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ)))
    (H2 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        ∀ᵐ ω ∂P, Tendsto
          (fun k => planeQuad k (fun z => φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)))
          atTop (𝓝 (∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n))))
    (M : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        AEStronglyMeasurable (fun ω => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)) P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsProbabilityMeasure P)
    (hQ : IsQuantumCone γ P hC hcirc) (φ : ℂ → ℝ) (hφ : IsTestFunction Set.univ φ) :
    TendstoInMeasure P (fun n ω => pairingApprox φ n (circleProcess (hcirc ω))) atTop (fun ω => hC ω φ) := by
  have hφc : Continuous φ := hφ.1.continuous
  have hφk : HasCompactSupport φ := hφ.2.1
  -- (1) almost surely, the circle smear splits into the lateral smear plus the radial Riemann limit.
  have hsplit : ∀ n : ℕ, ∀ᵐ ω ∂P, pairingApprox φ n (circleProcess (hcirc ω)) =
      circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
        (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)) +
      ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n) := by
    intro n
    filter_upwards [H2 γ hγ hγ2 Ω P hC hcirc hP hQ φ hφ n, hQ.ae_continuousOn_circle] with ω hY hω
    have hcontz : Continuous fun z => hcirc ω (pairingRadius n) z := by
      have h1 : ContinuousOn (fun z : ℂ => (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (pairingRadius n, z)) univ :=
        hω.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun z _ => ⟨pairingRadius_pos n, Set.mem_univ z⟩)
      exact continuousOn_univ.mp h1
    exact circleSmearCode_circleProcess_split φ hφc hφk (pairingRadius_pos n) (hC ω) (hcirc ω) hcontz hY
  -- (2) almost surely, the radial circle smears converge to the radial pairing (approximate identity).
  have hR_lim : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)) atTop
      (𝓝 (∫ x, φ x * hcirc ω ‖x‖ 0)) := by
    filter_upwards [ae_measurable_locallyIntegrable_radial hQ] with ω hω
    have hε : Tendsto pairingRadius atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨pairingRadius_tendsto, Eventually.of_forall pairingRadius_pos⟩
    exact (tendsto_integral_mul_circleAverage hω.1 hω.2 hφc hφk).comp hε
  -- (3) convergence in probability of the radial circle smears (M gives the measurability).
  have hR_tm : TendstoInMeasure P
      (fun n ω => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)) atTop
      (fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0) :=
    tendstoInMeasure_of_tendsto_ae
      (f := fun n ω => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n))
      (g := fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0)
      (fun n => M γ hγ hγ2 Ω P hC hcirc hP hQ φ hφ n) hR_lim
  -- (4) lateral smear (H1) plus radial part (3).
  have hsum := tendstoInMeasure_add_real (H1 γ hγ hγ2 Ω P hC hcirc hP hQ φ hφ) hR_tm
  -- (5) transfer along the a.s. identities of (1) and of the lateral decomposition hC φ = L(φ) + ∫ φ a.
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => EventuallyEq.symm (hsplit n)) ?_ hsum
  exact ae_of_all P fun ω => by simp only [lateralEval]; ring

/-- **`ConeCircleDecoderStep` from H1, H2, M** (chat 240 §2, `coneCircleDecoderStep_proved` of §4 with the three
named inputs as binders). The decoder is the `limsup` extraction of `coneCircleDecoderStep_of_pairingApprox`. -/
theorem coneCircleDecoderStep_of_H1_H2_M
    (H1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        TendstoInMeasure P
          (fun n ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
            (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)))
          atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ)))
    (H2 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        ∀ᵐ ω ∂P, Tendsto
          (fun k => planeQuad k (fun z => φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)))
          atTop (𝓝 (∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n))))
    (M : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        AEStronglyMeasurable (fun ω => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)) P) :
    ConeCircleDecoderStep :=
  coneCircleDecoderStep_of_pairingApprox (fun φ n => pairingApprox φ n)
    (fun φ n => measurable_pairingApprox φ n)
    (fun _ hγ hγ2 _ _ _ _ _ hP hQ φ hφ =>
      quantumCone_pairingApprox_tendstoInMeasure_of_H1_H2_M H1 H2 M hγ hγ2 hP hQ φ hφ)

/-- **`ConeLateralTransferStep` with no sphere-integrability binder** (chat 240 §3–§4). The radial pairing code and the
radial sphere code are concrete (`radialPairingCode_ae_eq`, and the unconditional `radialSphereCode_ae_eq` of
`S2y/ConeCircInt240.lean`). -/
theorem coneLateralTransferStep_proved240 (hscale : QuantumConeScalingInput) : ConeLateralTransferStep :=
  coneLateralTransferStep_of_radialCodes hscale radialPairingCode radialSphereCode
    measurable_radialPairingCode measurable_radialSphereCode
    (fun _ _ _ _ _ hcm hcont hrad φ hφ => radialPairingCode_ae_eq hcm hcont hrad φ hφ)
    (fun _ _ _ _ _ hcm hcont hrad _ z hr => radialSphereCode_ae_eq hcm hcont hrad hr z)

/-- **`ConeFieldScalingStep` without `hpair`, from H1, H2, M** (chat 240 §4, `coneFieldScalingStep_proved_no_hpair`
with the named binders). The inputs: the scaling input `hscale` and the three named inputs H1, H2, M of
`coneCircleDecoderStep_of_H1_H2_M`. -/
theorem coneFieldScalingStep_proved240 (hscale : QuantumConeScalingInput)
    (H1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        TendstoInMeasure P
          (fun n ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
            (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)))
          atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ)))
    (H2 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        ∀ᵐ ω ∂P, Tendsto
          (fun k => planeQuad k (fun z => φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)))
          atTop (𝓝 (∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n))))
    (M : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ n : ℕ,
        AEStronglyMeasurable (fun ω => ∫ z, φ z * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z (pairingRadius n)) P) :
    ConeFieldScalingStep :=
  coneFieldScalingStep_of_decoder hscale (coneCircleDecoderStep_of_H1_H2_M H1 H2 M)
    (coneLateralTransferStep_proved240 hscale)

end MatedCRT.LQGMeasure
