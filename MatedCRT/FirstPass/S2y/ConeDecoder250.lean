import MatedCRT.FirstPass.S2y.ConeDecoder240
import MatedCRT.FirstPass.S2y.ConeCircleDecoder
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# The pairing decoder of a quantum cone without H2 and M (fp-S2y-decoder-250, z8; chat 250)

Chat 250 (`notes/fp-gaps/CHATGPT-250-idla-z8-decoder-H1-H2-M-PRO.md`, §5) replaces the decoder of
`S2y/ConeDecoder240.lean` by the approximant

* `conePairingApprox φ n = lateralPairingApprox φ n + radialPairingCode φ` on the circle process,

where `lateralPairingApprox φ n` is the limit superior of the midpoint Riemann sums of
`z ↦ φ(z) L_ε(z)` at the radius `ε = pairingRadius n`, and `L_ε(z) = h_ε(z) - av_{∂B_ε(z)} h_{|x|}(0)` is the
lateral circle observable. The radial part enters through the Borel radial code `radialPairingCode`, which equals
`∫ φ(x) h_{|x|}(0) dx` almost surely (`radialPairingCode_ae_eq`, `S2y/ConeRadialCodes.lean`). Consequently:

* H2 (radial Riemann sums) is not used: the radial part is never approximated by Riemann sums;
* M (measurability of the radial parametric integrals) is not used: the radial circle average inside the lateral
  code is taken of the jointly measurable version `CirclePairing.radialVersion` (`Proofs/Measurability/ConePairing.lean`),
  which agrees with `h_{|x|}(0)` on the continuity event (Duplantier-Sheffield, arXiv:1409.7055, Section 3.1;
  Armitage-Gardiner, circle averages).

The one remaining analytic input is the lateral smear limit `ConeLateralSmearStep250` (H1, chat 250 §1), stated in the
form of `quantumCone_lateralSmear_tendstoInMeasure`. It is a named hypothesis of the reduction below, not proved here.
`ConeDecoder240.lean` is unchanged.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped Real ENNReal

namespace MatedCRT.LQGMeasure

/-- The circle process `q` read as a function of the radius and the centre; the value at a non-positive radius is `0`. -/
noncomputable def coneCircleFun (q : ConeCircleCode) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then q (⟨r, h⟩, z) else 0

lemma measurable_coneCircleFun (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Measurable fun q : ConeCircleCode => coneCircleFun q r z := by
  have hfun : (fun q : ConeCircleCode => coneCircleFun q r z) = fun q => q (⟨r, hr⟩, z) := by
    funext q
    simp [coneCircleFun, hr]
  rw [hfun]
  exact measurable_pi_apply _

/-- The lateral circle family of a circle process `q`: at `p = (r, z)`, `q(r, z)` minus the circle average over
`∂B_r(z)` of the jointly measurable radial version `x ↦ s_{|x|}(0)` (`CirclePairing.radialVersion`). -/
noncomputable def lateralCircleFamily (q : ConeCircleCode) : ConeCircleCode :=
  fun p => q p - Real.circleAverage (fun x => MatedCRT.CirclePairing.radialVersion coneCircleFun q ‖x‖) p.2 p.1.1

/-- The lateral pairing approximant at level `n`: the circle smear (`circleSmearCode`) of the lateral circle family. -/
noncomputable def lateralPairingApprox (φ : ℂ → ℝ) (n : ℕ) (q : ConeCircleCode) : ℝ :=
  pairingApprox φ n (lateralCircleFamily q)

/-- **The cone pairing approximant** (chat 250 §5, step 6): the lateral approximant plus the radial pairing code. -/
noncomputable def conePairingApprox (φ : ℂ → ℝ) (n : ℕ) (q : ConeCircleCode) : ℝ :=
  lateralPairingApprox φ n q + radialPairingCode φ q

/-! ### Measurability (no a.e. qualifier: the radial version is jointly measurable) -/

lemma measurable_radialVersion_pair :
    Measurable fun a : ConeCircleCode × ℝ => MatedCRT.CirclePairing.radialVersion coneCircleFun a.1 a.2 :=
  MatedCRT.CirclePairing.measurable_radialVersion fun r z hr => measurable_coneCircleFun r hr z

/-- The circle average over `∂B_R(c)` of the radial version is a Borel function of the circle process. -/
lemma measurable_circleAverage_radialVersion (c : ℂ) (R : ℝ) :
    Measurable fun q : ConeCircleCode =>
      Real.circleAverage (fun x => MatedCRT.CirclePairing.radialVersion coneCircleFun q ‖x‖) c R := by
  have hpair : Measurable fun p : ConeCircleCode × ℝ => (p.1, ‖circleMap c R p.2‖) :=
    measurable_fst.prodMk ((continuous_circleMap c R).norm.measurable.comp measurable_snd)
  have hF : Measurable fun p : ConeCircleCode × ℝ =>
      MatedCRT.CirclePairing.radialVersion coneCircleFun p.1 ‖circleMap c R p.2‖ :=
    Measurable.comp (g := fun a : ConeCircleCode × ℝ => MatedCRT.CirclePairing.radialVersion coneCircleFun a.1 a.2)
      (f := fun p : ConeCircleCode × ℝ => (p.1, ‖circleMap c R p.2‖)) measurable_radialVersion_pair hpair
  have hS : Measurable fun q : ConeCircleCode =>
      ∫ θ in Ioc (0 : ℝ) (2 * π),
        MatedCRT.CirclePairing.radialVersion coneCircleFun q ‖circleMap c R θ‖ :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))).measurable
  simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  exact measurable_const.mul hS

lemma measurable_lateralCircleFamily : Measurable lateralCircleFamily := by
  refine Measurable.of_eval fun p => ?_
  exact (measurable_pi_apply p).sub (measurable_circleAverage_radialVersion p.2 p.1.1)

/-- The lateral pairing approximants are Borel functions of the circle process. -/
theorem measurable_lateralPairingApprox (φ : ℂ → ℝ) (n : ℕ) : Measurable (lateralPairingApprox φ n) :=
  (measurable_pairingApprox φ n).comp measurable_lateralCircleFamily

/-- **The cone pairing approximants are Borel functions of the circle process** (no H2, no M). -/
theorem measurable_conePairingApprox (φ : ℂ → ℝ) (n : ℕ) : Measurable (conePairingApprox φ n) :=
  (measurable_lateralPairingApprox φ n).add (measurable_radialPairingCode φ)

/-! ### Almost sure identification of the lateral code -/

/-- On a sample whose circle average process is continuous on `(0, ∞) × ℂ`, the lateral circle family of the
circle process is the lateral circle observable `lateralEval (.circle ·)`, at every `(r, z)` with `r > 0`
(Armitage-Gardiner: the circle average over a sphere ignores a single point). -/
lemma lateralCircleFamily_circleProcess_eq {hcirc : ℝ → ℂ → ℝ} {hC : (ℂ → ℝ) → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    (p : Set.Ioi (0 : ℝ) × ℂ) :
    lateralCircleFamily (circleProcess hcirc) p = lateralEval hC hcirc (.circle p.1.1 p.2) := by
  have hs0 : ContinuousOn (fun s : ℝ => hcirc s 0) (Ioi 0) :=
    hcont.comp (f := fun s : ℝ => (s, (0 : ℂ))) (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have hcoe : ContinuousOn (fun s : ℝ => coneCircleFun (circleProcess hcirc) s 0) (Ioi 0) :=
    hs0.congr fun s hs => by simp [coneCircleFun, circleProcess, show (0 : ℝ) < s from hs]
  have hrv : ∀ s : ℝ, 0 < s →
      MatedCRT.CirclePairing.radialVersion coneCircleFun (circleProcess hcirc) s = hcirc s 0 := by
    intro s hs
    rw [MatedCRT.CirclePairing.radialVersion_eq hcoe hs]
    simp [coneCircleFun, circleProcess, hs]
  have hR : (p.1.1 : ℝ) ≠ 0 := ne_of_gt p.1.2
  have hagree : (fun x : ℂ => MatedCRT.CirclePairing.radialVersion coneCircleFun (circleProcess hcirc) ‖x‖) =ᶠ[
      codiscreteWithin (sphere p.2 |p.1.1|)] fun x => hcirc ‖x‖ 0 := by
    refine MatedCRT.CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ 0 fun y hy => ?_
    exact hrv ‖y‖ (norm_pos_iff.mpr hy)
  unfold lateralCircleFamily lateralEval
  have hav := Real.circleAverage_congr_codiscreteWithin hagree (by simpa using hR)
  simp only [circleProcess]
  rw [hav]

/-- Almost surely, the lateral pairing approximant is the circle smear of the lateral circle observables. -/
lemma ae_lateralPairingApprox_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (φ : ℂ → ℝ) (n : ℕ) :
    (fun ω => lateralPairingApprox φ n (circleProcess (hcirc ω))) =ᵐ[P]
      (fun ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
        (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2))) := by
  filter_upwards [hcont] with ω hω
  have key : ∀ p : Set.Ioi (0 : ℝ) × ℂ, lateralCircleFamily (circleProcess (hcirc ω)) p =
      lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2) :=
    fun p => lateralCircleFamily_circleProcess_eq hω p
  unfold lateralPairingApprox pairingApprox circleSmearCode
  simp only [key]

lemma measurable_circleProcess_comp {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable fun ω => circleProcess (hcirc ω) := by
  refine Measurable.of_eval fun p => ?_
  exact hmc p.1.1 p.2 p.1.2

/-- **The lateral smear input H1** (chat 250 §1, `quantumCone_lateralSmear_tendstoInMeasure`): for a quantum cone and a
test function `φ`, the circle smears at radius `pairingRadius n` of the lateral circle observables converge in probability
to the lateral pairing `lateralEval (.pairing φ)`. A named hypothesis of the reduction below; not proved in this file. -/
def ConeLateralSmearStep250 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
    ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      TendstoInMeasure P
        (fun n ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
          (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)))
        atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ))

/-- **The cone pairing approximants converge in probability** (chat 250 §5, Stage E), from the lateral smear input H1
and the a.s. radial identity `radialPairingCode_ae_eq`. No H2 and no M. -/
theorem quantumCone_conePairingApprox_tendstoInMeasure250 (H1 : ConeLateralSmearStep250)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsProbabilityMeasure P)
    (hQ : IsQuantumCone γ P hC hcirc) (φ : ℂ → ℝ) (hφ : IsTestFunction Set.univ φ) :
    TendstoInMeasure P (fun n ω => conePairingApprox φ n (circleProcess (hcirc ω))) atTop (fun ω => hC ω φ) := by
  have hlat : TendstoInMeasure P
      (fun n ω => circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)
        (fun p => lateralEval (hC ω) (hcirc ω) (.circle p.1.1 p.2)))
      atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ)) :=
    H1 γ hγ hγ2 Ω P hC hcirc hP hQ φ hφ
  have hlatCode : TendstoInMeasure P (fun n ω => lateralPairingApprox φ n (circleProcess (hcirc ω)))
      atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ)) :=
    TendstoInMeasure.congr_left
      (fun n => (ae_lateralPairingApprox_eq (hC := hC) hQ.ae_continuousOn_circle φ n).symm) hlat
  have hradTm : TendstoInMeasure P (fun _ ω => radialPairingCode φ (circleProcess (hcirc ω))) atTop
      (fun ω => radialPairingCode φ (circleProcess (hcirc ω))) :=
    tendstoInMeasure_of_tendsto_ae
      (fun _ => (Measurable.comp (g := radialPairingCode φ) (f := fun ω => circleProcess (hcirc ω))
        (measurable_radialPairingCode φ) (measurable_circleProcess_comp hQ.measurable_circle)).aestronglyMeasurable)
      (ae_of_all _ fun _ => tendsto_const_nhds)
  have hsum : TendstoInMeasure P
      (fun n ω => lateralPairingApprox φ n (circleProcess (hcirc ω)) +
        radialPairingCode φ (circleProcess (hcirc ω)))
      atTop (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ) +
        radialPairingCode φ (circleProcess (hcirc ω))) :=
    tendstoInMeasure_add_real hlatCode hradTm
  have hfin : (fun ω => lateralEval (hC ω) (hcirc ω) (.pairing φ) +
      radialPairingCode φ (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ) := by
    filter_upwards [radialPairingCode_ae_eq hQ.measurable_circle hQ.ae_continuousOn_circle hQ.radial_law φ hφ]
      with ω hω
    rw [hω]
    simp only [lateralEval]
    ring
  exact hsum.congr_right hfin

/-- **`ConeCircleDecoderStep` from the lateral smear input H1 alone** (chat 250 §5, Stage F; no H2, no M). -/
theorem coneCircleDecoderStep_of_lateralSmear250 (H1 : ConeLateralSmearStep250) : ConeCircleDecoderStep :=
  coneCircleDecoderStep_of_pairingApprox conePairingApprox
    (fun φ n => measurable_conePairingApprox φ n)
    (fun _ hγ hγ2 _ _ _ _ _ hP hQ φ hφ =>
      quantumCone_conePairingApprox_tendstoInMeasure250 H1 hγ hγ2 hP hQ φ hφ)

/-- **`ConeFieldScalingStep` from the lateral smear input H1 alone** (chat 250 §5, the downstream call). The lateral
transfer `coneLateralTransferStep_proved240` is unconditional. -/
theorem coneFieldScalingStep_proved250 (hscale : QuantumConeScalingInput) (H1 : ConeLateralSmearStep250) :
    ConeFieldScalingStep :=
  coneFieldScalingStep_of_decoder hscale (coneCircleDecoderStep_of_lateralSmear250 H1)
    (coneLateralTransferStep_proved240 hscale)

end MatedCRT.LQGMeasure

#print axioms MatedCRT.LQGMeasure.measurable_conePairingApprox
#print axioms MatedCRT.LQGMeasure.coneCircleDecoderStep_of_lateralSmear250
#print axioms MatedCRT.LQGMeasure.coneFieldScalingStep_proved250
