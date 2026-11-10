import MatedCRT.FirstPass.S2y.ConeDecoder250
import MatedCRT.FirstPass.S2y.CircleSmearId250
import MatedCRT.FirstPass.S2y.CircleAvgRadialCont250
import MatedCRT.FirstPass.S2y.LateralL1Limit250
import MatedCRT.FirstPass.S2y.LateralL2Limit250
import MatedCRT.FirstPass.S2y.LateralInMeasure250
import MatedCRT.FirstPass.S2y.LateralBilin250
import MatedCRT.FirstPass.S2y.ConeApproxIdentity
import MatedCRT.FirstPass.S2y.ConeRadialCodes

/-!
# FIRST PASS S2y, LateralAssembly250: the whole-plane lateral smear H1 (fp-S2y-decoder-250, z8; chat 250 §1.4, S4)

Assembly of `WholePlaneLateralSmear250` (`ConeDecoder250`) from the pieces proved in the S2y files.

* Pathwise (`lateralSmearOf_eq_pathwise`): on a sample whose circle process and radial version are continuous and whose
  `|radialVersion|^4` is locally integrable, the lateral circle smear at radius `ε ∈ (0,1]` equals
  `hC(ψ_ε) - ∫ ψ_ε(y) h_{|y|}(0) dy`, with `ψ_ε = circleKernel φ ε`. It uses the Riemann-sum limit
  (`planeQuad_tendsto_integral`), the a.s. circle smear identity (`circleSmear_ae_eq`, file CircleSmearId250) and the
  deterministic adjoint `integral_mul_circleAverage_eq`.
* Probabilistic (`wholePlaneLateralSmear250_of_radial`): the L² part (`tendsto_integral_sq_pairing_sub`), the L¹ part of
  the radial integral (`tendsto_integral_abs_radial`), and the passage to convergence in probability.

Named radial inputs (chat 250 §1.3, R5), used as hypotheses until their files land:
`RadialContAe250` (owner z9, `RadialProcCont250.ae_continuousOn_radialVersion`) and `RadialL4Ae250` (owner q2,
`RadialProcL4Ae250.ae_integrableOn_radialVersion_pow_four`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped Real ENNReal

set_option linter.unusedSectionVars false

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Named radial inputs (R5) -/

/-- **Radial continuity input** (chat 250 §1.3, R5a; owner z9, `RadialProcCont250.ae_continuousOn_radialVersion`): for every
whole-plane GFF, almost surely the radial version is continuous on `(0, ∞)`. A named hypothesis until that file lands. -/
def RadialContAe250 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    ∀ᵐ ω ∂P, ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Ioi 0)

/-- **Radial fourth-moment input** (chat 250 §1.3, R5b; owner q2, `RadialProcL4Ae250.ae_integrableOn_radialVersion_pow_four`):
for every whole-plane GFF, almost surely `|radialVersion|^4` is integrable on every `(0, n]`. A named hypothesis until that
file lands. -/
def RadialL4Ae250 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    ∀ᵐ ω ∂P, ∀ n : ℕ, IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ))

/-! ### Pathwise facts about the radial version -/

lemma radialVersion_eq_of_cont {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {s : ℝ} (hs : 0 < s) :
    MatedCRT.CirclePairing.radialVersion hcirc ω s = hcirc ω s 0 :=
  MatedCRT.CirclePairing.radialVersion_eq (MatedCRT.CirclePairing.continuousOn_radial hω) hs

/-- The circle average of the radial version is the circle average of `x ↦ h_{|x|}(0)` (they agree off the centre). -/
lemma circleAverage_radialVersion_eq {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε =
      Real.circleAverage (fun x : ℂ => hcirc ω ‖x‖ 0) z ε := by
  have hagree : (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) =ᶠ[codiscreteWithin (sphere z |ε|)]
      fun x : ℂ => hcirc ω ‖x‖ 0 := by
    refine MatedCRT.CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ 0 fun y hy => ?_
    exact radialVersion_eq_of_cont hω (norm_pos_iff.mpr hy)
  exact Real.circleAverage_congr_codiscreteWithin hagree hε.ne'

/-- Joint measurability of `(ω, s) ↦ radialVersion hcirc ω s` (lambda form, to keep unification cheap). -/
lemma measurable_radialVersion_joint {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    Measurable (fun q : Ω × ℝ => MatedCRT.CirclePairing.radialVersion hcirc q.1 q.2) := by
  have h0 := MatedCRT.CirclePairing.measurable_radialVersion h.measurable_circle
  rw [Function.uncurry_def] at h0
  exact h0

/-- Joint measurability gives measurability of each radial version. -/
lemma measurable_radialVersion_slice {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ω : Ω) :
    Measurable (fun s : ℝ => MatedCRT.CirclePairing.radialVersion hcirc ω s) := by
  have hpair : Measurable (fun s : ℝ => (ω, s)) := measurable_const.prodMk measurable_id
  have key := (measurable_radialVersion_joint h).comp hpair
  simp only [Function.comp_def] at key
  exact key

/-- Pathwise continuity of `z ↦ circleAverage(|radialVersion|)(z, ε)` (chat 250 §1.3; the analysis part is
`continuous_circleAverage_radial_of_memLp`, file CircleAvgRadialCont250). -/
lemma continuous_circleAverage_radialVersion {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hA : ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Ioi 0))
    (hB : ∀ n : ℕ, IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun z : ℂ =>
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε) := by
  refine continuous_iff_continuousAt.2 fun z0 => ?_
  have hL : IntegrableOn (fun r => |MatedCRT.CirclePairing.radialVersion hcirc ω r| ^ (4 : ℝ))
      (Ioc 0 (‖z0‖ + ε + 1)) := by
    refine ((hB ⌈‖z0‖ + ε + 1⌉₊).mono_set (Ioc_subset_Ioc_right (Nat.le_ceil _))).congr_fun (fun r _ => ?_)
      measurableSet_Ioc
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hc := continuous_circleAverage_radial_of_memLp (a := MatedCRT.CirclePairing.radialVersion hcirc ω)
    (ε := ε) (R := ‖z0‖ + ε + 1) hε (by norm_num) hA hL
  have hz0 : z0 ∈ Metric.ball (0 : ℂ) (‖z0‖ + ε + 1 - ε) := by
    rw [mem_ball_zero_iff]
    linarith
  exact hc.continuousAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz0) Metric.ball_subset_closedBall)

/-! ### Integrability of radial functions (pathwise) -/

lemma abs_le_one_add_pow_four (t : ℝ) : |t| ≤ 1 + |t| ^ 4 := by
  have hs : 0 ≤ |t| := abs_nonneg t
  nlinarith [sq_nonneg (|t| ^ 2 - 1 / 2), sq_nonneg (|t| - 1 / 2)]

/-- `y ↦ y |a(y)|` is integrable on `(0, R]` when `|a|⁴` is integrable on every `(0, n]` (`|a| ≤ 1 + |a|⁴`). -/
lemma integrableOn_mul_abs_of_fourth {a : ℝ → ℝ} (ha : Measurable a)
    (hB : ∀ n : ℕ, IntegrableOn (fun s => |a s| ^ 4) (Ioc 0 (n : ℝ))) (R : ℝ) :
    IntegrableOn (fun y => y * |a y|) (Ioc 0 R) := by
  have h4 : IntegrableOn (fun s => |a s| ^ 4) (Ioc 0 R) :=
    (hB ⌈R⌉₊).mono_set (Ioc_subset_Ioc_right (Nat.le_ceil R))
  have h1 : IntegrableOn (fun s => 1 + |a s| ^ 4) (Ioc 0 R) :=
    (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).add h4
  have hA1 : IntegrableOn (fun s => |a s|) (Ioc 0 R) :=
    Integrable.mono' h1 (continuous_abs.measurable.comp ha).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_le_one_add_pow_four (a s))
  refine Integrable.mono' (hA1.const_mul |R|)
    (measurable_id.mul (continuous_abs.measurable.comp ha)).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun y hy => ?_
  have hy0 : 0 ≤ y * |a y| := mul_nonneg hy.1.le (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hy0]
  exact mul_le_mul_of_nonneg_right (hy.2.trans (le_abs_self R)) (abs_nonneg _)

/-- The radial function `x ↦ a(|x|)` is locally integrable on `ℂ` when `|a|⁴` is locally integrable on `(0, ∞)`
(polar coordinates: `integrable_radial_indicator`, which rests on `integrable_fun_norm_addHaar`). -/
lemma locallyIntegrable_radial_fourth {a : ℝ → ℝ} (ha : Measurable a)
    (hB : ∀ n : ℕ, IntegrableOn (fun s => |a s| ^ 4) (Ioc 0 (n : ℝ))) :
    LocallyIntegrable (fun x : ℂ => a ‖x‖) volume := by
  intro x
  have hR0 : (0 : ℝ) ≤ ‖x‖ + 1 := by positivity
  refine ⟨closedBall (0 : ℂ) (‖x‖ + 1), ?_, ?_⟩
  · refine Filter.mem_of_superset (Metric.ball_mem_nhds x one_pos) fun y hy => ?_
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall_zero_iff]
    have h1 := norm_sub_norm_le y x
    have h2 := norm_sub_rev y x
    linarith
  · have hI := integrable_radial_indicator (g := a) (R0 := ‖x‖ + 1)
      (integrableOn_mul_abs_of_fourth ha hB (‖x‖ + 1))
    refine Integrable.mono' hI.integrableOn (ha.comp measurable_norm).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_closedBall).mono fun y hy => ?_
    have hmem : ‖y‖ ∈ Iic (‖x‖ + 1) := mem_closedBall_zero_iff.1 hy
    simp [Real.norm_eq_abs, Set.indicator_of_mem hmem]

/-- Multiplying a locally integrable radial function by a continuous compactly supported function is integrable. -/
lemma integrable_mul_radial {a : ℂ → ℝ} (hloc : LocallyIntegrable a volume) {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => g x * a x) volume := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hK : IntegrableOn (fun x => g x * a x) (closedBall (0 : ℂ) R) := by
    have h1 := (hloc.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) R)).mul_continuousOn
      hg.continuousOn (isCompact_closedBall (0 : ℂ) R)
    exact h1.congr_fun (fun x _ => mul_comm _ _) measurableSet_closedBall
  have hsupp : Function.support (fun x => g x * a x) ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    have hgx : g x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.1 hx)
    exact hR (subset_tsupport g (Function.mem_support.2 hgx))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hK

/-! ### The radial integral: integrability in `ω` (copy of the integrability step of `tendsto_integral_abs_radial_gen`) -/

/-- The random variable `ω ↦ ∫ g(y) A(ω, y) dy` is integrable for a jointly measurable `A` whose slices are `L²` and
agree a.s. with the circle averages `h_r(0)` off the centre (the integrability step of `tendsto_integral_abs_radial_gen`,
with `A` abstract). -/
lemma integrable_integral_radial_gen [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {A : Ω → ℂ → ℝ} (hAm : Measurable (fun p : Ω × ℂ => A p.1 p.2))
    (hAeq : ∀ y : ℂ, y ≠ 0 → (fun ω => A ω y) =ᵐ[P] (fun ω => hcirc ω ‖y‖ 0))
    {g : ℂ → ℝ} (hgm : Measurable g) {C R : ℝ} (hC0 : 0 ≤ C)
    (hgC : ∀ y, |g y| ≤ C) (hgR : ∀ y, y ∉ closedBall (0 : ℂ) R → g y = 0) :
    Integrable (fun ω => ∫ y, g y * A ω y) P := by
  have hy0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    rw [ae_iff]; simp
  have hAL2 : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => A ω y) 2 P :=
    ae_restrict_of_ae (hy0.mono fun y hy =>
      (memLp_circle_zero h (norm_pos_iff.2 hy)).ae_eq (hAeq y hy).symm)
  have hcv : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)),
      ∫ ω, (A ω y) ^ 2 ∂P = MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖ :=
    ae_restrict_of_ae (hy0.mono fun y hy => by
      have e : (fun ω => (A ω y) ^ 2) =ᵐ[P] (fun ω => (hcirc ω ‖y‖ 0) ^ 2) :=
        (hAeq y hy).fun_comp (fun t : ℝ => t ^ 2)
      rw [integral_congr_ae e]
      exact integral_sq_circle_zero h (norm_pos_iff.2 hy))
  have hfB : IntegrableOn (fun y : ℂ => MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖)
      (closedBall (0 : ℂ) R) := by
    have hdom : IntegrableOn (fun y : ℂ => 3 * |Real.log ‖y‖|) (closedBall (0 : ℂ) R) :=
      (((integrableOn_log_norm_ball (R + 1)).mono_set (closedBall_subset_ball (by linarith))).abs).const_mul 3
    have hmeas : Measurable (fun y : ℂ => MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖) := by
      unfold MatedCRT.Field.ConeRadial.radialCov
      fun_prop
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    exact ae_restrict_of_ae (hy0.mono fun y _ => abs_radialCov_self_le ‖y‖)
  have hAint : IntegrableOn (fun y => ∫ ω, (A ω y) ^ 2 ∂P) (closedBall (0 : ℂ) R) :=
    hfB.congr_fun_ae (hcv.mono fun y hy => hy.symm)
  have hgn : Integrable (fun p : Ω × ℂ => g p.2 * A p.1 p.2) (P.prod (volume : Measure ℂ)) :=
    integrable_mul_prod_of_bdd hAm hgm hC0 hgC hgR hAL2 hAint
  exact hgn.integral_prod_left

/-- The radial integral `ω ↦ ∫ g(y) h_{|y|}(0) dy` (through the radial version) is integrable. -/
lemma integrable_integral_radial [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hgm : Measurable g) {C R : ℝ} (hC0 : 0 ≤ C)
    (hgC : ∀ y, |g y| ≤ C) (hgR : ∀ y, y ∉ closedBall (0 : ℂ) R → g y = 0) :
    Integrable (fun ω => ∫ y, g y * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖) P := by
  have hf : Measurable (fun p : Ω × ℂ => (p.1, ‖p.2‖)) := measurable_fst.prodMk measurable_snd.norm
  have hAm : Measurable (fun p : Ω × ℂ => MatedCRT.CirclePairing.radialVersion hcirc p.1 ‖p.2‖) := by
    have key := (measurable_radialVersion_joint h).comp hf
    simp only [Function.comp_def] at key
    exact key
  exact integrable_integral_radial_gen (A := fun ω y => MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖) h hAm
    (fun _ hy => radialVersion_ae_eq h (norm_pos_iff.2 hy)) hgm hC0 hgC hgR
/-! ### Pathwise identities for the lateral smear -/

/-- The lateral pairing `h(φ) - ∫ φ h_{|x|}(0)` is `hC φ - ∫ φ · radialVersion` on a sample with continuous circle process. -/
lemma lateralProcess_pairing_eq {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    lateralProcess (hC ω) (hcirc ω) ⟨GFFObservable.pairing φ, hφ⟩ =
      hC ω φ - ∫ x, φ x * MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖ := by
  have hy0 : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ 0 := by
    rw [ae_iff]; simp
  have hint : ∫ x, φ x * hcirc ω ‖x‖ 0 = ∫ x, φ x * MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖ :=
    integral_congr_ae (hy0.mono fun x hx => by
      dsimp only
      rw [radialVersion_eq_of_cont hω (norm_pos_iff.2 hx)])
  simp only [lateralProcess, lateralEval]
  rw [hint]

/-- **Pathwise lateral smear identity.** On a sample with continuous circle process, continuous radial version and
`|radialVersion|⁴` locally integrable, and for which the circle smear identity holds at radius `ε ∈ (0, 1]`, the lateral
circle smear equals `hC(ψ_ε) - ∫ ψ_ε(y) h_{|y|}(0) dy`, `ψ_ε = circleKernel φ ε`. -/
lemma lateralSmearOf_eq_pathwise {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hA : ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Ioi 0))
    (hB : ∀ n : ℕ, IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ)))
    (hm : Measurable (MatedCRT.CirclePairing.radialVersion hcirc ω))
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR3 : ∫ z, φ z * hcirc ω ε z = hC ω (circleKernel φ ε)) :
    lateralSmearOf φ ε hε (lateralProcess (hC ω) (hcirc ω)) =
      hC ω (circleKernel φ ε) - ∫ x, circleKernel φ ε x * MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖ := by
  have hcε : Continuous (fun z : ℂ => hcirc ω ε z) := by
    have h1 : ContinuousOn ((fun p : ℝ × ℂ => hcirc ω p.1 p.2) ∘ (fun z : ℂ => (ε, z))) univ :=
      hω.comp (f := fun z : ℂ => (ε, z)) (s := univ) (continuous_const.prodMk continuous_id).continuousOn
        (fun z _ => ⟨hε, mem_univ _⟩)
    exact continuousOn_univ.1 h1
  have hAc := continuous_circleAverage_radialVersion hA hB hε
  have hseq : (fun k => planeQuad k (fun z => φ z *
      (lateralProcess (hC ω) (hcirc ω) ⟨GFFObservable.circle ε z, hε⟩))) =
      fun k => planeQuad k (fun z => φ z * (hcirc ω ε z -
        Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε)) := by
    funext k
    congr 1
    funext z
    rw [circleAverage_radialVersion_eq hω z hε]
    simp only [lateralProcess, lateralEval]
  have hFc : Continuous (fun z : ℂ => φ z * (hcirc ω ε z -
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε)) :=
    hφc.mul (hcε.sub hAc)
  have hFs : HasCompactSupport (fun z : ℂ => φ z * (hcirc ω ε z -
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε)) :=
    hφs.mul_right
  have hls : limsup (fun k => planeQuad k (fun z => φ z *
      (lateralProcess (hC ω) (hcirc ω) ⟨GFFObservable.circle ε z, hε⟩))) atTop =
      ∫ z, φ z * (hcirc ω ε z -
        Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε) := by
    rw [hseq]
    exact (planeQuad_tendsto_integral hFc hFs).limsup_eq
  have hint1 : Integrable (fun z : ℂ => φ z * hcirc ω ε z) :=
    (hφc.mul hcε).integrable_of_hasCompactSupport hφs.mul_right
  have hint2 : Integrable (fun z : ℂ => φ z *
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε) :=
    (hφc.mul hAc).integrable_of_hasCompactSupport hφs.mul_right
  have hsplit : ∫ z, φ z * (hcirc ω ε z -
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε) =
      (∫ z, φ z * hcirc ω ε z) - ∫ z, φ z *
        Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext z
    ring
  have hfub := integral_mul_circleAverage_eq (a := fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖)
    (φ := φ) (hm.comp measurable_norm) (locallyIntegrable_radial_fourth hm hB) hφc hφs hε hε1
  have hlhs : lateralSmearOf φ ε hε (lateralProcess (hC ω) (hcirc ω)) = ∫ z, φ z * (hcirc ω ε z -
      Real.circleAverage (fun x : ℂ => MatedCRT.CirclePairing.radialVersion hcirc ω ‖x‖) z ε) := hls
  rw [hlhs, hsplit, hR3, hfub]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ### Kernel bounds and support -/

lemma abs_circleKernel_le {φ : ℂ → ℝ} {C : ℝ} (hφM : ∀ x, |φ x| ≤ C) (ε : ℝ) (x : ℂ) :
    |circleKernel φ ε x| ≤ C := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hint : ‖∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ)‖ ≤ C * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => by rw [Real.norm_eq_abs]; exact hφM _)
  rw [sub_zero, abs_of_pos hpi, Real.norm_eq_abs] at hint
  unfold circleKernel
  rw [abs_mul, abs_inv, abs_of_pos hpi]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ)|
      ≤ (2 * π)⁻¹ * (C * (2 * π)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C := by field_simp

/-- The circle kernel vanishes outside `closedBall 0 (R0 + 1)` when `φ` vanishes outside `closedBall 0 R0` and `ε ∈ [0,1]`. -/
lemma circleKernel_eq_zero_of_far {φ : ℂ → ℝ} {R0 : ℝ} (hφR : ∀ x, x ∉ closedBall (0 : ℂ) R0 → φ x = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : ℂ) (hx : x ∉ closedBall (0 : ℂ) (R0 + 1)) :
    circleKernel φ ε x = 0 := by
  have h0 : ∀ θ : ℝ, φ (x - circleMap 0 ε θ) = 0 := by
    intro θ
    refine hφR _ fun hh => hx ?_
    rw [mem_closedBall_zero_iff] at hh ⊢
    have h1 : ‖x‖ ≤ ‖x - circleMap 0 ε θ‖ + ‖circleMap 0 ε θ‖ := by
      have := norm_add_le (x - circleMap 0 ε θ) (circleMap 0 ε θ)
      rwa [sub_add_cancel] at this
    rw [norm_circleMap_zero_eq hε θ] at h1
    linarith
  unfold circleKernel
  simp only [h0, intervalIntegral.integral_zero, mul_zero]

/-! ### Convergence in probability -/

/-- Convergence in probability to a limit, from convergence in probability of the differences to `0`. -/
lemma tendstoInMeasure_of_sub_zero {ι : Type*} {l : Filter ι} {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoInMeasure P (fun i ω => f i ω - g ω) l (fun _ => 0)) : TendstoInMeasure P f l g := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa [Real.dist_eq] using h ε hε

/-! ### The whole-plane lateral smear from the radial inputs -/

/-- **The whole-plane lateral smear input H1** (chat 250 §1.4; `WholePlaneLateralSmear250`), proved from the two radial
inputs R5a and R5b (`RadialContAe250`, `RadialL4Ae250`). All other steps are proved here. -/
theorem wholePlaneLateralSmear250_of_radial (hA : RadialContAe250) (hB : RadialL4Ae250) :
    WholePlaneLateralSmear250 := by
  intro Ω _ P hC hcirc hP h φ hφ
  have hφc : Continuous φ := hφ.1.continuous
  have hφs : HasCompactSupport φ := hφ.2.1
  obtain ⟨R0, hR0⟩ := hφs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨C0, hC0φ⟩ := hφc.bounded_above_of_compact_support hφs
  have hφM : ∀ x, |φ x| ≤ max C0 0 := fun x => by
    have := hC0φ x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hφR0 : ∀ x, x ∉ closedBall (0 : ℂ) R0 → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hm => hx (hR0 hm)
  have hφR : ∀ x, x ∉ closedBall (0 : ℂ) (R0 + 1) → φ x = 0 := fun x hx =>
    hφR0 x fun hm => hx (closedBall_subset_closedBall (by linarith) hm)
  have hεle : ∀ n : ℕ, pairingRadius n ≤ 1 := fun n => by
    unfold pairingRadius
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hψT : ∀ n : ℕ, IsTestFunction univ (circleKernel φ (pairingRadius n)) := fun n =>
    isTestFunction_circleKernel hφ (pairingRadius_pos n).le
  have hψR : ∀ n : ℕ, ∀ x, x ∉ closedBall (0 : ℂ) (R0 + 1) → circleKernel φ (pairingRadius n) x = 0 :=
    fun n x hx => circleKernel_eq_zero_of_far hφR0 (pairingRadius_pos n).le (hεle n) x hx
  have hψM : ∀ n : ℕ, ∀ x, |circleKernel φ (pairingRadius n) x| ≤ max C0 0 := fun n x =>
    abs_circleKernel_le hφM _ x
  have hlim : ∀ x, Tendsto (fun n : ℕ => circleKernel φ (pairingRadius n) x) atTop (𝓝 (φ x)) := fun x =>
    (tendsto_circleKernel hφc hφs x).comp
      (tendsto_nhdsWithin_iff.2 ⟨pairingRadius_tendsto, Eventually.of_forall pairingRadius_pos⟩)
  have hR3 : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∫ z, φ z * hcirc ω (pairingRadius n) z = hC ω (circleKernel φ (pairingRadius n)) :=
    ae_all_iff.2 fun n => circleSmear_ae_eq h hφ (pairingRadius_pos n) (hεle n)
  -- L² part: `E (h(ψ_n) - h(φ))² → 0`, hence convergence in probability to `0`
  have hX2 := tendsto_integral_sq_pairing_sub h hψT hφ hψR hφR hψM hφM hlim
  have hXm : TendstoInMeasure P (fun n ω => hC ω (circleKernel φ (pairingRadius n)) - hC ω φ) atTop
      (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq
      (Y := fun n ω => hC ω (circleKernel φ (pairingRadius n)) - hC ω φ)
      (fun n => ((memLp_pairing h (hψT n)).sub (memLp_pairing h hφ)).integrable_sq) hX2
  -- L¹ part of the radial integral
  have hgM : ∀ n : ℕ, ∀ y, |φ y - circleKernel φ (pairingRadius n) y| ≤ 2 * max C0 0 := fun n y => by
    have h1 := abs_sub (φ y) (circleKernel φ (pairingRadius n) y)
    linarith [hφM y, hψM n y]
  have hgR : ∀ n : ℕ, ∀ y, y ∉ closedBall (0 : ℂ) (R0 + 1) → φ y - circleKernel φ (pairingRadius n) y = 0 :=
    fun n y hy => by rw [hφR y hy, hψR n y hy, sub_zero]
  have hgm : ∀ n : ℕ, Measurable (fun y => φ y - circleKernel φ (pairingRadius n) y) := fun n =>
    hφc.measurable.sub (hψT n).1.continuous.measurable
  have hlim' : ∀ y, Tendsto (fun n : ℕ => φ y - circleKernel φ (pairingRadius n) y) atTop (𝓝 0) := fun y => by
    have := (tendsto_const_nhds (x := φ y)).sub (hlim y)
    simpa using this
  have hYi : ∀ n : ℕ, Integrable (fun ω =>
      ∫ y, (φ y - circleKernel φ (pairingRadius n) y) * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖) P :=
    fun n => integrable_integral_radial h (hgm n) (C := 2 * max C0 0) (by have := le_max_right C0 0; linarith) (hgM n) (hgR n)
  have hYr : TendstoInMeasure P (fun n ω =>
      ∫ y, (φ y - circleKernel φ (pairingRadius n) y) * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖)
      atTop (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_abs hYi (tendsto_integral_abs_radial h hgm hgM hgR hlim')
  -- the a.s. pathwise identity
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (hC ω (circleKernel φ (pairingRadius n)) - hC ω φ) + ∫ y,
          (φ y - circleKernel φ (pairingRadius n) y) * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖ =
        lateralSmearOf φ (pairingRadius n) (pairingRadius_pos n) (lateralProcess (hC ω) (hcirc ω)) -
          lateralProcess (hC ω) (hcirc ω) ⟨GFFObservable.pairing φ, hφ⟩ := by
    filter_upwards [h.ae_continuousOn_circle, hA Ω P hC hcirc hP h, hB Ω P hC hcirc hP h, hR3] with
      ω hω hAω hBω hR3ω
    intro n
    have hm := measurable_radialVersion_slice h ω
    rw [lateralSmearOf_eq_pathwise hω hAω hBω hm hφc hφs (pairingRadius_pos n) (hεle n) (hR3ω n),
      lateralProcess_pairing_eq hω hφ]
    have hI1 := integrable_mul_radial (locallyIntegrable_radial_fourth hm hBω) hφc hφs
    have hI2 := integrable_mul_radial (locallyIntegrable_radial_fourth hm hBω) (hψT n).1.continuous
      (hψT n).2.1
    beta_reduce at hI1 hI2
    have hsub : ∫ y, (φ y - circleKernel φ (pairingRadius n) y) * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖ =
        (∫ y, φ y * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖) -
          ∫ y, circleKernel φ (pairingRadius n) y * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖ := by
      rw [← integral_sub hI1 hI2]
      congr 1
      funext y
      ring
    rw [hsub]
    ring
  have hD : TendstoInMeasure P (fun n ω =>
      (hC ω (circleKernel φ (pairingRadius n)) - hC ω φ) + ∫ y,
        (φ y - circleKernel φ (pairingRadius n) y) * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖)
      atTop (fun _ => 0) :=
    (tendstoInMeasure_add_real hXm hYr).congr_right (Eventually.of_forall fun ω => by simp)
  have hsub : TendstoInMeasure P (fun n ω =>
      lateralSmearOf φ (pairingRadius n) (pairingRadius_pos n) (lateralProcess (hC ω) (hcirc ω)) -
        lateralProcess (hC ω) (hcirc ω) ⟨GFFObservable.pairing φ, hφ⟩) atTop (fun _ => 0) :=
    TendstoInMeasure.congr_left (fun n => hae.mono fun ω hω => hω n) hD
  exact tendstoInMeasure_of_sub_zero hsub

/-- **`ConeFieldScalingStep` from the two radial inputs** (chat 250 §5; H1 discharged by
`wholePlaneLateralSmear250_of_radial`; no H2 and no M). -/
theorem coneFieldScalingStep_of_radial (hscale : QuantumConeScalingInput) (hA : RadialContAe250)
    (hB : RadialL4Ae250) : ConeFieldScalingStep :=
  coneFieldScalingStep_proved250 hscale
    (coneLateralSmearStep250_of_wholePlane (wholePlaneLateralSmear250_of_radial hA hB))

end MatedCRT.LQGMeasure

#print axioms MatedCRT.LQGMeasure.wholePlaneLateralSmear250_of_radial
#print axioms MatedCRT.LQGMeasure.coneFieldScalingStep_of_radial
