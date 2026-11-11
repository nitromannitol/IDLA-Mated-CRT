import Mathlib
import HarmonicBalls.Defs.Brownian
import MarkovProcess.Path.ExitTimeShift
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite
import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail

/-!
# Removed `φ`-part small and the closed identification of the clock (ClockClosure)

Remaining inputs (explicit hypotheses): the GFF structure `hGFF` (`origin_tail_moment` is proved from it); the ordinary Brownian occupation identity `hS0`; the
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.KilledOccupation

/-! ### The removed `φ`-part is small, with the origin tail moment as a hypothesis -/

/-- `removed_tail_small` (`RemovedTail.lean`) with the origin tail moment supplied as the hypothesis `hT0`, the
conclusion of `origin_tail_moment` for the field `hc`. The measurability inputs `hreg`, `hRm` are needed only for
`ε > 0`. The proof is that of `removed_tail_small`. -/
theorem removed_tail_small_mod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (_hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hc : Ω → ℝ → ℂ → ℝ)
    (hT0 : ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (hreg : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (hc ω)))
    (hRm : ∀ ε a : ℝ, 0 < ε → Measurable (clockDistR γ hc (exitNN z r) ε a)) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x} ≤ δ := by
  intro η hη δ hδ
  obtain ⟨K, hK, ρ, hρ, hG'⟩ := greenFunction_origin_bound hr hr2 hG hy
  have hp1' : p < 4 / γ ^ 2 - 1 := lt_of_lt_of_le hp1 (min_le_right _ _)
  have hp1le : p ≤ 1 := (hp1.trans_le (min_le_left _ _)).le
  have hκpos : 0 < κ := by
    have h5 : p + 1 < 4 / γ ^ 2 := by linarith
    have h6 : (p + 1) * γ ^ 2 < 4 := (lt_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)).1 h5
    have hfac : κ = p / 2 * (4 - γ ^ 2 * (p + 1)) := by rw [hκ]; ring
    rw [hfac]
    have : 0 < 4 - γ ^ 2 * (p + 1) := by linarith
    exact mul_pos (by linarith) this
  obtain ⟨C, a₀, ha₀, hT⟩ := hT0
  set c : ℝ≥0∞ := 2 * ENNReal.ofReal K / ENNReal.ofReal η with hc_def
  have hηne : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.2 hη).ne'
  have hcfin : c ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hηne
  have hcpne : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le hcfin
  -- the deterministic bound in `a`
  have h2a : Tendsto (fun a : ℝ => 2 * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun a ha => ?_⟩
    · have h0 : Tendsto (fun a : ℝ => 2 * a) (𝓝 0) (𝓝 0) :=
        (by fun_prop : Continuous fun a : ℝ => 2 * a).tendsto' 0 0 (by simp)
      exact h0.mono_left nhdsWithin_le_nhds
    · exact mul_pos two_pos (mem_Ioi.1 ha)
  have hlim2 : Tendsto (fun a : ℝ => C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((tendsto_rpow_mul_log_rpow hκpos hp0).comp h2a).const_mul C
    rw [mul_zero] at this
    exact this
  have hlim3 : Tendsto (fun a : ℝ => ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hlim2
    rw [ENNReal.ofReal_zero] at this
    exact this
  have hB : Tendsto (fun a : ℝ => c ^ p * ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hlim3 (Or.inr hcpne)
    rw [mul_zero] at this
    exact this
  have hsmall := hB.eventually (gt_mem_nhds hδ)
  have hA : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioo 0 (min (a₀ / 2) (min (ρ / 2) (1 / 2))) :=
    Ioo_mem_nhdsGT (lt_min (by linarith) (lt_min (by linarith) (by norm_num)))
  filter_upwards [hsmall, hA] with a hsa hAa
  obtain ⟨ha0, haL⟩ := hAa
  have h2a0 : 2 * a < a₀ := by
    have := lt_of_lt_of_le haL (min_le_left _ _)
    linarith
  have h2ρ : 2 * a ≤ ρ := by
    have := lt_of_lt_of_le haL (min_le_right _ _ |>.trans (min_le_left _ _))
    linarith
  have h21 : 2 * a ≤ 1 := by
    have := lt_of_lt_of_le haL (min_le_right _ _ |>.trans (min_le_right _ _))
    linarith
  filter_upwards [Ioo_mem_nhdsGT ha₀] with ε hε
  have hbound := removed_tail_bound P hc hS0 hK hG' h2ρ h21 hp0 hp1le hη (fun ω => hreg ω ε hε.1)
    (hRm ε a hε.1) hy (γ := γ) (ε := ε) (a := a) (p := p) (η := η)
  have hW : ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P ≤
      ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)) := by
    have := hT (2 * a) ⟨by linarith, h2a0⟩ ε hε
    rwa [mul_assoc] at this
  calc (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x}
      ≤ c ^ p * ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P := hbound
    _ ≤ c ^ p * ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)) := by
        gcongr
    _ ≤ δ := hsa.le

/-- **Identification of the clock, closed form** (tex:370-414; `regClock_identification_of_GFF` of `RemovedTail.lean`
with its measurability binders and `hfin` discharged).

Discharged here: `hfin` (`weightedClock_ae_prod_ne_top`, from the quenched mean and the finite Green mass `hS3`),
`hQm` (`measurable_clockDistQ_of_kernel`), `hreg`, `hνm`, `hRm` (for the field `modField N hc` that agrees with `hc`
off a null set `N`, `measurable_modField_clockDistR`), and `hR` (`removed_tail_small_mod`, with the origin tail moment
of `origin_tail_moment` transferred from `hc` to `modField N hc`).

Remaining inputs (explicit hypotheses): the GFF structure `hGFF`; the ordinary Brownian occupation identity `hS0`; the
Green disk formula `hG`; the printed claim `hE` (tex:377-385, the `χ_a`-parts converge in probability, from lem:occ-base);
the s-finite kernel `K` of the random clock with `hK` (the measurability of `dA`, implicit in lem:occ-base); and the
upstream occupation inputs `hbase`, `hmeas`, `hweight`, `hS3` of `weightedClock_quenchedMean` (`hD : ball z r ⊆ ball 0 1`).
No joint measurability or moment bound is an input: `origin_tail_moment` is proved from `hGFF` (747c849). -/
theorem regClock_identification_closed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hc : Ω → ℝ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    (μ ν : Ω → Measure ℂ) (hD : ball z r ⊆ ball (0 : ℂ) 1)
    (hbase : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), q (b u) ∂(dA ω b) ∂(HarmonicBalls.planarBrownianMotion y) =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * HarmonicBalls.greenFunction (ball z r) y x) * q x ∂(ν ω))
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (exitNN z r b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω))
    (hS3 : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) < ⊤)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ hc dA (exitNN z r) ε a x}) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistD γ hc dA (exitNN z r) ε x}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have hσ : Measurable (exitNN z r) :=
    ENNReal.measurable_toNNReal.comp (ContinuousPath.measurable_exitTime (ball z r) Metric.isOpen_ball)
  obtain ⟨N, hN, hN0, hgood⟩ := exists_null_continuous hGFF
  have hmeasCirc : ∀ ε : ℝ, 0 < ε → ∀ x : ℂ, Measurable fun ω => hc ω ε x :=
    fun ε hε x => hGFF.measurable_circle ε x hε
  -- the field modified on `N`
  have hreg' : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (modField N hc ω)) := fun ω ε hε =>
    measurable_regDensity_of_continuous γ ε hε _ (modField_continuous hgood ω ε hε)
  have hνm' : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (nuDensity γ ε (modField N hc ω)) := fun ω ε hε =>
    measurable_nuDensity_of_continuous γ ε _ (modField_continuous hgood ω ε hε)
  have hRm' : ∀ ε a : ℝ, 0 < ε → Measurable (clockDistR γ (modField N hc) (exitNN z r) ε a) :=
    fun ε a hε => measurable_modField_clockDistR hN hmeasCirc hgood γ ε a hε (exitNN z r) hσ
  have hQm : ∀ a : ℝ, Measurable (clockDistQ γ dA (exitNN z r) a) :=
    fun a => measurable_clockDistQ_of_kernel γ dA K hK hσ a
  have hfin := weightedClock_ae_prod_ne_top P (HarmonicBalls.planarBrownianMotion y) γ hD μ ν dA
    (exitNN z r) K hK hσ hbase hmeas hweight hS3
  -- the origin tail moment, transferred from `hc` to the modified field
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hT0 : ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (modField N hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := by
    obtain ⟨C, a₀, ha₀, hT⟩ := origin_tail_moment P hC hc hGFF hγ0 hγ2 hp0 hp1 hκ
    refine ⟨C, a₀, ha₀, fun a ha ε hε => ?_⟩
    have hae : (fun ω => weightedMass γ ε (modField N hc ω) (ball 0 a) ^ p) =ᵐ[P]
        (fun ω => weightedMass γ ε (hc ω) (ball 0 a) ^ p) := by
      filter_upwards [hNae] with ω hω
      rw [modField_eq_of_not_mem hω]
    exact (lintegral_congr_ae hae).trans_le (hT a ha ε hε)
  have hR' := removed_tail_small_mod P hγ0 hγ2 hp0 hp1 hκ (modField N hc) hT0 hr hr2 hG hy hS0 hreg' hRm'
  -- the removed `χ_a`-parts and the sup-distance, transferred along the null set `N`
  have hE' : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ (modField N hc) dA (exitNN z r) ε a x}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro a ha η hη
    refine Tendsto.congr (fun ε => ?_) (hE a ha η hη)
    refine measure_prod_congr_of_fst_notMem _ hN0 (fun x hx => ?_)
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    unfold clockDistE
    rw [modField_eq_of_not_mem hx]
  have main := regClock_identification P (HarmonicBalls.planarBrownianMotion y) hγ0.ne' (modField N hc) dA
    (exitNN z r) hreg' hνm' hQm hfin hE' hR'
  intro η hη
  refine Tendsto.congr (fun ε => ?_) (main η hη)
  refine measure_prod_congr_of_fst_notMem _ hN0 (fun x hx => ?_) |>.symm
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold clockDistD
  rw [modField_eq_of_not_mem hx]

end MatedCRT.KilledOccupation
