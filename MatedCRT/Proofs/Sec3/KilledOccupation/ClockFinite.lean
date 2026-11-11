import Mathlib
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import MarkovProcess.Path.ExitTimeShift
import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail

/-!
# Finiteness of the weighted clock and measurability of the clock functionals (ClockFinite)

Discharges binders of `regClock_identification_of_GFF` (`RemovedTail.lean`):

* `hfin` (printed tex:396-398): `Φ(σ) < ∞` almost surely. The quenched mean (eq:occ-weightedmean,
  `weightedClock_quenchedMean`, `WeightedClock.lean`) equals `∫_D 2 G_D(y,·) dμ_ω`, which is finite by the
  Green potential bound at the pole `y` (eq:occ-potential, in the form `hS3`).
* `hQm` (implicit measurability of the removed weighted clock `Q_a`): from the kernel measurability `hdA` of the
  random clock measure `dA` (implicit in lem:occ-base; an explicit hypothesis here).
* the almost-everywhere form of `hreg` and `hνm`: for almost every field, `ε ↦ h_ε` is continuous in the
  centre (`ae_continuousOn_circle` of `IsWholePlaneGFF`).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.KilledOccupation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint measurability of `(ω, b) ↦ ∫⁻_{[0, σ b]} f(b u) dA_{ω,b}(u)`. The random clock `dA` enters through an
s-finite kernel `K` from `Ω × C(ℝ≥0, ℂ)` to `ℝ≥0` with `K x = dA x.1 x.2` (`hK`): the kernel measurability and
s-finiteness of the clock are implicit in lem:occ-base and are explicit hypotheses here. -/
lemma measurable_clockIntegral (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    {σ : ContinuousPath ℂ → ℝ≥0} (hσ : Measurable σ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x : Ω × ContinuousPath ℂ => ∫⁻ u in Icc 0 (σ x.2), f (x.2 u) ∂(dA x.1 x.2) := by
  have hσp : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 => σ p.1.2 :=
    hσ.comp (measurable_snd.comp measurable_fst)
  have hS : MeasurableSet {p : (Ω × ContinuousPath ℂ) × ℝ≥0 | p.2 ∈ Icc 0 (σ p.1.2)} := by
    have h : {p : (Ω × ContinuousPath ℂ) × ℝ≥0 | p.2 ∈ Icc 0 (σ p.1.2)} =
        {p | 0 ≤ p.2} ∩ {p | p.2 ≤ σ p.1.2} := by
      ext p
      simp [mem_Icc]
    rw [h]
    exact (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd hσp)
  have hev : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 => p.1.2 p.2 :=
    ContinuousEval.continuous_eval.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hF : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
      (Icc 0 (σ p.1.2)).indicator (fun u => f (p.1.2 u)) p.2 := by
    have h : (fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 => (Icc 0 (σ p.1.2)).indicator (fun u => f (p.1.2 u)) p.2) =
        fun p => if p.2 ∈ Icc 0 (σ p.1.2) then f (p.1.2 p.2) else 0 := by
      ext p
      simp [Set.indicator_apply]
    rw [h]
    exact Measurable.ite hS (hf.comp hev) measurable_const
  have key : (fun x : Ω × ContinuousPath ℂ => ∫⁻ u in Icc 0 (σ x.2), f (x.2 u) ∂(dA x.1 x.2)) =
      fun x => ∫⁻ u, (fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
        (Icc 0 (σ p.1.2)).indicator (fun u => f (p.1.2 u)) p.2) (x, u) ∂(K x) := by
    funext x
    rw [hK x]
    exact (lintegral_indicator measurableSet_Icc _).symm
  rw [key]
  exact hF.lintegral_kernel_prod_right'

/-- The removed `Φ`-part `Q_a` is measurable on the product (implicit measurability `hQm` of
`regClock_identification`), from the kernel measurability `hdA` and the measurability of the exit time `σ`. -/
lemma measurable_clockDistQ_of_kernel (γ : ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    {σ : ContinuousPath ℂ → ℝ≥0} (hσ : Measurable σ) (a : ℝ) :
    Measurable (clockDistQ γ dA σ a) := by
  have hf : Measurable fun w : ℂ => if ‖w‖ < 2 * a then gammaWeight γ w else 0 :=
    Measurable.ite (measurableSet_lt measurable_norm measurable_const) (measurable_gammaWeight γ)
      measurable_const
  have h := measurable_clockIntegral dA K hK hσ hf
  have key : clockDistQ γ dA σ a = fun x : Ω × ContinuousPath ℂ =>
      ∫⁻ u in Icc 0 (σ x.2), (fun w : ℂ => if ‖w‖ < 2 * a then gammaWeight γ w else 0) (x.2 u)
        ∂(dA x.1 x.2) := by
    funext x
    simp only [clockDistQ, removedWeightedClock, min_self]
  rw [key]
  exact h

/-- The weighted clock at its exit time is jointly measurable in the field and the path. -/
lemma measurable_weightedClock_exit (γ : ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    {σ : ContinuousPath ℂ → ℝ≥0} (hσ : Measurable σ) :
    Measurable fun x : Ω × ContinuousPath ℂ =>
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) := by
  have h := measurable_clockIntegral dA K hK hσ (measurable_gammaWeight γ)
  have key : (fun x : Ω × ContinuousPath ℂ =>
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2)) =
      fun x => ∫⁻ u in Icc 0 (σ x.2), gammaWeight γ (x.2 u) ∂(dA x.1 x.2) := by
    funext x
    simp only [weightedClock, min_self]
  rw [key]
  exact h

/-- **hfin, iterated form** (tex:396-398, from eq:occ-weightedmean and eq:occ-potential). For `P`-almost every
field `ω`, the weighted clock `Φ(σ)` is finite for `PB`-almost every Brownian path. The quenched mean
`weightedClock_quenchedMean` gives `∫ Φ(σ) dPB = ∫_D 2 G dμ_ω`, and `hS3` (the finite Green mass at the pole) makes
it finite. The domain `D = ball z r` lies in `ball 0 1`, as the weight identity `hweight` requires. -/
theorem weightedClock_ae_ae_ne_top (P : Measure Ω) (PB : Measure (ContinuousPath ℂ))
    (γ : ℝ) {z : ℂ} {r : ℝ} {y : ℂ} (hD : ball z r ⊆ ball (0 : ℂ) 1)
    (μ ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (hbase : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b) ∂PB =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * HarmonicBalls.greenFunction (ball z r) y x) * q x ∂(ν ω))
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω))
    (hS3 : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) < ⊤) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂PB, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) ≠ ⊤ := by
  have hQ := weightedClock_quenchedMean P PB γ (ball z r) measurableSet_ball hD
    (HarmonicBalls.greenFunction (ball z r) y) (HarmonicBalls.measurable_greenFunction Metric.isOpen_ball y)
    μ ν dA σ hbase hmeas hweight
  filter_upwards [hQ, hS3, hmeas] with ω hQω hS3ω hmω
  have hfinite : ∫⁻ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) ∂PB ≠ ⊤ := by
    rw [hQω]
    have h2 : ∫⁻ x in ball z r, ENNReal.ofReal (2 * HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) =
        ENNReal.ofReal 2 * ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num)
    rw [h2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS3ω.ne
  have hmeasΦ : Measurable fun b => weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) := by
    have h := hmω (gammaWeight γ) (measurable_gammaWeight γ)
    simpa only [weightedClock, min_self] using h
  exact (ae_lt_top hmeasΦ hfinite).mono fun b hb => hb.ne

/-- **hfin, product form** (tex:396-398): the almost-sure finiteness of `Φ(σ)` on the product of the field law and
planar Brownian motion, as the printed hypothesis `hfin` of `regClock_identification_of_GFF` requires. The iterated
form `weightedClock_ae_ae_ne_top` is lifted to the product by `Measure.ae_prod_iff_ae_ae`, using the joint
measurability of `Φ(σ)` (`measurable_weightedClock_exit`). -/
theorem weightedClock_ae_prod_ne_top (P : Measure Ω) [IsProbabilityMeasure P]
    (PB : Measure (ContinuousPath ℂ)) [IsProbabilityMeasure PB]
    (γ : ℝ) {z : ℂ} {r : ℝ} {y : ℂ} (hD : ball z r ⊆ ball (0 : ℂ) 1)
    (μ ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    (hσ : Measurable σ)
    (hbase : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b) ∂PB =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * HarmonicBalls.greenFunction (ball z r) y x) * q x ∂(ν ω))
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω))
    (hS3 : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) < ⊤) :
    ∀ᵐ x ∂(P.prod PB), weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤ := by
  have hm := measurable_weightedClock_exit γ dA K hK hσ
  have hset : MeasurableSet {x : Ω × ContinuousPath ℂ |
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤} :=
    hm (measurableSet_singleton ⊤).compl
  exact (Measure.ae_prod_iff_ae_ae hset).2
    (weightedClock_ae_ae_ne_top P PB γ hD μ ν dA σ hbase hmeas hweight hS3)

/-- The regularized density `ε^{γ²/2} e^{γ h_ε(x)}` (`regDensity`) is measurable in `x` as soon as the circle
average `x ↦ hc ε x` is continuous (`circleAverage_log_norm_eq` turns the logarithmic part into `log (max |x| ε)`). -/
lemma measurable_regDensity_of_continuous (γ ε : ℝ) (hε : 0 < ε) (hc : ℝ → ℂ → ℝ)
    (hcont : Continuous fun x => hc ε x) : Measurable (regDensity γ ε hc) := by
  have hfc : ∀ x : ℂ, HarmonicBalls.fieldCircleAverage γ hc ε x =
      hc ε x - γ * Real.log (max ‖x‖ ε) := by
    intro x
    unfold HarmonicBalls.fieldCircleAverage
    rw [circleAverage_log_norm_eq hε x]
  have h : regDensity γ ε hc = fun x : ℂ =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - γ * Real.log (max ‖x‖ ε)))) := by
    funext x
    unfold regDensity
    rw [hfc x]
  rw [h]
  refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul ?_)))
  exact hcont.measurable.sub (measurable_const.mul (Real.measurable_log.comp
    (measurable_norm.max measurable_const)))

/-- **Almost-sure form of `hreg`.** For `P`-almost every field, every regularized density `regDensity γ ε (hc ω)`
(`ε > 0`) is measurable, because `IsWholePlaneGFF.ae_continuousOn_circle` makes `(r, z) ↦ hc ω r z` continuous
on `(0, ∞) × ℂ` for almost every `ω`. The quantifier over all `ω` of the printed binder `hreg` is not derivable
from the GFF structure; only this almost-sure form is. -/
theorem ae_measurable_regDensity {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (hc ω)) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω ε hε
  have hcont : Continuous fun x => hc ω ε x := by
    have h1 : ContinuousOn (fun x : ℂ => (ε, x)) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h2 : ContinuousOn (fun x : ℂ => hc ω ε x) univ :=
      hω.comp h1 (fun x _ => ⟨mem_Ioi.2 hε, mem_univ x⟩)
    exact continuousOn_univ.mp h2
  exact measurable_regDensity_of_continuous γ ε hε (hc ω) hcont

end MatedCRT.KilledOccupation
