import Mathlib
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import MarkovProcess.Path.ExitTimeShift
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete

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


/-! ### Measurability of the regularized clocks

The printed measurability binders `hreg`, `hνm`, `hRm` quantify over every field `ω`, but `IsWholePlaneGFF` makes the
circle averages continuous in the centre only for almost every `ω`. We therefore replace the field by `modField N hc`,
which is `0` on a measurable null set `N` of the field index and equals `hc` off `N`. -/

/-- Evaluation of a path at a measurable time, jointly measurable in the path and the time. -/
lemma measurable_path_eval {X : Type*} [MeasurableSpace X] {b : X → ContinuousPath ℂ} {u : X → ℝ≥0}
    (hb : Measurable b) (hu : Measurable u) : Measurable fun x => b x (u x) :=
  ContinuousEval.continuous_eval.measurable.comp (hb.prodMk hu)

/-- Tonelli-type measurability of `x ↦ ∫⁻_{[0, s x]} g(x, u) dμ(u)` for a fixed s-finite measure `μ` on `ℝ≥0`. -/
lemma measurable_lintegral_Icc_fixed {X : Type*} [MeasurableSpace X] (μ : Measure ℝ≥0) [SFinite μ]
    {s : X → ℝ≥0} (hs : Measurable s) {g : X × ℝ≥0 → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∫⁻ u in Icc 0 (s x), g (x, u) ∂μ := by
  have hS : MeasurableSet {p : X × ℝ≥0 | p.2 ∈ Icc 0 (s p.1)} := by
    have h : {p : X × ℝ≥0 | p.2 ∈ Icc 0 (s p.1)} = {p | 0 ≤ p.2} ∩ {p | p.2 ≤ s p.1} := by
      ext p
      simp [mem_Icc]
    rw [h]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hs.comp measurable_fst))
  have hF : Measurable fun p : X × ℝ≥0 => (Icc 0 (s p.1)).indicator (fun u => g (p.1, u)) p.2 := by
    have h : (fun p : X × ℝ≥0 => (Icc 0 (s p.1)).indicator (fun u => g (p.1, u)) p.2) =
        fun p => if p.2 ∈ Icc 0 (s p.1) then g p else 0 := by
      ext p
      simp [Set.indicator_apply]
    rw [h]
    exact Measurable.ite hS hg measurable_const
  have key : (fun x => ∫⁻ u in Icc 0 (s x), g (x, u) ∂μ) =
      fun x => ∫⁻ u, (Icc 0 (s x)).indicator (fun u => g (x, u)) u ∂μ := by
    funext x
    exact (lintegral_indicator measurableSet_Icc _).symm
  rw [key]
  exact hF.lintegral_prod_right'

/-- `regDensity` in closed form: `ε^{γ²/2} exp(γ (h_ε(x) - γ log (|x| ∨ ε)))` (`circleAverage_log_norm_eq`). -/
lemma regDensity_formula (γ ε : ℝ) (hε : 0 < ε) (hc : ℝ → ℂ → ℝ) (x : ℂ) :
    regDensity γ ε hc x = ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - γ * Real.log (max ‖x‖ ε)))) := by
  unfold regDensity HarmonicBalls.fieldCircleAverage
  rw [circleAverage_log_norm_eq hε x]

lemma measurable_nuDensity_of_continuous (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (hcont : Continuous fun x => hc ε x) :
    Measurable (nuDensity γ ε hc) := by
  unfold nuDensity
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul hcont.measurable)))

/-- Joint measurability of `(ω, x) ↦ ε^{γ²/2} exp(γ (F ω x - γ log (|x| ∨ ε)))` when `F` is continuous in `x` and
measurable in `ω`: a Carathéodory function. -/
lemma measurable_uncurry_regDensity {Ω : Type*} [MeasurableSpace Ω] (γ ε : ℝ) (hε : 0 < ε) {F : Ω → ℂ → ℝ}
    (hF_cont : ∀ ω, Continuous fun x => F ω x) (hF_meas : ∀ x, Measurable fun ω => F ω x) :
    Measurable fun q : Ω × ℂ =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (F q.1 q.2 - γ * Real.log (max ‖q.2‖ ε)))) := by
  let u : ℂ → Ω → ℝ := fun x ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ * (F ω x - γ * Real.log (max ‖x‖ ε)))
  have hlog : Continuous fun x : ℂ => Real.log (max ‖x‖ ε) :=
    Continuous.log (continuous_norm.max continuous_const)
      (fun x => (lt_of_lt_of_le hε (le_max_right _ _)).ne')
  have hu_cont : ∀ ω : Ω, Continuous fun x : ℂ => u x ω := fun ω =>
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((hF_cont ω).sub (continuous_const.mul hlog))))
  have hu_meas : ∀ x : ℂ, Measurable fun ω : Ω => u x ω := fun x =>
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ((hF_meas x).sub measurable_const)))
  have hU : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas
  exact ENNReal.measurable_ofReal.comp (hU.comp measurable_swap)

open Classical in
/-- The field `hc` with its values on the measurable set `N` of field indices replaced by `0`. -/
def modField {Ω : Type*} (N : Set Ω) (hc : Ω → ℝ → ℂ → ℝ) : Ω → ℝ → ℂ → ℝ :=
  fun ω r z => if ω ∈ N then 0 else hc ω r z

lemma modField_eq_of_not_mem {Ω : Type*} {N : Set Ω} {hc : Ω → ℝ → ℂ → ℝ} {ω : Ω} (hω : ω ∉ N) :
    modField N hc ω = hc ω := by
  funext r z
  simp [modField, hω]

/-- Off a measurable null set of field indices, the circle averages of `IsWholePlaneGFF` are continuous in the centre
(`ae_continuousOn_circle`). -/
lemma exists_null_continuous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hc : Ω → ℝ → ℂ → ℝ} (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => hc ω ε x := by
  have h := hGFF.ae_continuousOn_circle
  rw [ae_iff] at h
  refine ⟨toMeasurable P {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hc ω p.1 p.2) (Ioi 0 ×ˢ univ)},
    measurableSet_toMeasurable _ _, by rw [measure_toMeasurable]; exact h, fun ω hω ε hε => ?_⟩
  have hgood : ContinuousOn (fun p : ℝ × ℂ => hc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    by_contra hbad
    exact hω (subset_toMeasurable _ _ hbad)
  have h1 : ContinuousOn (fun x : ℂ => ((ε, x) : ℝ × ℂ)) univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h2 : ContinuousOn (fun x : ℂ => hc ω ε x) univ :=
    hgood.comp h1 (fun x _ => ⟨mem_Ioi.2 hε, mem_univ x⟩)
  exact continuousOn_univ.mp h2

lemma modField_continuous {Ω : Type*} {N : Set Ω} {hc : Ω → ℝ → ℂ → ℝ}
    (hgood : ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => hc ω ε x)
    (ω : Ω) (ε : ℝ) (hε : 0 < ε) : Continuous fun x : ℂ => modField N hc ω ε x := by
  by_cases hω : ω ∈ N
  · have h : (fun x : ℂ => modField N hc ω ε x) = fun _ => 0 := by
      funext x
      simp [modField, hω]
    rw [h]
    exact continuous_const
  · have h : (fun x : ℂ => modField N hc ω ε x) = fun x => hc ω ε x := by
      funext x
      simp [modField, hω]
    rw [h]
    exact hgood ω hω ε hε

/-- Joint measurability of `(ω, x) ↦ regDensity γ ε (modField N hc ω) x`, for `ε > 0`. -/
lemma measurable_regDensity_modField {Ω : Type*} [MeasurableSpace Ω] {N : Set Ω} (hN : MeasurableSet N)
    {hc : Ω → ℝ → ℂ → ℝ} (hmeas : ∀ ε : ℝ, 0 < ε → ∀ x : ℂ, Measurable fun ω => hc ω ε x)
    (hgood : ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => hc ω ε x) (γ ε : ℝ) (hε : 0 < ε) :
    Measurable fun q : Ω × ℂ => regDensity γ ε (modField N hc q.1) q.2 := by
  have hF_cont : ∀ ω, Continuous fun x => modField N hc ω ε x := fun ω => modField_continuous hgood ω ε hε
  have hF_meas : ∀ x, Measurable fun ω => modField N hc ω ε x := fun x =>
    Measurable.ite hN measurable_const (hmeas ε hε x)
  have h := measurable_uncurry_regDensity (Ω := Ω) γ ε hε hF_cont hF_meas
  simp only [regDensity_formula γ ε hε]
  exact h

/-- The removed-part functional `R_{ε,a}` (`clockDistR`) is measurable on the product, for `ε > 0`. -/
lemma measurable_clockDistR_of_density {Ω : Type*} [MeasurableSpace Ω] (γ ε a : ℝ)
    (hc : Ω → ℝ → ℂ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ)
    (hG : Measurable fun q : Ω × ℂ => regDensity γ ε (hc q.1) q.2) :
    Measurable (clockDistR γ hc σ ε a) := by
  have : SFinite timeLeb := by
    unfold timeLeb
    infer_instance
  have hσ' : Measurable fun x : Ω × ContinuousPath ℂ => σ x.2 := hσ.comp measurable_snd
  have hev : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 => p.1.2 p.2 :=
    measurable_path_eval (measurable_snd.comp measurable_fst) measurable_snd
  have hpair : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 => (p.1.1, p.1.2 p.2) :=
    (measurable_fst.comp measurable_fst).prodMk hev
  have hg : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
      if ‖p.1.2 p.2‖ < 2 * a then regDensity γ ε (hc p.1.1) (p.1.2 p.2) else 0 :=
    Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp hev) measurable_const)
      (hG.comp hpair) measurable_const
  exact measurable_lintegral_Icc_fixed timeLeb hσ' hg

/-- The regularized clocks of the modified field are jointly measurable, for `ε > 0`: `hreg`, `hνm`, `hRm` hold for
every field index. -/
lemma measurable_modField_clockDistR {Ω : Type*} [MeasurableSpace Ω] {N : Set Ω} (hN : MeasurableSet N)
    {hc : Ω → ℝ → ℂ → ℝ} (hmeas : ∀ ε : ℝ, 0 < ε → ∀ x : ℂ, Measurable fun ω => hc ω ε x)
    (hgood : ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => hc ω ε x) (γ ε a : ℝ) (hε : 0 < ε)
    (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) :
    Measurable (clockDistR γ (modField N hc) σ ε a) :=
  measurable_clockDistR_of_density γ ε a (modField N hc) σ hσ
    (measurable_regDensity_modField hN hmeas hgood γ ε hε)

/-! ### Transfer of events along a null set of fields -/

lemma ae_fst_notMem_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (PB : Measure (ContinuousPath ℂ))
    [SFinite PB] {N : Set Ω} (hN0 : P N = 0) : ∀ᵐ x ∂(P.prod PB), x.1 ∉ N := by
  rw [ae_iff]
  have h : {x : Ω × ContinuousPath ℂ | ¬ x.1 ∉ N} = N ×ˢ (univ : Set (ContinuousPath ℂ)) := by
    ext x
    simp
  rw [h, Measure.prod_prod, hN0, zero_mul]

lemma measure_prod_congr_of_fst_notMem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (PB : Measure (ContinuousPath ℂ)) [SFinite PB] {N : Set Ω} (hN0 : P N = 0)
    {S T : Set (Ω × ContinuousPath ℂ)} (h : ∀ x : Ω × ContinuousPath ℂ, x.1 ∉ N → (x ∈ S ↔ x ∈ T)) :
    (P.prod PB) S = (P.prod PB) T := by
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_fst_notMem_prod PB hN0] with x hx using h x hx

/-!
### Exit time of a ball under planar Brownian motion (hσexit of `rescaled_occupation_green_identity`)

The exit time `τ` of `ball z r` is almost surely finite: `{τ = ∞}` lies in `{ω T ∈ ball z r}` for every
`T`, and the real part of `ω T` is Gaussian with variance `T`, which gives mass at most
`2r/√(2Real.piT) → 0` to an interval of length `2r`. Literature: Mörters-Peres, Brownian Motion, Ch. 2 (a.s. exit from
bounded sets); Armitage-Gardiner for the potential-theoretic reading of the exit time.
-/

open HarmonicBalls in
/-- The real part of planar Brownian motion at a fixed time `T` is the Gaussian `N(Re y, T)`. -/
theorem planarBrownianMotion_re_eval_map (y : ℂ) (T : NNReal) :
    (planarBrownianMotion y).map (fun ω : ContinuousPath ℂ => (ω T).re) = gaussianReal y.re T := by
  have hre : Measurable (fun ω : ContinuousPath ℂ => (reImPath ω).1) :=
    measurable_fst.comp measurable_reImPath
  have hcomp : (fun ω : ContinuousPath ℂ => (ω T).re) =
      (fun f : ContinuousPath ℝ => f T) ∘ (fun ω : ContinuousPath ℂ => (reImPath ω).1) := by
    funext ω
    simp [reImPath_fst_apply]
  have hg : Measurable (fun f : ContinuousPath ℝ => f T) := ContinuousPath.measurable_coordinateProcess T
  rw [hcomp, ← Measure.map_map hg hre, planarBrownianMotion_map_re]
  exact brownianMotion_map_eval T y.re

/-- A Gaussian `N(μ, T)` with `T ≠ 0` gives an interval `(a, b)` mass at most `(b - a) / √(2Real.piT)`
(the density is bounded by `(√(2Real.piT))⁻¹`). -/
theorem gaussianReal_Ioo_le_inv_sqrt (μ : ℝ) {T : NNReal} (hT : T ≠ 0) (a b : ℝ) :
    gaussianReal μ T (Ioo a b) ≤ ENNReal.ofReal ((√(2 * Real.pi * (T : ℝ)))⁻¹ * (b - a)) := by
  have hc0 : 0 ≤ (√(2 * Real.pi * (T : ℝ)))⁻¹ := by positivity
  have hpt : ∀ x : ℝ, gaussianPDF μ T x ≤ ENNReal.ofReal (√(2 * Real.pi * (T : ℝ)))⁻¹ := by
    intro x
    simp only [gaussianPDF_def, gaussianPDFReal_def]
    refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hc0 (Real.exp_le_one_iff.2 ?_))
    have h1 : 0 ≤ (x - μ) ^ 2 / (2 * (T : ℝ)) := by positivity
    have h2 : -(x - μ) ^ 2 / (2 * (T : ℝ)) = -((x - μ) ^ 2 / (2 * (T : ℝ))) := neg_div _ _
    rw [h2]
    linarith
  calc gaussianReal μ T (Ioo a b) = ∫⁻ x in Ioo a b, gaussianPDF μ T x := gaussianReal_apply μ hT _
    _ ≤ ∫⁻ _ in Ioo a b, ENNReal.ofReal (√(2 * Real.pi * (T : ℝ)))⁻¹ :=
        setLIntegral_mono' measurableSet_Ioo (fun x _ => hpt x)
    _ = ENNReal.ofReal (√(2 * Real.pi * (T : ℝ)))⁻¹ * volume (Ioo a b) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((√(2 * Real.pi * (T : ℝ)))⁻¹ * (b - a)) := by
        rw [Real.volume_Ioo, ENNReal.ofReal_mul hc0]

open HarmonicBalls in
/-- **Almost sure finite exit time** (hσexit input): the first exit time of a ball by planar Brownian motion is
almost surely finite, from every starting point. -/
theorem planar_exit_ae_lt_top (y z : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion y, ContinuousPath.exitTime (ball z r) b < ⊤ := by
  rw [ae_iff]
  have hbound : ∀ n : ℕ, (planarBrownianMotion y) {b : ContinuousPath ℂ | ¬ ContinuousPath.exitTime (ball z r) b < ⊤}
      ≤ ENNReal.ofReal ((√(2 * Real.pi * ((n : ℝ) + 1)))⁻¹ * (2 * r)) := by
    intro n
    set T : NNReal := (n : NNReal) + 1 with hT
    have hT0 : T ≠ 0 := by rw [hT]; positivity
    have hTr : (T : ℝ) = (n : ℝ) + 1 := by simp [hT]
    have hmeas : Measurable (fun b : ContinuousPath ℂ => (b T).re) :=
      Complex.measurable_re.comp (ContinuousPath.measurable_coordinateProcess T)
    have hsub : {b : ContinuousPath ℂ | ¬ ContinuousPath.exitTime (ball z r) b < ⊤} ⊆
        (fun b : ContinuousPath ℂ => (b T).re) ⁻¹' Ioo (z.re - r) (z.re + r) := by
      intro b hb
      have htop : ContinuousPath.exitTime (ball z r) b = ⊤ := top_le_iff.1 (not_lt.1 hb)
      have hall : ∀ t : NNReal, b t ∈ ball z r := (ContinuousPath.exitTime_eq_top_iff _ _).1 htop
      have h1 : dist (b T) z < r := mem_ball.1 (hall T)
      rw [dist_eq_norm] at h1
      have h2 : |(b T - z).re| ≤ ‖b T - z‖ := Complex.abs_re_le_norm _
      have h3 : |(b T - z).re| < r := lt_of_le_of_lt h2 h1
      rw [Complex.sub_re, abs_lt] at h3
      simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> linarith [h3.1, h3.2]
    calc (planarBrownianMotion y) {b : ContinuousPath ℂ | ¬ ContinuousPath.exitTime (ball z r) b < ⊤}
        ≤ (planarBrownianMotion y) ((fun b : ContinuousPath ℂ => (b T).re) ⁻¹' Ioo (z.re - r) (z.re + r)) :=
          measure_mono hsub
      _ = (planarBrownianMotion y).map (fun b : ContinuousPath ℂ => (b T).re) (Ioo (z.re - r) (z.re + r)) := by
          rw [Measure.map_apply hmeas measurableSet_Ioo]
      _ = gaussianReal y.re T (Ioo (z.re - r) (z.re + r)) := by
          rw [planarBrownianMotion_re_eval_map]
      _ ≤ ENNReal.ofReal ((√(2 * Real.pi * (T : ℝ)))⁻¹ * ((z.re + r) - (z.re - r))) :=
          gaussianReal_Ioo_le_inv_sqrt _ hT0 _ _
      _ = ENNReal.ofReal ((√(2 * Real.pi * ((n : ℝ) + 1)))⁻¹ * (2 * r)) := by
          rw [hTr, show (z.re + r) - (z.re - r) = 2 * r by ring]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((√(2 * Real.pi * ((n : ℝ) + 1)))⁻¹ * (2 * r)))
      atTop (𝓝 0) := by
    have hA : Tendsto (fun n : ℕ => 2 * Real.pi * ((n : ℝ) + 1)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hR : Tendsto (fun n : ℕ => (√(2 * Real.pi * ((n : ℝ) + 1)))⁻¹ * (2 * r)) atTop (𝓝 (0 * (2 * r))) :=
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hA)).mul_const (2 * r)
    simpa [zero_mul, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hR
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

open HarmonicBalls in
/-- **hσexit, discharged** (`MainOccupation.lean`, `rescaled_occupation_green_identity`): for the first exit time
`σ b = (exitTime (ball z r) b).toNNReal` of planar Brownian motion started in the ball, almost surely the path stays
in the ball before `σ` and lies outside the ball at `σ`. -/
theorem ae_planar_exit_spec (y z : ℂ) (r : ℝ) (hy : y ∈ ball z r) :
    ∀ᵐ b ∂planarBrownianMotion y,
      (∀ s < (ContinuousPath.exitTime (ball z r) b).toNNReal, b s ∈ ball z r) ∧
        b ((ContinuousPath.exitTime (ball z r) b).toNNReal) ∉ ball z r := by
  filter_upwards [planar_exit_ae_lt_top y z r, ae_planarBrownianMotion_eval_zero y] with b hfin h0
  have hfin' : ContinuousPath.exitTime (ball z r) b ≠ ⊤ := ne_top_of_lt hfin
  refine ⟨fun s hs => ContinuousPath.mem_of_lt_exitTime _ _ s ?_, ?_⟩
  · rw [← ENNReal.coe_toNNReal hfin']
    exact_mod_cast hs
  · have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (ball z r) isOpen_ball b
      (by rw [h0]; exact hy) hfin'
    rw [isOpen_ball.frontier_eq] at hfr
    exact hfr.2

end MatedCRT.KilledOccupation
