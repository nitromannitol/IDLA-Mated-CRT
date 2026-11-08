import MatedCRT.Proofs.Field.WholePlaneAffine
import MatedCRT.Proofs.Field.WholePlaneCircleLaw
import MatedCRT.Proofs.Field.WholePlaneLQGCoord
import MatedCRT.Proofs.Field.WholePlaneBrownian
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import MatedCRT.Proposed.SheffieldWang2016

/-!
# The insertion-`α` coordinate rule: the exact Step and its no-insertion-atom component

Internal module. It is not a literature input and cites no source for the whole-plane statement.

* `InsertionCoordinateExtensionStep` is the exact Step (steps3 Section 2, lines 405-712, sha256 `d34cf930...`). It was
  previously declared in `MatedCRT/Proposed/DuplantierSheffieldCoordinate2011.lean`, which now keeps a
  backwards-compatible abbreviation of it.
* `insertion_no_atom_zero_ae` is the first component of the written proof (steps3 "Circle law, measurable limits, and
  absence of an atom", Lemma `lem:insertion-no-atom`). It assumes the measurable-decoder premise
  `MeasurableDyadicDecoder` (its written constructor is not yet formalized). The Gaussian marginal is derived from
  `Field.map_radial_eq_brownian`; the affine change of variables is `Field.isLQGLimit_affine_iff`.

Not yet formalized here: the punctured all-scale convergence (Sheffield-Wang Theorem 1.1 with the Dirichlet projection),
the identification for complex `a ≠ 0` and the translation by `b`. The exact Step is therefore not proved.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- **The exact Step `InsertionCoordinateExtensionStep`** (steps3 Section 2, lines 405-712). For `0 < γ < 2`,
`α < Q = lqgQ γ`, a whole-plane GFF `(hC, hcirc)` on a probability space whose insertion-`α` LQG measure is `μ`, and
every complex affine map `z ↦ a z + b` with `a ≠ 0`: almost surely the circle averages
`(ε, z) ↦ h_{|a| ε}(a z + b) + Q log |a|` converge vaguely to `μ ∘ φ⁻¹` along the dyadic scales. The quantifier over
`(a, b)` precedes the almost-sure assertion, and no measurability of `μ` is assumed. -/
def InsertionCoordinateExtensionStep : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
  ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ, ∀ᵐ ω ∂P,
    IsLQGLimit γ (fun ε z => fieldCircleAverage α (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
      ((μ ω).map fun x => (x - b) / a)

/-! ## Positive-radius processes -/

/-- The positive-radius circle process `(r, z) ↦ h r z` on `(0, ∞) × ℂ`: the object of `Field.wholePlane_circle_law`. -/
def circleProc (h : ℝ → ℂ → ℝ) : Set.Ioi (0 : ℝ) × ℂ → ℝ := fun p => h p.1 p.2

/-- Extension of a positive-radius process to `ℝ × ℂ` by `0` at non-positive radii. -/
noncomputable def procExt (u : Set.Ioi (0 : ℝ) × ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if hr : 0 < r then u (⟨r, hr⟩, z) else 0

theorem procExt_circleProc (h : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    procExt (circleProc h) r z = h r z := by
  simp [procExt, circleProc, hr]

theorem measurable_circleProc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    Measurable fun ω => circleProc (hcirc ω) :=
  Measurable.of_eval fun p => hGFF.measurable_circle p.1 p.2 p.1.2

/-- A slice `z ↦ h ε z` at a positive radius is continuous when `h` is continuous on `(0,∞) × ℂ`. -/
theorem continuous_slice {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (h ε) := by
  have h1 : ContinuousOn (fun z : ℂ => (ε, z)) Set.univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => h ε z) Set.univ :=
    hh.comp h1 fun z _ => ⟨hε, Set.mem_univ z⟩
  exact continuousOn_univ.mp h2

/-- A positive-radius process that is continuous on `(0,∞) × ℂ` is continuous as a function on the product. -/
theorem continuous_circleProc_of_continuousOn {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    Continuous (circleProc h) := by
  have hmap : Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => ((p.1 : ℝ), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact hh.comp_continuous hmap fun p => ⟨p.1.2, Set.mem_univ _⟩

theorem ae_continuous_circleProc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, Continuous (circleProc (hcirc ω)) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  exact continuous_circleProc_of_continuousOn hω

/-! ## Calculus of the log circle average -/

/-- Scaling of the logarithmic circle average: `cavg(log|·|)(R v, R s) = log R + cavg(log|·|)(v, s)`. -/
theorem circleAverage_log_scale {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (v : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) ((R : ℂ) * v) (R * s)
      = Real.log R + Real.circleAverage (fun x => Real.log ‖x‖) v s := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := (R : ℂ) * v)
    (R := R * s) (mul_pos hR hs).ne'
  have h2 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := v) (R := s)
    hs.ne'
  simp only [sub_zero] at h1 h2
  have hn : (R * s)⁻¹ * ‖(R : ℂ) * v‖ = s⁻¹ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    field_simp
  rw [h1, h2, hn, Real.log_mul hR.ne' hs.ne']
  ring

/-- The logarithmic circle average at the origin: `cavg(log|·|)(0, R) = log R`. -/
theorem circleAverage_log_zero {R : ℝ} (hR : 0 < R) :
    Real.circleAverage (fun x => Real.log ‖x‖) 0 R = Real.log R := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := 0) (R := R) hR.ne'
  simp only [sub_zero, norm_zero, mul_zero, Real.posLog_zero, add_zero] at h
  exact h

/-- The circle averages of the affine transform `affH R 0 h` of a field are the affine transform of its
`α`-circle averages, at positive radii. -/
theorem fieldCircleAverage_affH (α : ℝ) {R : ℝ} (hR : 0 < R) (h : ℝ → ℂ → ℝ) {s : ℝ} (hs : 0 < s) (v : ℂ) :
    fieldCircleAverage α (Field.affH R 0 h) s v = Field.affH R 0 (fieldCircleAverage α h) s v := by
  unfold fieldCircleAverage Field.affH
  simp only [add_zero]
  rw [circleAverage_log_scale hR hs v, circleAverage_log_zero hR]
  ring

/-- The `α`-circle average is continuous in the centre at a positive radius, once the slice is continuous. -/
theorem continuous_fieldCircleAverage (α : ℝ) {ε : ℝ} (hε : 0 < ε) {h : ℝ → ℂ → ℝ}
    (hh : Continuous (h ε)) : Continuous (fieldCircleAverage α h ε) := by
  have hcav : ∀ z : ℂ, Real.circleAverage (fun x => Real.log ‖x‖) z ε
      = Real.log ε + Real.posLog (ε⁻¹ * ‖z‖) := by
    intro z
    have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) (R := ε)
      hε.ne'
    simpa only [sub_zero] using h
  have hfun : fieldCircleAverage α h ε
      = fun z => h ε z - α * (Real.log ε + Real.posLog (ε⁻¹ * ‖z‖)) := by
    funext z
    simp only [fieldCircleAverage, hcav z]
  rw [hfun]
  exact hh.sub (continuous_const.mul (continuous_const.add (Real.continuous_posLog.comp
    (continuous_const.mul continuous_norm))))

theorem ae_fieldCircleAverage_continuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  intro ε hε
  exact continuous_fieldCircleAverage α hε (continuous_slice hω hε)

/-! ## Vague limits: congruence and uniqueness -/

/-- Approximation families that agree at positive radii have the same dyadic limits. -/
private theorem isLQGLimit_congr_pos {γ : ℝ} {h₁ h₂ : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (heq : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, h₁ ε z = h₂ ε z) (h : IsLQGLimit γ h₁ m) :
    IsLQGLimit γ h₂ m := by
  refine ⟨h.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  have hk : ∀ k : ℕ, lqgApprox γ h₂ (dyadicScale k) = lqgApprox γ h₁ (dyadicScale k) := by
    intro k
    unfold lqgApprox
    congr 1
    funext z
    rw [heq _ (dyadicScale_pos k) z]
  simp only [hk]
  exact h.tendsto_integral f hf hfc

/-- Dyadic vague limits are unique: two Radon measures with the same `C_c` integrals along the dyadic approximations
coincide. -/
theorem isLQGLimit_unique {γ : ℝ} {h : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ h m) (hm' : IsLQGLimit γ h m') : m = m' := by
  have := hm.isLocallyFiniteMeasure
  have := hm'.isLocallyFiniteMeasure
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  exact tendsto_nhds_unique (hm.tendsto_integral (⇑f) f.continuous f.hasCompactSupport)
    (hm'.tendsto_integral (⇑f) f.continuous f.hasCompactSupport)

/-- The α-field of a positive-radius process has the same dyadic limits as the α-field of the process itself. -/
theorem isLQGLimit_circleProc_iff {γ α : ℝ} {x : ℝ → ℂ → ℝ} {m : Measure ℂ} :
    IsLQGLimit γ (fieldCircleAverage α (procExt (circleProc x))) m ↔ IsLQGLimit γ (fieldCircleAverage α x) m := by
  have heq : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      fieldCircleAverage α (procExt (circleProc x)) ε z = fieldCircleAverage α x ε z := by
    intro ε hε z
    unfold fieldCircleAverage
    rw [procExt_circleProc _ hε]
  exact ⟨isLQGLimit_congr_pos (fun ε hε z => heq ε hε z),
    isLQGLimit_congr_pos (fun ε hε z => (heq ε hε z).symm)⟩

/-! ## The measurable-decoder premise (written constructor not yet formalized) -/

/-- **Premise: measurable dyadic decoder (written constructor pending).** There is a product-measurable map `dec` from
positive-radius processes to measures on `ℂ` which is the dyadic insertion limit on every continuous process that has
one. This is the measurable version `𝓜` of the dyadic limit in the written proof (steps3, paragraph "We need a measurable
way of taking the given dyadic limit"). Only this existence statement is used. Its construction (restriction to a
countable dense set of points, and the Borel convergence set on continuous representatives) is not formalized, so
this is a hypothesis, not a proved object. The premise does not require the decoded set to lie in the continuous
functions. -/
def MeasurableDyadicDecoder (γ α : ℝ) : Prop :=
  ∃ dec : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → Measure ℂ, Measurable dec ∧
    ∀ u : Set.Ioi (0 : ℝ) × ℂ → ℝ, Continuous u →
      (∃ m : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (procExt u)) m) →
      IsLQGLimit γ (fieldCircleAverage α (procExt u)) (dec u)

/-! ## Normalized circle law and the decoded scaling identity -/

/-- The circle process of the normalized field `affHcirc R 0 hcirc` has the law of the circle process of `hcirc`, for
`R > 0` (steps3:520-531, from `Field.wholePlane_circle_law`). -/
theorem circleProc_affine_law {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    P.map (fun ω => circleProc (Field.affHcirc R 0 hcirc ω)) = P.map (fun ω => circleProc (hcirc ω)) :=
  (Field.wholePlane_circle_law hGFF (Field.isWholePlaneGFF_affine hGFF hR 0)).symm

/-- Decoded normalized measures: a.s. the decoded measure of the normalized dyadic circle process is the rescaled
decoded limit, `dec(circ(affHcirc R_n 0 hcirc)) = c_n⁻¹ • (·/R_n)_* μ` (steps3:551-556, eq. dyadic-measure-exact,
here via `Field.isLQGLimit_affine_iff`, with the shift `R_n · 2^{-k} = 2^{-(k+n)}`). -/
theorem dec_affine_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (dec : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → Measure ℂ)
    (hlim : ∀ u : Set.Ioi (0 : ℝ) × ℂ → ℝ, Continuous u →
      (∃ m : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (procExt u)) m) →
      IsLQGLimit γ (fieldCircleAverage α (procExt u)) (dec u)) (n : ℕ) :
    ∀ᵐ ω ∂P, dec (circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω)) =
      ENNReal.ofReal (Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0)⁻¹ •
        (μ ω).map (fun x => (x - 0) / ((dyadicScale n : ℝ) : ℂ)) := by
  have hR : 0 < dyadicScale n := dyadicScale_pos n
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  filter_upwards [hμ', ae_fieldCircleAverage_continuous hGFF α,
    ae_continuous_circleProc (Field.isWholePlaneGFF_affine hGFF hR 0)] with ω h1 h2 h3
  have : IsLocallyFiniteMeasure (μ ω) := h1.isLocallyFiniteMeasure
  have hA : IsLQGLimit γ (Field.affH (dyadicScale n) 0 (fieldCircleAverage α (hcirc ω)))
      (ENNReal.ofReal (Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0)⁻¹ •
        (μ ω).map (fun x => (x - 0) / ((dyadicScale n : ℝ) : ℂ))) := by
    refine (Field.isLQGLimit_affine_iff γ hR 0 (fieldCircleAverage α (hcirc ω)) h2 (μ ω)).2 ?_
    intro g hg hgc
    have hshift : ∀ k : ℕ, dyadicScale n * dyadicScale k = dyadicScale (k + n) := by
      intro k
      rw [dyadicScale, dyadicScale, dyadicScale, pow_add]
      ring
    simp only [hshift]
    exact (tendsto_add_atTop_iff_nat n).2 (h1.tendsto_integral g hg hgc)
  have hB : IsLQGLimit γ (fieldCircleAverage α (Field.affHcirc (dyadicScale n) 0 hcirc ω))
      (ENNReal.ofReal (Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0)⁻¹ •
        (μ ω).map (fun x => (x - 0) / ((dyadicScale n : ℝ) : ℂ))) :=
    isLQGLimit_congr_pos (fun ε hε z => (fieldCircleAverage_affH α hR (hcirc ω) hε z).symm) hA
  have hC' := hlim (circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω)) h3
    ⟨_, isLQGLimit_circleProc_iff.2 hB⟩
  exact isLQGLimit_unique (isLQGLimit_circleProc_iff.1 hC') hB

/-- The rescaled decoded measure has atom mass `c⁻¹ · μ{0}` at the origin, because `(·/R)` fixes `0`. -/
theorem smul_map_div_singleton (c : ℝ≥0∞) (ν : Measure ℂ) {R : ℝ} (hR : R ≠ 0) :
    (c • ν.map (fun x => (x - 0) / ((R : ℝ) : ℂ))) {0} = c * ν {0} := by
  have hpre : (fun x : ℂ => (x - 0) / ((R : ℝ) : ℂ)) ⁻¹' {0} = {0} := by
    ext x
    simp [hR]
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hpre]

/-! ## The dyadic constant and its Gaussian estimate (steps3:557-562) -/

theorem dyadicScale_eq_exp (n : ℕ) : dyadicScale n = Real.exp (-(n * Real.log 2)) := by
  unfold dyadicScale
  rw [show -((n : ℝ) * Real.log 2) = (n : ℝ) * Real.log ((2 : ℝ)⁻¹) by rw [Real.log_inv]; ring,
    Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The insertion constant at `(2^{-n}, 0)` is `exp(γ h_{2^{-n}}(0) - n log 2 · γ(Q - α))`. -/
theorem coordConst_dyadic_eq {γ α : ℝ} (hγ : 0 < γ) (n : ℕ) (H : ℝ → ℂ → ℝ) :
    Field.coordConst γ (dyadicScale n) (fieldCircleAverage α H) 0
      = Real.exp (γ * H (dyadicScale n) 0 - n * Real.log 2 * (γ * (lqgQ γ - α))) := by
  have hpow : (dyadicScale n) ^ (2 + γ ^ 2 / 2) = Real.exp (-(n * Real.log 2) * (2 + γ ^ 2 / 2)) := by
    rw [dyadicScale_eq_exp, ← Real.exp_mul]
  have hlog : Real.log (dyadicScale n) = -(n * Real.log 2) := by
    rw [dyadicScale_eq_exp, Real.log_exp]
  unfold Field.coordConst fieldCircleAverage
  rw [hpow, circleAverage_log_zero (dyadicScale_pos n), hlog, ← Real.exp_add]
  congr 1
  unfold lqgQ
  field_simp
  ring

/-- The one-dimensional law of the circle average at `(2^{-n}, 0)` is `N(0, n log 2)`: the radial process of a
whole-plane GFF is a Brownian motion in `-log r` (`Field.map_radial_eq_brownian`; steps3:557-560). -/
theorem map_circle_dyadic {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (n : ℕ) :
    P.map (fun ω => hcirc ω (dyadicScale n) 0) = gaussianReal 0 (Real.toNNReal (n * Real.log 2)) := by
  have hnn : (0 : ℝ) ≤ n * Real.log 2 := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)
  have htR : ((Real.toNNReal (n * Real.log 2) : ℝ≥0) : ℝ) = n * Real.log 2 := Real.coe_toNNReal _ hnn
  have hrad := Field.map_radial_eq_brownian hGFF
  have hradM : Measurable (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (-(s : ℝ))) 0) :=
    Measurable.of_eval fun s => hGFF.measurable_circle _ _ (Real.exp_pos _)
  have hev : Measurable (fun f : ℝ≥0 → ℝ => f (Real.toNNReal (n * Real.log 2))) := measurable_pi_apply _
  calc P.map (fun ω => hcirc ω (dyadicScale n) 0)
      = P.map ((fun f : ℝ≥0 → ℝ => f (Real.toNNReal (n * Real.log 2))) ∘
          (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (-(s : ℝ))) 0)) := by
        congr 1
        funext ω
        simp only [Function.comp, htR, dyadicScale_eq_exp]
    _ = (P.map (fun ω (s : ℝ≥0) => hcirc ω (Real.exp (-(s : ℝ))) 0)).map
          (fun f : ℝ≥0 → ℝ => f (Real.toNNReal (n * Real.log 2))) :=
        (Measure.map_map hev hradM).symm
    _ = ((brownianMotion 0).map (fun w (s : ℝ≥0) => w s)).map
          (fun f : ℝ≥0 → ℝ => f (Real.toNNReal (n * Real.log 2))) := by rw [hrad]
    _ = (brownianMotion 0).map (fun w => w (Real.toNNReal (n * Real.log 2))) := by
        have hmeasW : Measurable (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s) :=
          Measurable.of_eval fun s => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s
        rw [Measure.map_map hev hmeasW]
        rfl
    _ = gaussianReal 0 (Real.toNNReal (n * Real.log 2)) := brownianMotion_map_eval _ 0

/-- **Chernoff and Borel-Cantelli.** Almost surely, `h_{2^{-n}}(0) < ct · n` for all large `n`, for every `ct > 0`
(steps3:557-562: the Gaussian exponential bound, summed over `n`). -/
theorem ae_eventually_circle_dyadic_lt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {ct : ℝ} (hct : 0 < ct) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, hcirc ω (dyadicScale n) 0 < ct * n := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hκ : 0 < ct ^ 2 / (2 * Real.log 2) := div_pos (pow_pos hct 2) (mul_pos two_pos hL)
  have hq0 : 0 ≤ Real.exp (-(ct ^ 2 / (2 * Real.log 2))) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(ct ^ 2 / (2 * Real.log 2))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hbound : ∀ n : ℕ, P {ω | ct * n ≤ hcirc ω (dyadicScale n) 0}
      ≤ ENNReal.ofReal (Real.exp (-(ct ^ 2 / (2 * Real.log 2))) ^ n) := by
    intro n
    have hnn : (0 : ℝ) ≤ n * Real.log 2 := mul_nonneg (Nat.cast_nonneg n) hL.le
    have hXm : Measurable (fun ω => hcirc ω (dyadicScale n) 0) :=
      hGFF.measurable_circle _ _ (dyadicScale_pos n)
    have hlaw : HasLaw (fun ω => hcirc ω (dyadicScale n) 0)
        (gaussianReal 0 (Real.toNNReal (n * Real.log 2))) P :=
      ⟨hXm.aemeasurable, map_circle_dyadic hGFF n⟩
    have hτ0 : 0 ≤ ct / Real.log 2 := (div_pos hct hL).le
    have hint : Integrable (fun ω => Real.exp (ct / Real.log 2 * hcirc ω (dyadicScale n) 0)) P := by
      have hg : Integrable (fun x : ℝ => Real.exp (ct / Real.log 2 * x))
          (P.map (fun ω => hcirc ω (dyadicScale n) 0)) := by
        rw [hlaw.map_eq]
        exact integrable_exp_mul_gaussianReal (ct / Real.log 2)
      exact (integrable_map_measure hg.aestronglyMeasurable hXm.aemeasurable).1 hg
    have hmgf : mgf (fun ω => hcirc ω (dyadicScale n) 0) P (ct / Real.log 2)
        = Real.exp (0 * (ct / Real.log 2) + (n * Real.log 2) * (ct / Real.log 2) ^ 2 / 2) := by
      rw [mgf_gaussianReal hlaw (ct / Real.log 2), Real.coe_toNNReal _ hnn]
    have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => hcirc ω (dyadicScale n) 0)
      (ct * n) hτ0 hint
    rw [hmgf] at hchern
    have hexp : Real.exp (-(ct / Real.log 2) * (ct * n))
        * Real.exp (0 * (ct / Real.log 2) + (n * Real.log 2) * (ct / Real.log 2) ^ 2 / 2)
        = Real.exp (-(ct ^ 2 / (2 * Real.log 2))) ^ n := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      field_simp
      ring
    calc P {ω | ct * n ≤ hcirc ω (dyadicScale n) 0}
        = ENNReal.ofReal (P.real {ω | ct * n ≤ hcirc ω (dyadicScale n) 0}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
      _ ≤ ENNReal.ofReal (Real.exp (-(ct ^ 2 / (2 * Real.log 2))) ^ n) :=
          ENNReal.ofReal_le_ofReal (hchern.trans hexp.le)
  have hb : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(ct ^ 2 / (2 * Real.log 2))) ^ n) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hq0 n)
      (summable_geometric_of_lt_one hq0 hq1)]
    exact ENNReal.ofReal_ne_top
  have hsum : ∑' n : ℕ, P {ω | ct * n ≤ hcirc ω (dyadicScale n) 0} ≠ ⊤ :=
    ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hbound)
  filter_upwards [ae_eventually_notMem (s := fun n : ℕ => {ω | ct * n ≤ hcirc ω (dyadicScale n) 0}) hsum]
    with ω hω
  exact hω.mono fun n hn => not_le.1 hn

/-- **Dyadic constant tends to zero.** Almost surely `c_n = coordConst γ 2^{-n} h 0 → 0` (steps3:557-562, the
exponent `γ h(2^{-n},0) - n log 2 · γ(Q - α)` with `α < Q`). -/
theorem ae_tendsto_coordConst_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0)
      atTop (𝓝 0) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQα : 0 < lqgQ γ - α := by linarith
  have hctpos : 0 < Real.log 2 * (lqgQ γ - α) / 2 := div_pos (mul_pos hL hQα) two_pos
  have hκpos : 0 < γ * Real.log 2 * (lqgQ γ - α) / 2 := div_pos (mul_pos (mul_pos hγ hL) hQα) two_pos
  filter_upwards [ae_eventually_circle_dyadic_lt hGFF hctpos] with ω hω
  have hsq : Tendsto (fun n : ℕ => Real.exp (-((γ * Real.log 2 * (lqgQ γ - α) / 2) * n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => -((γ * Real.log 2 * (lqgQ γ - α) / 2) * (n : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκpos)
    exact Real.tendsto_exp_atBot.comp h1
  refine squeeze_zero'
    (Eventually.of_forall fun n => (Field.coordConst_pos γ (dyadicScale_pos n) (fieldCircleAverage α (hcirc ω)) 0).le)
    ?_ hsq
  filter_upwards [hω] with n hn
  rw [coordConst_dyadic_eq hγ n (hcirc ω)]
  apply Real.exp_le_exp.2
  have key : γ * (Real.log 2 * (lqgQ γ - α) / 2 * n) - n * Real.log 2 * (γ * (lqgQ γ - α))
      = -((γ * Real.log 2 * (lqgQ γ - α) / 2) * n) := by ring
  linarith [mul_lt_mul_of_pos_left hn hγ]

/-! ## The Fatou argument (steps3:563-585) -/

/-- **Fatou argument.** Let `a` be the atom mass and `b n` the atom masses of the rescaled decoded measures. They have
the same laws as `a`, and `b n = c_n⁻¹ a` with `c_n → 0`, `c_n > 0` almost surely. Then `a = 0` almost surely. -/
theorem atom_vanishing_of_scaling {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a : Ω → ℝ≥0∞) (b : ℕ → Ω → ℝ≥0∞) (c : ℕ → Ω → ℝ)
    (ha : Measurable a)
    (hlaw : ∀ (n : ℕ) (L : ℝ≥0∞), P (b n ⁻¹' Set.Ioi L) = P (a ⁻¹' Set.Ioi L))
    (hfin : ∀ᵐ ω ∂P, a ω ≠ ⊤)
    (hscale : ∀ᵐ ω ∂P, ∀ n, b n ω = ENNReal.ofReal (c n ω)⁻¹ * a ω)
    (hc0 : ∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0))
    (hcpos : ∀ (n : ℕ) (ω : Ω), 0 < c n ω) :
    ∀ᵐ ω ∂P, a ω = 0 := by
  have key : ∀ L : ℕ, P (a ⁻¹' Set.Ioi 0) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := by
    intro L
    let T : ℕ → Set Ω := fun N => ⋂ n, ⋂ (_ : N ≤ n), b n ⁻¹' Set.Ioi (L : ℝ≥0∞)
    have hTmono : Monotone T := by
      intro N M hNM ω hω
      simp only [T, Set.mem_iInter] at hω ⊢
      intro n hn
      exact hω n (hNM.trans hn)
    have hcover : a ⁻¹' Set.Ioi 0 ≤ᵐ[P] ⋃ N, T N := by
      filter_upwards [hfin, hscale, hc0] with ω hfω hsω hcω
      intro hpos
      have hpos' : (0 : ℝ≥0∞) < a ω := hpos
      have h1 : Tendsto (fun n => ENNReal.ofReal (c n ω)⁻¹) atTop (𝓝 ⊤) := by
        have hinv : Tendsto (fun n => (c n ω)⁻¹) atTop atTop :=
          tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hcω, Eventually.of_forall fun n => hcpos n ω⟩)
        exact ENNReal.tendsto_ofReal_atTop.comp hinv
      have h2 : Tendsto (fun n => b n ω) atTop (𝓝 ⊤) := by
        have hfun : (fun n => b n ω) = fun n => ENNReal.ofReal (c n ω)⁻¹ * a ω := funext hsω
        rw [hfun]
        have h3 := ENNReal.Tendsto.mul_const (b := a ω) h1 (Or.inl ENNReal.top_ne_zero)
        rwa [ENNReal.top_mul hpos'.ne'] at h3
      have h4 : ∀ᶠ n in atTop, (L : ℝ≥0∞) < b n ω :=
        h2.eventually_const_lt (ENNReal.natCast_ne_top L).lt_top
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h4
      exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter.2 fun n => Set.mem_iInter.2 fun hn => hN n hn⟩
    have h1 : P (a ⁻¹' Set.Ioi 0) ≤ P (⋃ N, T N) := measure_mono_ae hcover
    have h2 : Tendsto (fun N => P (T N)) atTop (𝓝 (P (⋃ N, T N))) :=
      tendsto_measure_iUnion_atTop (fun N M hNM => hTmono hNM)
    have h3 : ∀ N, P (T N) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := fun N =>
      (measure_mono (fun ω hω => Set.mem_iInter.1 (Set.mem_iInter.1 hω N) le_rfl)).trans (hlaw N L).le
    have h4 : P (⋃ N, T N) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := le_of_tendsto h2 (Eventually.of_forall h3)
    exact h1.trans h4
  have hS : Antitone (fun L : ℕ => a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := by
    intro L M hLM
    exact Set.preimage_mono (Set.Ioi_subset_Ioi (by exact_mod_cast hLM))
  have hlim := tendsto_measure_iInter_atTop (μ := P) (s := fun L : ℕ => a ⁻¹' Set.Ioi (L : ℝ≥0∞))
    (fun L : ℕ => (ha measurableSet_Ioi).nullMeasurableSet) hS ⟨0, measure_ne_top P _⟩
  have hinter : P (⋂ L : ℕ, a ⁻¹' Set.Ioi (L : ℝ≥0∞)) = 0 := by
    apply measure_mono_null (t := {ω | ¬ a ω ≠ ⊤})
    · intro ω hω
      rw [Set.mem_iInter] at hω
      show ¬ a ω ≠ ⊤
      intro hne
      obtain ⟨L, hL⟩ := ENNReal.exists_nat_gt hne
      exact absurd (hω L) (not_lt.2 hL.le)
    · exact ae_iff.1 hfin
  have hzero : P (a ⁻¹' Set.Ioi 0) = 0 := by
    have hle := ge_of_tendsto hlim (Eventually.of_forall key)
    rw [hinter] at hle
    exact nonpos_iff_eq_zero.1 hle
  have hz : P {ω | ¬ a ω = 0} = 0 :=
    measure_mono_null (fun ω hω => pos_iff_ne_zero.2 hω) hzero
  exact ae_iff.2 hz

/-! ## The no-insertion-atom component -/

/-- **No insertion atom at the origin** (steps3:538-585, Lemma `lem:insertion-no-atom`). Under `0 < γ`, `α < Q`, a
whole-plane GFF `(hC, hcirc)` whose insertion-`α` LQG measure is `μ`, and the measurable-decoder premise
`MeasurableDyadicDecoder γ α`, `μ{0} = 0` almost surely. -/
theorem insertion_no_atom_zero_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hdec : MeasurableDyadicDecoder γ α) :
    ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  obtain ⟨dec, hmeas, hlim⟩ := hdec
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hid : ∀ᵐ ω ∂P, μ ω = dec (circleProc (hcirc ω)) := by
    filter_upwards [hμ', ae_continuous_circleProc hGFF] with ω h1 h2
    exact isLQGLimit_unique h1
      (isLQGLimit_circleProc_iff.1 (hlim _ h2 ⟨μ ω, isLQGLimit_circleProc_iff.2 h1⟩))
  let a : Ω → ℝ≥0∞ := fun ω => dec (circleProc (hcirc ω)) {0}
  let b : ℕ → Ω → ℝ≥0∞ := fun n ω => dec (circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω)) {0}
  let c : ℕ → Ω → ℝ := fun n ω => Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0
  have heval : Measurable fun ν : Measure ℂ => ν {0} := Measure.measurable_coe (measurableSet_singleton 0)
  have hdec_map : ∀ X Y : Ω → Set.Ioi (0 : ℝ) × ℂ → ℝ, Measurable X → Measurable Y → P.map X = P.map Y →
      P.map (fun ω => dec (X ω) {0}) = P.map (fun ω => dec (Y ω) {0}) := by
    intro X Y hX hY hXY
    calc P.map (fun ω => dec (X ω) {0})
        = (P.map (dec ∘ X)).map (fun ν : Measure ℂ => ν {0}) :=
          (Measure.map_map heval (hmeas.comp hX)).symm
      _ = ((P.map X).map dec).map (fun ν : Measure ℂ => ν {0}) := by
          rw [Measure.map_map hmeas hX]
      _ = ((P.map Y).map dec).map (fun ν : Measure ℂ => ν {0}) := by rw [hXY]
      _ = (P.map (dec ∘ Y)).map (fun ν : Measure ℂ => ν {0}) := by
          rw [Measure.map_map hmeas hY]
      _ = P.map (fun ω => dec (Y ω) {0}) := Measure.map_map heval (hmeas.comp hY)
  have ha : Measurable a := heval.comp (hmeas.comp (measurable_circleProc hGFF))
  have hb : ∀ n, Measurable (b n) := fun n =>
    heval.comp (hmeas.comp
      (measurable_circleProc (Field.isWholePlaneGFF_affine hGFF (dyadicScale_pos n) 0)))
  have hlaw : ∀ (n : ℕ) (L : ℝ≥0∞), P (b n ⁻¹' Set.Ioi L) = P (a ⁻¹' Set.Ioi L) := by
    intro n L
    have hmap : P.map (b n) = P.map a :=
      hdec_map _ _ (measurable_circleProc (Field.isWholePlaneGFF_affine hGFF (dyadicScale_pos n) 0))
        (measurable_circleProc hGFF) (circleProc_affine_law hGFF (dyadicScale_pos n))
    rw [← Measure.map_apply (hb n) measurableSet_Ioi, ← Measure.map_apply ha measurableSet_Ioi, hmap]
  have hscale : ∀ᵐ ω ∂P, ∀ n, b n ω = ENNReal.ofReal (c n ω)⁻¹ * a ω := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [dec_affine_ae hGFF hμ dec hlim n, hid] with ω h1 h2
    show dec (circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω)) {0}
      = ENNReal.ofReal (Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0)⁻¹
        * dec (circleProc (hcirc ω)) {0}
    rw [h1, smul_map_div_singleton _ _ (dyadicScale_pos n).ne', h2]
  have hfin : ∀ᵐ ω ∂P, a ω ≠ ⊤ := by
    filter_upwards [hμ', hid] with ω h1 h2
    have := h1.isLocallyFiniteMeasure
    show dec (circleProc (hcirc ω)) {0} ≠ ⊤
    rw [← h2]
    exact (isCompact_singleton.measure_lt_top).ne
  have hc0 : ∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0) :=
    ae_tendsto_coordConst_zero hGFF hγ hαQ
  have hcpos : ∀ (n : ℕ) (ω : Ω), 0 < c n ω := fun n ω =>
    Field.coordConst_pos γ (dyadicScale_pos n) (fieldCircleAverage α (hcirc ω)) 0
  have hmain := atom_vanishing_of_scaling a b c ha hlaw hfin hscale hc0 hcpos
  filter_upwards [hmain, hid] with ω h1 h2
  rw [h2]
  exact h1



/-- Harmonicity on an open set `D` in the mean-value sense (Armitage--Gardiner, *Classical Potential Theory*):
`H` is continuous on `D` and equals its circle average over every closed circle contained in `D`. For continuous
functions this is the classical characterization of `Δ H = 0` on `D`. -/
def IsHarmonicOnDisk (D : Set ℂ) (H : ℂ → ℝ) : Prop :=
  ContinuousOn H D ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ D → H z = Real.circleAverage H z r

/-- The insertion remainder `H(z) - α log |z|` of the harmonic part `H` (steps3:609-621: adding `-α log|z|` to the
harmonic remainder). -/
noncomputable def insertionRemainder (α : ℝ) (H : ℂ → ℝ) (z : ℂ) : ℝ :=
  H z - α * Real.log ‖z‖

/-- Circle average of `log |·|` over a circle not meeting `0`: `log |c|` (mean value property of `log |·|` on
`ℂ \ {0}`, Armitage--Gardiner). -/
theorem circleAverage_log_norm_of_lt {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : r < ‖c‖) :
    Real.circleAverage (fun x => Real.log ‖x‖) c r = Real.log ‖c‖ := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := c) (R := r) hr.ne'
  simp only [sub_zero] at h
  have hpos : 1 ≤ r⁻¹ * ‖c‖ := by
    rw [← div_eq_inv_mul, one_le_div hr]
    exact hcr.le
  rw [h]
  unfold Real.posLog
  rw [max_eq_right (Real.log_nonneg hpos), Real.log_mul (inv_ne_zero hr.ne') (lt_trans hr hcr).ne', Real.log_inv]
  ring

/-- On an admissible circle (closed ball avoiding `0`), the insertion circle average is the whole-plane one minus
`α log |z|`. -/
theorem fieldCircleAverage_eq_sub_log_of_closedBall {α r : ℝ} {h : ℝ → ℂ → ℝ} {z : ℂ} (hr : 0 < r)
    (hsub : Metric.closedBall z r ⊆ ({0}ᶜ : Set ℂ)) :
    fieldCircleAverage α h r z = h r z - α * Real.log ‖z‖ := by
  have h0 : (0 : ℂ) ∉ Metric.closedBall z r := fun hm => (Set.mem_compl_singleton_iff.mp (hsub hm)) rfl
  have hlt : r < ‖z‖ := by
    by_contra hcon
    apply h0
    rw [Metric.mem_closedBall, dist_comm, dist_zero_right]
    exact not_lt.mp hcon
  unfold fieldCircleAverage
  rw [circleAverage_log_norm_of_lt hr hlt]

/-- The set of centres whose closed `ε`-ball lies in the open set `D` is open. -/
theorem isOpen_setOf_closedBall_subset {D : Set ℂ} (hD : IsOpen D) {ε : ℝ} (hε : 0 ≤ ε) :
    IsOpen {z : ℂ | Metric.closedBall z ε ⊆ D} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open hD hz
  rw [cthickening_closedBall hδ.le hε] at hsub
  refine ⟨δ, hδ, fun z' hz' w hw => hsub ?_⟩
  rw [Metric.mem_closedBall]
  have h1 : dist w z' ≤ ε := Metric.mem_closedBall.mp hw
  have h2 : dist z' z < δ := Metric.mem_ball.mp hz'
  calc dist w z ≤ dist w z' + dist z' z := dist_triangle _ _ _
    _ ≤ δ + ε := by linarith

/-- Uniform admissibility on a compact set: for `K ⊆ D` compact, `D` open, small closed balls around `K` lie in `D`. -/
theorem exists_closedBall_subset_of_compact {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 ≤ ε → ε < δ → Metric.closedBall z ε ⊆ D := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hD hKD
  refine ⟨δ, hδ, fun z hz ε hε hεδ w hw => hsub ?_⟩
  exact Metric.mem_cthickening_of_dist_le w z δ K hz (by
    have := Metric.mem_closedBall.mp hw
    linarith)

/-- Measurability in `z` of a zero-boundary circle average, from its continuity on admissible circles and its
vanishing on non-admissible ones (`IsDirichletGFF.continuous_circle` plus the zero-outside convention). -/
theorem measurable_zeroBoundary_circle {D : Set ℂ} (hD : IsOpen D) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℂ → ℝ} (hzero : ∀ r z, ¬ Metric.closedBall z r ⊆ D → g r z = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => g p.1 p.2) {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}) :
    Measurable (g ε) := by
  classical
  have hAo := isOpen_setOf_closedBall_subset hD hε.le
  have hmap : Continuous fun z : ℂ => ((ε, z) : ℝ × ℂ) := continuous_const.prodMk continuous_id
  have hcA : ContinuousOn (g ε) {z : ℂ | Metric.closedBall z ε ⊆ D} :=
    hcont.comp hmap.continuousOn (fun z hz => ⟨hε, hz⟩)
  have hfun : g ε = {z : ℂ | Metric.closedBall z ε ⊆ D}.piecewise (g ε) (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ {z : ℂ | Metric.closedBall z ε ⊆ D}
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      exact hzero ε z hz
  rw [hfun]
  exact ContinuousOn.measurable_piecewise hcA continuousOn_const hAo.measurableSet

/-- Integral against an LQG approximation as a Lebesgue integral with continuous-type density. -/
theorem integral_lqgApprox_eq {γ ε : ℝ} (hε : 0 < ε) {g : ℝ → ℂ → ℝ} (hgm : Measurable (g ε)) (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ g ε) = ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z) * f z := by
  unfold lqgApprox
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hgm)))
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  have hnn : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z) := by positivity
  rw [smul_eq_mul, ENNReal.toReal_ofReal hnn]

/-- The multiplier `exp(t · (H - α log|·|))` is continuous on `D` when `H` is continuous on `D` and `0 ∉ D`. -/
theorem continuousOn_exp_mul_insertionRemainder {D : Set ℂ} {α t : ℝ} {H : ℂ → ℝ} (hH : ContinuousOn H D)
    (hD0 : D ⊆ ({0}ᶜ : Set ℂ)) :
    ContinuousOn (fun z => Real.exp (t * insertionRemainder α H z)) D := by
  have hL : ContinuousOn (fun z : ℂ => Real.log ‖z‖) D :=
    ContinuousOn.log continuous_norm.continuousOn (fun z hz => norm_ne_zero_iff.mpr (hD0 hz))
  have hR : ContinuousOn (insertionRemainder α H) D := by
    unfold insertionRemainder
    exact hH.sub (continuousOn_const.mul hL)
  exact Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hR)

/-- Multiplying a continuous compactly supported function by a function continuous on an open set `D` that contains
its support gives a continuous function on the whole plane. -/
theorem continuous_mul_of_tsupport_subset {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ} (hf : Continuous f)
    (hfD : tsupport f ⊆ D) (hg : ContinuousOn g D) : Continuous fun z => f z * g z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ D
  · exact (hf.continuousAt).mul (hg.continuousAt (hD.mem_nhds hz))
  · have hzf : z ∉ tsupport f := fun h => hz (hfD h)
    have hev : (fun z => f z * g z) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hzf] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
    exact continuousAt_const.congr hev.symm

/-- Pushing `μ|_D` through the density `exp(-γ · (H - α log|·|))` and integrating a test function `f` vanishing off
`D` gives the whole-plane integral of `f · exp(-γ · remainder)` against `μ`. -/
theorem integral_withDensity_restrict_insertion {D : Set ℂ} (hD : IsOpen D) (μ : Measure ℂ) {α γ : ℝ} {H : ℂ → ℝ}
    (hH : ContinuousOn H D) (hD0 : D ⊆ ({0}ᶜ : Set ℂ)) (f : ℂ → ℝ) (hf : ∀ z, z ∉ D → f z = 0) :
    ∫ z, f z ∂((μ.restrict D).withDensity fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α H z))))
      = ∫ z, f z * Real.exp (-(γ * insertionRemainder α H z)) ∂μ := by
  have hc : ContinuousOn (fun z => Real.exp (-(γ * insertionRemainder α H z))) D := by
    simpa only [neg_mul] using continuousOn_exp_mul_insertionRemainder (t := -γ) hH hD0
  have hae : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α H z))))
      (μ.restrict D) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hD.measurableSet
  rw [integral_withDensity_eq_integral_toReal_smul₀ hae (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  have hG : ∀ z, (ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α H z)))).toReal • f z
      = f z * Real.exp (-(γ * insertionRemainder α H z)) := by
    intro z
    rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
  simp only [hG]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hf z hz])


/-- **Local Dirichlet/harmonic decomposition: producer residual** (steps3:609-621, the written paragraph; not a published
result). For a disk `B(c, ρ)` with `closedBall c ρ ⊆ ℂ \ {0}` and a whole-plane GFF `(hC, hcirc)` on `Ω`, there are a
zero-boundary Dirichlet GFF `(h0, hcirc0)` on the disk, vanishing on non-admissible circles (the representative
convention of `SheffieldWangCircleAverageAllScaleStmt`), and a random function `H` such that almost surely `H` is
harmonic on the disk (`IsHarmonicOnDisk`, which contains the continuity used for the multiplier) and
`hcirc ω r z = hcirc0 ω r z + H ω z` for every admissible circle. The Gaussian Dirichlet projection gives this on an
arbitrary probability space (steps3:609-621). It is not formalized and enters only as this named hypothesis. -/
def LocalDirichletHarmonicDecompositionStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ) →
    ∃ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0 ∧
      (∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0) ∧
      ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
        ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z

/-- **Local finiteness of the zero-boundary limit: unwritten residual (GAP).** steps3:603-625 applies Sheffield--Wang
Theorem 1.1 to the zero-boundary field on `D = B(c, ρ)`, whose limit is `exp(-γ · remainder) · μ|_D`. The staged
statement `SheffieldWangCircleAverageAllScaleStmt` (Proposed/SheffieldWang2016.lean) requires `IsLocallyFiniteMeasure`
of its supplied limit on all of `ℂ`, i.e. `∫_D exp(-γ (H - α log|·|)) dμ < ∞`, the total mass of the zero-boundary
Gaussian multiplicative chaos. The written paragraph does not state this finiteness. It is carried here as a named
hypothesis and is not a published result.

Superseded for the interior chain: `punctured_disk_allScales_interior` and `punctured_allScales_of_steps_interior` do not
take this residual. The finiteness they need is only on compact subsets of `D` and is derived from the locally finite
insertion measure (`ae_zeroBoundaryLimit_compact_lt_top`), with the compact-interior staged statement
`SheffieldWangCircleAverageAllScaleInteriorStmt`. This declaration is kept for `punctured_disk_allScales` and
`punctured_allScales_of_steps`, which keep the global form. -/
def ZeroBoundaryLimitLocallyFiniteStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α : ℝ),
    0 < γ → γ < 2 → α < lqgQ γ →
    ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
    ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ) →
    ∀ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0 →
      (∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
        ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z) →
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (((μ ω).restrict (Metric.ball c ρ)).withDensity
        fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))

/-- Density identity on an admissible circle (steps3:609-621, deterministic part): where the whole-plane circle
averages split as zero-boundary ones plus `H` on the admissible circles of radius `ε`, the insertion approximation of
`f` equals the zero-boundary approximation of `f · exp(γ · remainder)`. -/
theorem integral_insertion_eq_zeroBoundary {D : Set ℂ} (hD0 : D ⊆ ({0}ᶜ : Set ℂ)) {α γ ε : ℝ} (hε : 0 < ε)
    {hc hc0 : ℝ → ℂ → ℝ} {H : ℂ → ℝ} (hmeasIns : Measurable (fieldCircleAverage α hc ε))
    (hmeas0 : Measurable (hc0 ε))
    (hrel : ∀ z, Metric.closedBall z ε ⊆ D → hc ε z = hc0 ε z + H z)
    (f : ℂ → ℝ) (hK : ∀ z ∈ tsupport f, Metric.closedBall z ε ⊆ D) :
    ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α hc) ε)
      = ∫ z, f z * Real.exp (γ * insertionRemainder α H z) ∂(lqgApprox γ hc0 ε) := by
  rw [integral_lqgApprox_eq hε hmeasIns f,
    integral_lqgApprox_eq hε hmeas0 (fun z => f z * Real.exp (γ * insertionRemainder α H z))]
  congr 1
  funext z
  by_cases hz : z ∈ tsupport f
  · have hball := hK z hz
    have hsub : Metric.closedBall z ε ⊆ ({0}ᶜ : Set ℂ) := hball.trans hD0
    rw [fieldCircleAverage_eq_sub_log_of_closedBall hε hsub, hrel z hball]
    have key : Real.exp (γ * (hc0 ε z + H z - α * Real.log ‖z‖))
        = Real.exp (γ * hc0 ε z) * Real.exp (γ * insertionRemainder α H z) := by
      rw [← Real.exp_add]
      congr 1
      unfold insertionRemainder
      ring
    rw [key]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

/-- Linearity of an LQG approximation integral over a finite decomposition `f = ∑ φ i` into continuous compactly
supported pieces (continuous density). -/
theorem integral_lqgApprox_finset {γ ε : ℝ} (hε : 0 < ε) {g : ℝ → ℂ → ℝ} (hgc : Continuous (g ε))
    {ι : Type} [Fintype ι] (φ : ι → ℂ → ℝ) (hφc : ∀ i, Continuous (φ i)) (hφs : ∀ i, HasCompactSupport (φ i))
    (f : ℂ → ℝ) (hf : ∀ z, f z = ∑ i, φ i z) :
    ∫ z, f z ∂(lqgApprox γ g ε) = ∑ i, ∫ z, φ i z ∂(lqgApprox γ g ε) := by
  have hdens : Continuous fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hgc))
  rw [integral_lqgApprox_eq hε hgc.measurable f]
  simp only [integral_lqgApprox_eq hε hgc.measurable]
  have hsum : (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z) * f z)
      = fun z => ∑ i, ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ε z) * φ i z := by
    funext z
    rw [hf z, Finset.mul_sum]
  rw [hsum]
  exact integral_finsetSum _ (fun i _ => (hdens.mul (hφc i)).integrable_of_hasCompactSupport ((hφs i).mul_left))

/-- Linearity of an integral against a locally finite measure over a finite decomposition into continuous compactly
supported pieces. -/
theorem integral_finset_compactSupport {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] {ι : Type} [Fintype ι]
    (φ : ι → ℂ → ℝ) (hφc : ∀ i, Continuous (φ i)) (hφs : ∀ i, HasCompactSupport (φ i)) (f : ℂ → ℝ)
    (hf : ∀ z, f z = ∑ i, φ i z) : ∫ z, f z ∂ν = ∑ i, ∫ z, φ i z ∂ν := by
  have hfe : f = fun z => ∑ i, φ i z := funext hf
  rw [hfe]
  exact integral_finsetSum _ (fun i _ => (hφc i).integrable_of_hasCompactSupport (hφs i))

/-- For `x : ℝ`, `exp(-x) · exp(x) = 1`. -/
theorem exp_neg_mul_exp_self (x : ℝ) : Real.exp (-x) * Real.exp x = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **Punctured all-scale convergence on one disk** (steps3:603-625, the written argument). Given the zero-boundary
decomposition of the insertion field on `D = B(c, ρ)` (the producer residual, as data), the staged Sheffield--Wang
statement applied to the zero-boundary field, and the local finiteness of the zero-boundary limit (`hfin`, named
residual), the insertion approximations converge along all scales on every test function supported in `D`, to `μ`. -/
theorem punctured_disk_allScales {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hSW : SheffieldWangCircleAverageAllScaleStmt.{0})
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcl : Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ))
    {h0 : Ω → (ℂ → ℝ) → ℝ} {hcirc0 : Ω → ℝ → ℂ → ℝ} {H : Ω → ℂ → ℝ}
    (hDir : IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0)
    (hzero : ∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0)
    (hdec : ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z)
    (hfin : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω))
    (hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε)) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := by
  have hD : IsOpen (Metric.ball c ρ) := Metric.isOpen_ball
  have hD0 : Metric.ball c ρ ⊆ ({0}ᶜ : Set ℂ) := Metric.ball_subset_closedBall.trans hcl
  have hDne : Metric.ball c ρ ≠ univ := fun h =>
    NormedSpace.unbounded_univ ℝ ℂ (by rw [← h]; exact Metric.isBounded_ball)
  have : ContractibleSpace (Metric.ball c ρ) :=
    (convex_ball c ρ).contractibleSpace ⟨c, Metric.mem_ball_self hρ⟩
  have : SimplyConnectedSpace (Metric.ball c ρ) := SimplyConnectedSpace.ofContractible _
  -- Dyadic hypothesis of the staged statement for the zero-boundary limit `exp(-γ·remainder) · μ|_D`.
  have hSWhyp : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hcirc0 ω) (dyadicScale n))) atTop
          (𝓝 (∫ z, f z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
            fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))))) := by
    filter_upwards [hfin, hdec, hμ, hcont, hDir.continuous_circle] with ω hfinω hdecω hμω hcontω hcontD0
    refine ⟨hfinω, fun f hf hfc hfD => ?_⟩
    have hHc := hdecω.1.1
    have hfsupp : ∀ z, z ∉ Metric.ball c ρ → f z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h => hz (hfD h))
    have hexpc : ContinuousOn (fun z => Real.exp (-(γ * insertionRemainder α (H ω) z))) (Metric.ball c ρ) := by
      simpa only [neg_mul] using continuousOn_exp_mul_insertionRemainder (t := -γ) hHc hD0
    let F : ℂ → ℝ := fun z => f z * Real.exp (-(γ * insertionRemainder α (H ω) z))
    have hFc : Continuous F := continuous_mul_of_tsupport_subset hD hf hfD hexpc
    have hFs : HasCompactSupport F := hfc.mul_right
    obtain ⟨δ, hδ, hball⟩ := exists_closedBall_subset_of_compact hD hfc.isCompact hfD
    have hdyadic : Tendsto (fun n : ℕ => dyadicScale n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ := (tendsto_order.1 hdyadic).2 δ hδ
    have hlim := hμω.tendsto_integral F hFc hFs
    rw [integral_withDensity_restrict_insertion hD (μ ω) hHc hD0 f hfsupp]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hev] with n hn
    have hεpos : 0 < dyadicScale n := by unfold dyadicScale; positivity
    have hK : ∀ z ∈ tsupport F, Metric.closedBall z (dyadicScale n) ⊆ Metric.ball c ρ :=
      fun z hz => hball z (tsupport_mul_subset_left hz) _ hεpos.le hn
    have hid := integral_insertion_eq_zeroBoundary (γ := γ) hD0 hεpos ((hcontω _ hεpos).measurable)
      (measurable_zeroBoundary_circle hD hεpos (fun r z => hzero ω r z) hcontD0)
      (fun z hz => hdecω.2 _ z hεpos hz) F hK
    rw [hid]
    congr 1
    funext z
    show f z * Real.exp (-(γ * insertionRemainder α (H ω) z)) * Real.exp (γ * insertionRemainder α (H ω) z) = f z
    rw [mul_assoc, exp_neg_mul_exp_self, mul_one]
  have hSWall := hSW Ω P (Metric.ball c ρ) h0 hcirc0
    (fun ω => ((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))
    γ hD hDne inferInstance Metric.isBounded_ball hDir hγ.le hγ2 hzero hSWhyp
  filter_upwards [hSWall, hdec, hμ, hcont, hDir.continuous_circle] with ω hSWω hdecω hμω hcontω hcontD0
  intro f hf hfc hfD
  have hHc := hdecω.1.1
  have hfsupp : ∀ z, z ∉ Metric.ball c ρ → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hfD h))
  have hexpc : ContinuousOn (fun z => Real.exp (γ * insertionRemainder α (H ω) z)) (Metric.ball c ρ) :=
    continuousOn_exp_mul_insertionRemainder (t := γ) hHc hD0
  let g : ℂ → ℝ := fun z => f z * Real.exp (γ * insertionRemainder α (H ω) z)
  have hgc : Continuous g := continuous_mul_of_tsupport_subset hD hf hfD hexpc
  have hgs : HasCompactSupport g := hfc.mul_right
  have hgD : tsupport g ⊆ Metric.ball c ρ := (tsupport_mul_subset_left).trans hfD
  have hlim := hSWω g hgc hgs hgD
  have hgμ : ∫ z, g z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))
      = ∫ z, f z ∂(μ ω) := by
    rw [integral_withDensity_restrict_insertion hD (μ ω) hHc hD0 g (fun z hz => by
      show f z * Real.exp (γ * insertionRemainder α (H ω) z) = 0
      rw [hfsupp z hz, zero_mul])]
    congr 1
    funext z
    show f z * Real.exp (γ * insertionRemainder α (H ω) z) * Real.exp (-(γ * insertionRemainder α (H ω) z))
      = f z
    linear_combination (f z) * exp_neg_mul_exp_self (γ * insertionRemainder α (H ω) z)
  obtain ⟨δf, hδf, hballf⟩ := exists_closedBall_subset_of_compact hD hfc.isCompact hfD
  have heq : (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ z, g z ∂(lqgApprox γ (hcirc0 ω) ε)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (neg_lt_zero.2 hδf) hδf)] with ε hε1 hε2
    have hεpos : 0 < ε := hε1
    exact integral_insertion_eq_zeroBoundary hD0 hεpos ((hcontω ε hεpos).measurable)
      (measurable_zeroBoundary_circle hD hεpos (fun r z => hzero ω r z) hcontD0)
      (fun z hz => hdecω.2 ε z hεpos hz) f (fun z hz => hballf z hz ε hεpos.le hε2.2)
  rw [← hgμ]
  exact Tendsto.congr' heq.symm hlim

/-! ## Rational disks covering `ℂ \ {0}` (steps3:603-625: "a countable cover of `ℂ \ {0}`") -/

/-- Centre `a + b i` of the rational disk indexed by `p = (a, b, r)`. -/
def ratCenter (p : ℚ × ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩

/-- Radius `r` of the rational disk indexed by `p = (a, b, r)`. -/
def ratRadius (p : ℚ × ℚ × ℚ) : ℝ := (p.2.2 : ℝ)

/-- Admissible rational disks: `0 < r < |c|`, so that the closed disk avoids `0`. -/
def RatDiskAdmissible (p : ℚ × ℚ × ℚ) : Prop := 0 < ratRadius p ∧ ratRadius p < ‖ratCenter p‖

/-- Countable index set of the admissible rational disks. -/
abbrev RatDiskIdx := {p : ℚ × ℚ × ℚ // RatDiskAdmissible p}

theorem ratDisk_closedBall_subset (p : RatDiskIdx) :
    Metric.closedBall (ratCenter p.1) (ratRadius p.1) ⊆ ({0}ᶜ : Set ℂ) := by
  intro w hw hw0
  have hw0' : w = 0 := Set.mem_singleton_iff.mp hw0
  have h1 : dist w (ratCenter p.1) ≤ ratRadius p.1 := Metric.mem_closedBall.mp hw
  rw [hw0', dist_zero_left] at h1
  exact absurd h1 (not_le.mpr p.2.2)

/-- Every nonzero point lies in an admissible rational disk. -/
theorem exists_ratDisk_mem {z : ℂ} (hz : z ≠ 0) :
    ∃ p : RatDiskIdx, z ∈ Metric.ball (ratCenter p.1) (ratRadius p.1) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ‖z‖ / 4 < ‖z‖ / 2 by linarith)
  have hr0 : (0 : ℝ) < r := lt_trans (by linarith) hr1
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - (r : ℝ) / 4 < z.re + (r : ℝ) / 4 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - (r : ℝ) / 4 < z.im + (r : ℝ) / 4 by linarith)
  set c : ℂ := ⟨(a : ℝ), (b : ℝ)⟩ with hc
  have hA : |z.re - a| < (r : ℝ) / 4 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hB : |z.im - b| < (r : ℝ) / 4 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hzc : ‖z - c‖ ≤ |z.re - a| + |z.im - b| := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - c)
    have hre : (z - c).re = z.re - a := by simp [hc]
    have him : (z - c).im = z.im - b := by simp [hc]
    rw [hre, him] at h
    exact h
  have hlt : (r : ℝ) < ‖c‖ := by
    have h := norm_add_le (z - c) c
    rw [sub_add_cancel] at h
    linarith
  refine ⟨⟨(a, b, r), ⟨hr0, hlt⟩⟩, ?_⟩
  show z ∈ Metric.ball c (r : ℝ)
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- **Punctured all-scale convergence (steps3:603-625).** Assuming the staged Sheffield--Wang statement (read-only),
the local Dirichlet/harmonic decomposition (producer residual `LocalDirichletHarmonicDecompositionStep`), and the local
finiteness of the zero-boundary limit (named gap residual `ZeroBoundaryLimitLocallyFiniteStep`), almost surely the
insertion approximations converge along all scales on every continuous compactly supported test function on `ℂ \ {0}`,
with limit the insertion measure `μ`. The limit of the all-scale family is identified with `μ` on `ℂ \ {0}`. -/
theorem punctured_allScales_of_steps {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hWP : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hSW : SheffieldWangCircleAverageAllScaleStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep)
    (hFin : ZeroBoundaryLimitLocallyFiniteStep) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ ({0}ᶜ : Set ℂ) →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε) :=
    ae_fieldCircleAverage_continuous hWP α
  have hall : ∀ p : RatDiskIdx, ∃ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball (ratCenter p.1) (ratRadius p.1)) h0 hcirc0 ∧
      (∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) → hcirc0 ω r z = 0) ∧
      ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball (ratCenter p.1) (ratRadius p.1)) (H ω) ∧
        ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) →
          hcirc ω r z = hcirc0 ω r z + H ω z :=
    fun p => hDec Ω P hC hcirc hWP (ratCenter p.1) (ratRadius p.1) p.2.1 (ratDisk_closedBall_subset p)
  choose h0 hcirc0 H hDir hzero hdec using hall
  have hper : ∀ p : RatDiskIdx, ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := fun p =>
    punctured_disk_allScales hγ hγ2 hSW p.2.1 (ratDisk_closedBall_subset p) (hDir p) (hzero p) (hdec p)
      (hFin Ω P γ α hγ hγ2 hαQ hC hcirc μ hWP hμ (ratCenter p.1) (ratRadius p.1) p.2.1
        (ratDisk_closedBall_subset p) (h0 p) (hcirc0 p) (H p) (hDir p) (hdec p))
      hμ' hcont
  have hall_ae := ae_all_iff.2 hper
  filter_upwards [hall_ae, hμ', hcont] with ω hω hμω hcontω
  intro f hf hfc hfsupp
  have hK : IsCompact (tsupport f) := hfc.isCompact
  have hcover : tsupport f ⊆ ⋃ p : RatDiskIdx, Metric.ball (ratCenter p.1) (ratRadius p.1) := by
    intro z hz
    obtain ⟨p, hp⟩ := exists_ratDisk_mem (fun h => hfsupp hz h)
    exact Set.mem_iUnion.2 ⟨p, hp⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun p : RatDiskIdx => Metric.ball (ratCenter p.1) (ratRadius p.1)) (fun p => Metric.isOpen_ball) hcover
  let idx : Fin t.card → RatDiskIdx := fun i => (t.equivFin.symm i : RatDiskIdx)
  obtain ⟨χ, hχsub, hχsum, -, hχcpt⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (s := fun i : Fin t.card => Metric.ball (ratCenter (idx i).1) (ratRadius (idx i).1))
    (fun i => Metric.isOpen_ball) hK (by
      intro z hz
      obtain ⟨p, hpt, hzp⟩ := Set.mem_iUnion₂.mp (ht hz)
      refine Set.mem_iUnion.2 ⟨t.equivFin ⟨p, hpt⟩, ?_⟩
      simpa [idx] using hzp)
  let φ : Fin t.card → ℂ → ℝ := fun i z => f z * χ i z
  have hφc : ∀ i, Continuous (φ i) := fun i => hf.mul (χ i).continuous
  have hφs : ∀ i, HasCompactSupport (φ i) := fun i => hfc.mul_right
  have hφsub : ∀ i, tsupport (φ i) ⊆ Metric.ball (ratCenter (idx i).1) (ratRadius (idx i).1) :=
    fun i => (tsupport_mul_subset_right).trans (hχsub i)
  have hfsum : ∀ z, f z = ∑ i, φ i z := by
    intro z
    by_cases hz : z ∈ tsupport f
    · have h1 : ∑ i, χ i z = 1 := by
        have := hχsum hz
        simpa [ContinuousMap.sum_apply] using this
      calc f z = f z * ∑ i, χ i z := by rw [h1, mul_one]
        _ = ∑ i, φ i z := by rw [Finset.mul_sum]
    · simp [φ, image_eq_zero_of_notMem_tsupport hz]
  have hlimμ : ∫ z, f z ∂(μ ω) = ∑ i, ∫ z, φ i z ∂(μ ω) := by
    have : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
    have : IsFiniteMeasureOnCompacts (μ ω) := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    exact integral_finset_compactSupport φ hφc hφs f hfsum
  have hsumT : Tendsto (fun ε : ℝ => ∑ i, ∫ z, φ i z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε))
      (𝓝[>] 0) (𝓝 (∑ i, ∫ z, φ i z ∂(μ ω))) :=
    tendsto_finsetSum _ (fun i _ => hω (idx i) (φ i) (hφc i) (hφs i) (hφsub i))
  rw [hlimμ]
  refine Tendsto.congr' ?_ hsumT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_lqgApprox_finset (γ := γ) hε (hcontω ε hε) φ hφc hφs f hfsum).symm

/-! ## Compact-interior form of the zero-boundary limit (steps3:603-625)

The zero-boundary limit `ν = (μ|_D).withDensity (exp(-γ · remainder))` on `D = B(c, ρ)` is finite on compact subsets
of `D`: the density is continuous on `D`, hence bounded on each compact subset, and `μ` is locally finite. It is not
claimed to be finite on all of `ℂ`, so `ZeroBoundaryLimitLocallyFiniteStep` is not used by the interior consumers
below, and no total mass of `ν` on `D` is asserted. -/

/-- Finiteness on compact subsets of `D` for a density `ofReal ∘ φ` with `φ` continuous on `D` (deterministic). On a
compact `K ⊆ D` the density is bounded by `ofReal M`, `M = sup_K |φ|`, so `(μ|_D).withDensity (ofReal ∘ φ)` charges
`K` with at most `ofReal M * μ K`. No finiteness near `∂D` is claimed. -/
theorem withDensity_restrict_compact_lt_top {D K : Set ℂ} {μ : Measure ℂ} {φ : ℂ → ℝ}
    (hK : IsCompact K) (hKD : K ⊆ D) (hφ : ContinuousOn φ D) (hμK : μ K < ⊤) :
    ((μ.restrict D).withDensity fun z => ENNReal.ofReal (φ z)) K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
  have hbound : ∀ x ∈ K, ENNReal.ofReal (φ x) ≤ ENNReal.ofReal M := fun x hx => by
    have h := hM x hx
    rw [Real.norm_eq_abs] at h
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans h)
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (φ z) ∂(μ.restrict D)
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(μ.restrict D) :=
        setLIntegral_mono' hK.isClosed.measurableSet hbound
    _ = ENNReal.ofReal M * μ K := by
        rw [setLIntegral_const, Measure.restrict_apply hK.isClosed.measurableSet,
          Set.inter_eq_left.2 hKD]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK

/-- Almost surely, the zero-boundary limit `(μ|_D).withDensity (exp(-γ · remainder))` is finite on every compact
subset of `D`. Source: the insertion measure is locally finite (`IsLQGLimit.isLocallyFiniteMeasure`) and the harmonic
remainder `H` is continuous on `D`. -/
theorem ae_zeroBoundaryLimit_compact_lt_top {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Set ℂ} (hD0 : D ⊆ ({0}ᶜ : Set ℂ))
    {H : Ω → ℂ → ℝ} (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω))
    (hH : ∀ᵐ ω ∂P, ContinuousOn (H ω) D) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ D →
      ((μ ω).restrict D).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))) K < ⊤ := by
  filter_upwards [hμ, hH] with ω hμω hHω
  have : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have : IsFiniteMeasureOnCompacts (μ ω) := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  intro K hK hKD
  have hc : ContinuousOn (fun z => Real.exp (-(γ * insertionRemainder α (H ω) z))) D := by
    simpa only [neg_mul] using continuousOn_exp_mul_insertionRemainder (t := -γ) hHω hD0
  exact withDensity_restrict_compact_lt_top hK hKD hc hK.measure_lt_top

/-- Dyadic compact-test limit of the zero-boundary limit `ν` on `D = B(c, ρ)` (steps3:603-625, the written
multiplication argument): almost surely, `∫ f d(lqgApprox γ hcirc0 (dyadicScale n)) → ∫ f dν` for every continuous
compactly supported `f` with support in `D`. It uses the insertion limit, the admissible-circle identity and the
harmonicity of `H`; no finiteness beyond that of the insertion measure is assumed. -/
theorem ae_zeroBoundary_dyadic_compactTest {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {c : ℂ} {ρ : ℝ}
    (hD : IsOpen (Metric.ball c ρ)) (hD0 : Metric.ball c ρ ⊆ ({0}ᶜ : Set ℂ))
    {h0 : Ω → (ℂ → ℝ) → ℝ} {hcirc0 : Ω → ℝ → ℂ → ℝ} {H : Ω → ℂ → ℝ}
    (hDir : IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0)
    (hzero : ∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0)
    (hdec : ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z)
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω))
    (hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε)) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
      Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hcirc0 ω) (dyadicScale n))) atTop
        (𝓝 (∫ z, f z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
          fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))))) := by
  filter_upwards [hdec, hμ, hcont, hDir.continuous_circle] with ω hdecω hμω hcontω hcontD0
  intro f hf hfc hfD
  have hHc := hdecω.1.1
  have hfsupp : ∀ z, z ∉ Metric.ball c ρ → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hfD h))
  have hexpc : ContinuousOn (fun z => Real.exp (-(γ * insertionRemainder α (H ω) z))) (Metric.ball c ρ) := by
    simpa only [neg_mul] using continuousOn_exp_mul_insertionRemainder (t := -γ) hHc hD0
  let F : ℂ → ℝ := fun z => f z * Real.exp (-(γ * insertionRemainder α (H ω) z))
  have hFc : Continuous F := continuous_mul_of_tsupport_subset hD hf hfD hexpc
  have hFs : HasCompactSupport F := hfc.mul_right
  obtain ⟨δ, hδ, hball⟩ := exists_closedBall_subset_of_compact hD hfc.isCompact hfD
  have hdyadic : Tendsto (fun n : ℕ => dyadicScale n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ := (tendsto_order.1 hdyadic).2 δ hδ
  have hlim := hμω.tendsto_integral F hFc hFs
  rw [integral_withDensity_restrict_insertion hD (μ ω) hHc hD0 f hfsupp]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [hev] with n hn
  have hεpos : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hK : ∀ z ∈ tsupport F, Metric.closedBall z (dyadicScale n) ⊆ Metric.ball c ρ :=
    fun z hz => hball z (tsupport_mul_subset_left hz) _ hεpos.le hn
  have hid := integral_insertion_eq_zeroBoundary (γ := γ) hD0 hεpos ((hcontω _ hεpos).measurable)
    (measurable_zeroBoundary_circle hD hεpos (fun r z => hzero ω r z) hcontD0)
    (fun z hz => hdecω.2 _ z hεpos hz) F hK
  rw [hid]
  congr 1
  funext z
  show f z * Real.exp (-(γ * insertionRemainder α (H ω) z)) * Real.exp (γ * insertionRemainder α (H ω) z) = f z
  rw [mul_assoc, exp_neg_mul_exp_self, mul_one]

/-- Transfer of the zero-boundary convergence to the insertion field on `D = B(c, ρ)` (steps3:603-625, the written
argument): on the event of the zero-boundary convergence, the insertion approximation of `f` equals the zero-boundary
approximation of `f · exp(γ · remainder)` along admissible circles, and the continuous positive factor
`exp(±γ · remainder)` preserves convergence for test functions supported in `D`. -/
theorem ae_insertion_conv_of_zeroBoundary {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {c : ℂ} {ρ : ℝ}
    (hD : IsOpen (Metric.ball c ρ)) (hD0 : Metric.ball c ρ ⊆ ({0}ᶜ : Set ℂ))
    {h0 : Ω → (ℂ → ℝ) → ℝ} {hcirc0 : Ω → ℝ → ℂ → ℝ} {H : Ω → ℂ → ℝ}
    (hDir : IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0)
    (hzero : ∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0)
    (hdec : ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z)
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω))
    (hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε))
    (hSWall : ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (hcirc0 ω) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
          fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))))) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := by
  filter_upwards [hSWall, hdec, hμ, hcont, hDir.continuous_circle] with ω hSWω hdecω hμω hcontω hcontD0
  intro f hf hfc hfD
  have hHc := hdecω.1.1
  have hfsupp : ∀ z, z ∉ Metric.ball c ρ → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hfD h))
  have hexpc : ContinuousOn (fun z => Real.exp (γ * insertionRemainder α (H ω) z)) (Metric.ball c ρ) :=
    continuousOn_exp_mul_insertionRemainder (t := γ) hHc hD0
  let g : ℂ → ℝ := fun z => f z * Real.exp (γ * insertionRemainder α (H ω) z)
  have hgc : Continuous g := continuous_mul_of_tsupport_subset hD hf hfD hexpc
  have hgs : HasCompactSupport g := hfc.mul_right
  have hgD : tsupport g ⊆ Metric.ball c ρ := (tsupport_mul_subset_left).trans hfD
  have hlim := hSWω g hgc hgs hgD
  have hgμ : ∫ z, g z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))
      = ∫ z, f z ∂(μ ω) := by
    rw [integral_withDensity_restrict_insertion hD (μ ω) hHc hD0 g (fun z hz => by
      show f z * Real.exp (γ * insertionRemainder α (H ω) z) = 0
      rw [hfsupp z hz, zero_mul])]
    congr 1
    funext z
    show f z * Real.exp (γ * insertionRemainder α (H ω) z) * Real.exp (-(γ * insertionRemainder α (H ω) z))
      = f z
    linear_combination (f z) * exp_neg_mul_exp_self (γ * insertionRemainder α (H ω) z)
  obtain ⟨δf, hδf, hballf⟩ := exists_closedBall_subset_of_compact hD hfc.isCompact hfD
  have heq : (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ z, g z ∂(lqgApprox γ (hcirc0 ω) ε)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (neg_lt_zero.2 hδf) hδf)] with ε hε1 hε2
    have hεpos : 0 < ε := hε1
    exact integral_insertion_eq_zeroBoundary hD0 hεpos ((hcontω ε hεpos).measurable)
      (measurable_zeroBoundary_circle hD hεpos (fun r z => hzero ω r z) hcontD0)
      (fun z hz => hdecω.2 ε z hεpos hz) f (fun z hz => hballf z hz ε hεpos.le hε2.2)
  rw [← hgμ]
  exact Tendsto.congr' heq.symm hlim

/-- **Punctured all-scale convergence on one disk, compact-interior form (steps3:603-625).** Assuming the
compact-interior Sheffield--Wang statement `SheffieldWangCircleAverageAllScaleInteriorStmt` (staged in Proposed/,
read-only here), the zero-boundary decomposition of the insertion field on `D = B(c, ρ)` as data, and the insertion
limit `μ`, the insertion approximations converge along all scales on every test function supported in `D`. The
finiteness of the zero-boundary limit is derived on compact subsets of `D` (`ae_zeroBoundaryLimit_compact_lt_top`);
`ZeroBoundaryLimitLocallyFiniteStep` is not used, and no finiteness on `ℂ` or total mass on `D` is assumed. -/
theorem punctured_disk_allScales_interior {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcl : Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ))
    {h0 : Ω → (ℂ → ℝ) → ℝ} {hcirc0 : Ω → ℝ → ℂ → ℝ} {H : Ω → ℂ → ℝ}
    (hDir : IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0)
    (hzero : ∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0)
    (hdec : ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z)
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω))
    (hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε)) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := by
  have hD : IsOpen (Metric.ball c ρ) := Metric.isOpen_ball
  have hD0 : Metric.ball c ρ ⊆ ({0}ᶜ : Set ℂ) := Metric.ball_subset_closedBall.trans hcl
  have hDne : Metric.ball c ρ ≠ univ := fun h =>
    NormedSpace.unbounded_univ ℝ ℂ (by rw [← h]; exact Metric.isBounded_ball)
  have : ContractibleSpace (Metric.ball c ρ) :=
    (convex_ball c ρ).contractibleSpace ⟨c, Metric.mem_ball_self hρ⟩
  have : SimplyConnectedSpace (Metric.ball c ρ) := SimplyConnectedSpace.ofContractible _
  have hSWhyp : ∀ᵐ ω ∂P, (∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball c ρ →
      ((μ ω).restrict (Metric.ball c ρ)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))) K < ⊤) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Metric.ball c ρ →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hcirc0 ω) (dyadicScale n))) atTop
          (𝓝 (∫ z, f z ∂(((μ ω).restrict (Metric.ball c ρ)).withDensity
            fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z)))))) := by
    filter_upwards [ae_zeroBoundaryLimit_compact_lt_top hD0 hμ (hdec.mono fun ω hω => hω.1.1),
      ae_zeroBoundary_dyadic_compactTest hD hD0 hDir hzero hdec hμ hcont] with ω hfinω hdyω
    exact ⟨hfinω, hdyω⟩
  have hSWall := hSWI Ω P (Metric.ball c ρ) h0 hcirc0
    (fun ω => ((μ ω).restrict (Metric.ball c ρ)).withDensity
      fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))
    γ hD hDne inferInstance Metric.isBounded_ball hDir hγ.le hγ2 hzero hSWhyp
  exact ae_insertion_conv_of_zeroBoundary hD hD0 hDir hzero hdec hμ hcont hSWall

/-- **Punctured all-scale convergence, compact-interior form (steps3:603-625).** Given the compact-interior
Sheffield--Wang statement `SheffieldWangCircleAverageAllScaleInteriorStmt` (read-only) and the local Dirichlet/harmonic
decomposition `LocalDirichletHarmonicDecompositionStep` (producer residual, carried explicitly), almost surely the
insertion approximations converge along all scales on every continuous compactly supported test function on `ℂ \ {0}`,
with limit the insertion measure `μ`. This replaces `punctured_allScales_of_steps` in the chain: it takes no
`ZeroBoundaryLimitLocallyFiniteStep`. -/
theorem punctured_allScales_of_steps_interior {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hWP : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ ({0}ᶜ : Set ℂ) →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hcont : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fieldCircleAverage α (hcirc ω) ε) :=
    ae_fieldCircleAverage_continuous hWP α
  have hall : ∀ p : RatDiskIdx, ∃ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball (ratCenter p.1) (ratRadius p.1)) h0 hcirc0 ∧
      (∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) → hcirc0 ω r z = 0) ∧
      ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball (ratCenter p.1) (ratRadius p.1)) (H ω) ∧
        ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) →
          hcirc ω r z = hcirc0 ω r z + H ω z :=
    fun p => hDec Ω P hC hcirc hWP (ratCenter p.1) (ratRadius p.1) p.2.1 (ratDisk_closedBall_subset p)
  choose h0 hcirc0 H hDir hzero hdec using hall
  have hper : ∀ p : RatDiskIdx, ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ Metric.ball (ratCenter p.1) (ratRadius p.1) →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε)) (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ ω))) := fun p =>
    punctured_disk_allScales_interior hγ hγ2 hSWI p.2.1 (ratDisk_closedBall_subset p) (hDir p) (hzero p)
      (hdec p) hμ' hcont
  have hall_ae := ae_all_iff.2 hper
  filter_upwards [hall_ae, hμ', hcont] with ω hω hμω hcontω
  intro f hf hfc hfsupp
  have hK : IsCompact (tsupport f) := hfc.isCompact
  have hcover : tsupport f ⊆ ⋃ p : RatDiskIdx, Metric.ball (ratCenter p.1) (ratRadius p.1) := by
    intro z hz
    obtain ⟨p, hp⟩ := exists_ratDisk_mem (fun h => hfsupp hz h)
    exact Set.mem_iUnion.2 ⟨p, hp⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun p : RatDiskIdx => Metric.ball (ratCenter p.1) (ratRadius p.1)) (fun p => Metric.isOpen_ball) hcover
  let idx : Fin t.card → RatDiskIdx := fun i => (t.equivFin.symm i : RatDiskIdx)
  obtain ⟨χ, hχsub, hχsum, -, hχcpt⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (s := fun i : Fin t.card => Metric.ball (ratCenter (idx i).1) (ratRadius (idx i).1))
    (fun i => Metric.isOpen_ball) hK (by
      intro z hz
      obtain ⟨p, hpt, hzp⟩ := Set.mem_iUnion₂.mp (ht hz)
      refine Set.mem_iUnion.2 ⟨t.equivFin ⟨p, hpt⟩, ?_⟩
      simpa [idx] using hzp)
  let φ : Fin t.card → ℂ → ℝ := fun i z => f z * χ i z
  have hφc : ∀ i, Continuous (φ i) := fun i => hf.mul (χ i).continuous
  have hφs : ∀ i, HasCompactSupport (φ i) := fun i => hfc.mul_right
  have hφsub : ∀ i, tsupport (φ i) ⊆ Metric.ball (ratCenter (idx i).1) (ratRadius (idx i).1) :=
    fun i => (tsupport_mul_subset_right).trans (hχsub i)
  have hfsum : ∀ z, f z = ∑ i, φ i z := by
    intro z
    by_cases hz : z ∈ tsupport f
    · have h1 : ∑ i, χ i z = 1 := by
        have := hχsum hz
        simpa [ContinuousMap.sum_apply] using this
      calc f z = f z * ∑ i, χ i z := by rw [h1, mul_one]
        _ = ∑ i, φ i z := by rw [Finset.mul_sum]
    · simp [φ, image_eq_zero_of_notMem_tsupport hz]
  have hlimμ : ∫ z, f z ∂(μ ω) = ∑ i, ∫ z, φ i z ∂(μ ω) := by
    have : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
    have : IsFiniteMeasureOnCompacts (μ ω) := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    exact integral_finset_compactSupport φ hφc hφs f hfsum
  have hsumT : Tendsto (fun ε : ℝ => ∑ i, ∫ z, φ i z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) ε))
      (𝓝[>] 0) (𝓝 (∑ i, ∫ z, φ i z ∂(μ ω))) :=
    tendsto_finsetSum _ (fun i _ => hω (idx i) (φ i) (hφc i) (hφs i) (hφsub i))
  rw [hlimμ]
  refine Tendsto.congr' ?_ hsumT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_lqgApprox_finset (γ := γ) hε (hcontω ε hε) φ hφc hφs f hfsum).symm

end MatedCRT
