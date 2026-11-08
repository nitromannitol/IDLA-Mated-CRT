import MatedCRT.Proofs.Field.WholePlaneAffine
import MatedCRT.Proofs.Field.WholePlaneCircleLaw
import MatedCRT.Proofs.Field.WholePlaneLQGCoord
import MatedCRT.Proofs.Field.WholePlaneBrownian
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

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
theorem isLQGLimit_congr_pos {γ : ℝ} {h₁ h₂ : ℝ → ℂ → ℝ} {m : Measure ℂ}
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

end MatedCRT
