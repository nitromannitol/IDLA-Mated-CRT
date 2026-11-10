import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S4d.JumpProxy

/-!
# Strict gap of a good family: proxy form and cone rescaling (FIRST PASS, S4d, deterministic part of B1)

Helper for `StrictGapFixedTimeUnionStep` (`StrictGapReduction.lean`). A family `U : ℝ → Set ℂ` is *good* when it is
increasing on `(0, ∞)` and each `U s`, `s > 0`, is a regular open set (Armitage-Gardiner, Section 1.3; conditions
(a)-(b) of `HarmonicBalls.SatisfiesHarmonicBallConditions`). For a good family the strict gap
`U t ≠ ⋃_{0<s<t} U s` has the countable-coordinate proxy form of `JumpProxy`, and the cone rescaling
`x ↦ R x`, `t ↦ b t` (`rescaledFamily`, eq:quantum-cone-scaling) carries the strict gap at `t` to the strict gap at
`b t`. Everything here is deterministic; no external input.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- A family is *good* when it is increasing on `(0, ∞)` and each `U s`, `s > 0`, is regular open. -/
def GoodFamily (U : ℝ → Set ℂ) : Prop :=
  MonotoneOn U (Ioi 0) ∧ (∀ s : ℝ, 0 < s → IsOpen (U s)) ∧
    ∀ s : ℝ, 0 < s → interior (closure (U s)) = U s

/-- The section `{x | p (s, x)}` at time `s` of a Prop-valued process `p : ℝ × ℂ → Prop` (Lemma 2.6 notation). -/
def famOf (p : ℝ × ℂ → Prop) (s : ℝ) : Set ℂ :=
  {x | p (s, x)}

/-- The proxy strict gap at time `t` of a Prop-valued process: some countable-coordinate ball `ProxySub D` of the
section at `t` is in no section at a rational earlier time. -/
def ProxyJumpPred (D : Set ℂ) (t : ℝ) (p : ℝ × ℂ → Prop) : Prop :=
  ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ ProxySub D (famOf p t) q r ∧
    ∀ s : ℚ, 0 < (s : ℝ) → (s : ℝ) < t → ¬ ProxySub D (famOf p s) q r

/-- The almost sure cone-family property gives a good family (conditions (a)-(b) and the harmonic ball property). -/
theorem goodFamily_of_isConeHarmonicBallFamily {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (h : IsConeHarmonicBallFamily μ Λ) : GoodFamily Λ := by
  obtain ⟨hball, hcond, -⟩ := h
  exact ⟨hcond.monotoneOn, fun s hs => (hball s hs).1, fun s hs => hcond.isRegularOpen s hs⟩

theorem famOf_globalFamilyProcess {U : ℝ → Set ℂ} {s : ℝ} (hs : 0 < s) :
    famOf (globalFamilyProcess U) s = U s := by
  ext x
  simp [famOf, globalFamilyProcess, hs]

/-- The strict gap of a good family in proxy form (countable dense `D`). -/
theorem strictGap_iff_proxyJump {U : ℝ → Set ℂ} (hU : GoodFamily U) {D : Set ℂ} (hD : Dense D) {t : ℝ}
    (ht : 0 < t) :
    U t ≠ ⋃ s ∈ Ioo (0 : ℝ) t, U s ↔ ProxyJumpPred D t (globalFamilyProcess U) := by
  obtain ⟨hmono, hopen, hreg⟩ := hU
  rw [strictGap_jump_iff_proxy ht hmono hopen hreg hD]
  unfold ProxyJumpPred
  rw [famOf_globalFamilyProcess ht]
  refine exists_congr fun q => and_congr_right fun _ => exists_congr fun r =>
    and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun s =>
      imp_congr_right fun hs0 => imp_congr_right fun _ => ?_
  rw [famOf_globalFamilyProcess hs0]

/-- The proxy strict gap is a measurable event of the Prop-valued process (coordinates `p (s, d)`, `d ∈ D`). -/
theorem measurableSet_proxyJumpPred {D : Set ℂ} (hDc : D.Countable) (t : ℝ) :
    MeasurableSet {p : ℝ × ℂ → Prop | ProxyJumpPred D t p} := by
  have hU : ∀ s : ℝ, ∀ d ∈ D, MeasurableSet {p : ℝ × ℂ → Prop | d ∈ famOf p s} := by
    intro s d _
    exact measurableSet_setOfPred.2 (measurable_pi_apply (s, d))
  exact measurableSet_strictGapProxyEvent (U := fun p s => famOf p s) hDc hU t

/-- Cone rescaling `U ↦ rescaledFamily U R b` (`R ≠ 0`, `b > 0`) preserves goodness. -/
theorem goodFamily_rescaledFamily {U : ℝ → Set ℂ} (hU : GoodFamily U) {R b : ℝ} (hR : R ≠ 0) (hb : 0 < b) :
    GoodFamily (rescaledFamily U R b) := by
  obtain ⟨hmono, hopen, hreg⟩ := hU
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  refine ⟨fun s hs s' hs' hss' x hx => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · exact hmono (mul_pos hb hs) (mul_pos hb hs') (mul_le_mul_of_nonneg_left hss' hb.le) hx
  · exact (hopen (b * s) (mul_pos hb hs)).preimage (continuous_const.mul continuous_id)
  · let h : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (R : ℂ) hR'
    have hh : (fun x : ℂ => (R : ℂ) * x) = ⇑h := rfl
    show interior (closure ((fun x : ℂ => (R : ℂ) * x) ⁻¹' U (b * s))) =
      (fun x : ℂ => (R : ℂ) * x) ⁻¹' U (b * s)
    rw [hh, ← h.preimage_closure, ← h.preimage_interior, hreg (b * s) (mul_pos hb hs)]

/-- The strict gap at `t` of the rescaled family is the strict gap at `b t` of the original one (`R ≠ 0`, `b > 0`). -/
theorem rescaled_strictGap_iff {U : ℝ → Set ℂ} {R b t : ℝ} (hR : R ≠ 0) (hb : 0 < b) :
    rescaledFamily U R b t ≠ ⋃ s ∈ Ioo (0 : ℝ) t, rescaledFamily U R b s ↔
      U (b * t) ≠ ⋃ u ∈ Ioo (0 : ℝ) (b * t), U u := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hsurj : Function.Surjective (fun x : ℂ => (R : ℂ) * x) := fun y =>
    ⟨(R : ℂ)⁻¹ * y, mul_inv_cancel_left₀ hR' y⟩
  have hW : (⋃ s ∈ Ioo (0 : ℝ) t, U (b * s)) = ⋃ u ∈ Ioo (0 : ℝ) (b * t), U u := by
    ext x
    simp only [mem_iUnion, exists_prop, mem_Ioo]
    constructor
    · rintro ⟨s, ⟨hs0, hst⟩, hx⟩
      exact ⟨b * s, ⟨mul_pos hb hs0, mul_lt_mul_of_pos_left hst hb⟩, hx⟩
    · rintro ⟨u, ⟨hu0, hut⟩, hx⟩
      refine ⟨u / b, ⟨div_pos hu0 hb, (div_lt_iff₀ hb).2 (by linarith [mul_comm b t])⟩, ?_⟩
      have e : b * (u / b) = u := by field_simp
      rw [e]
      exact hx
  have hL : (⋃ s ∈ Ioo (0 : ℝ) t, rescaledFamily U R b s) =
      (fun x : ℂ => (R : ℂ) * x) ⁻¹' (⋃ u ∈ Ioo (0 : ℝ) (b * t), U u) := by
    rw [← hW, preimage_iUnion₂]
    rfl
  have hinj : Function.Injective (Set.preimage (fun x : ℂ => (R : ℂ) * x)) := hsurj.preimage_injective
  show (fun x : ℂ => (R : ℂ) * x) ⁻¹' U (b * t) ≠ ⋃ s ∈ Ioo (0 : ℝ) t, rescaledFamily U R b s ↔ _
  rw [hL]
  exact hinj.ne_iff

end MatedCRT
