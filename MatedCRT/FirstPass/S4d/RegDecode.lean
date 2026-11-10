import MatedCRT.FirstPass.S4d.JumpProxy

/-!
# Decoding regular open sets from countably many coordinates (FIRST PASS, S4d, B2 part I)

For an open regular open set `U ⊆ ℂ` (`interior (closure U) = U`, Armitage-Gardiner Section 1.3) membership is
decided by countably many coordinates: `w ∈ U` iff some closed ball `closedBall p r`, `p ∈ D` (a countable dense set)
and `r ∈ ℚ_{>0}`, contains `w` and is contained in `U`, and the containment `closedBall p r ⊆ U` is the countable
condition `ProxySub D U p r` (`JumpProxy`). This is the decoder used for the measurable whole-process representatives
(ChatGPT answer, §3, steps 3.2-3.3, operator 01:12). Everything is deterministic except the measurability lemma.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- Membership in a regular open set is decided by countably many closed-ball tests. -/
theorem mem_iff_proxy_of_regular {D U : Set ℂ} (hD : Dense D) (hU : IsOpen U)
    (hreg : interior (closure U) = U) (w : ℂ) :
    w ∈ U ↔ ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ w ∈ closedBall p (r : ℝ) ∧ ProxySub D U p (r : ℝ) := by
  constructor
  · intro hw
    obtain ⟨K, hK, hwK, hKU⟩ := ratBallCover_cover hD U hU w hw
    obtain ⟨⟨p, r⟩, ⟨hpD, hr⟩, rfl⟩ := hK
    refine ⟨p, hpD, r, hr, hwK, ?_⟩
    exact (closedBall_subset_iff_proxy hD hU hreg (by exact_mod_cast le_of_lt hr)).1 hKU
  · rintro ⟨p, _, r, hr, hwK, hpr⟩
    exact (closedBall_subset_iff_proxy hD hU hreg (by exact_mod_cast le_of_lt hr)).2 hpr hwK

/-- The decoded membership event `{ω | w ω ∈ U ω}` (for a measurable point `w ω`) is measurable, as a countable union of
measurable events, whenever the coordinates `{ω | d ∈ U ω}`, `d ∈ D`, are measurable. No regularity is needed for
measurability of this decoded event. -/
theorem measurableSet_exists_proxy {Ω : Type*} [MeasurableSpace Ω] {D : Set ℂ} (hDc : D.Countable)
    {U : Ω → Set ℂ} (hU : ∀ d ∈ D, MeasurableSet {ω | d ∈ U ω}) {w : Ω → ℂ} (hw : Measurable w) :
    MeasurableSet {ω | ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧
      ProxySub D (U ω) p (r : ℝ)} := by
  have hcountD : Countable D := hDc.to_subtype
  have hpr : ∀ (p : ℂ) (r : ℚ), MeasurableSet {ω | 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧
      ProxySub D (U ω) p (r : ℝ)} := by
    intro p r
    by_cases hr : 0 < r
    · have hset : {ω | 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧ ProxySub D (U ω) p (r : ℝ)} =
          {ω | w ω ∈ closedBall p (r : ℝ)} ∩ {ω | ProxySub D (U ω) p (r : ℝ)} := by
        ext ω
        simp only [hr, true_and, mem_inter_iff, mem_ofPred_eq]
      rw [hset]
      exact (hw measurableSet_closedBall).inter (measurableSet_proxySub hDc hU p (r : ℝ))
    · have hset : {ω | 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧ ProxySub D (U ω) p (r : ℝ)} = ∅ := by
        ext ω
        simp [hr]
      rw [hset]
      exact MeasurableSet.empty
  have heq : {ω | ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧
      ProxySub D (U ω) p (r : ℝ)} =
      ⋃ p ∈ D, ⋃ r : ℚ, {ω | 0 < r ∧ w ω ∈ closedBall p (r : ℝ) ∧ ProxySub D (U ω) p (r : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq]
  exact MeasurableSet.biUnion hDc fun p _ => MeasurableSet.iUnion fun r => hpr p r

/-- The preimage of a regular open set under `x ↦ R x` (`R ≠ 0`) is regular open (the homeomorphism
`Homeomorph.mulLeft₀`). Used for the rescaled slices `R⁻¹ Λ_{bt}` (`rescaledFamily`). -/
theorem isRegularOpen_preimage_mul {U : Set ℂ} (hU : IsOpen U) (hreg : interior (closure U) = U)
    {R : ℝ} (hR : R ≠ 0) :
    IsOpen ((fun x : ℂ => (R : ℂ) * x) ⁻¹' U) ∧
      interior (closure ((fun x : ℂ => (R : ℂ) * x) ⁻¹' U)) = (fun x : ℂ => (R : ℂ) * x) ⁻¹' U := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  let h : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (R : ℂ) hR'
  have hh : (fun x : ℂ => (R : ℂ) * x) = ⇑h := rfl
  refine ⟨hU.preimage (continuous_const.mul continuous_id), ?_⟩
  rw [hh, ← h.preimage_closure, ← h.preimage_interior, hreg]

end MatedCRT
