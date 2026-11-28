import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps

/-!
# Shimura's Lemma 2 on a gap `[b, b + d]`

`ShimuraLemmaTwo γ` bounds from below the probability of a four-part event on the unit interval
`[0, 1]` for every `γ`-correlated Brownian pair.  Recentring a path at the time `b` and scaling time by `d`
and space by `√d` maps a `γ`-correlated law to a `γ`-correlated law
(`isCorrelatedBM2_map_recenterPath`, `isCorrelatedBM2_map_unitRescalePath`), so the same bound holds for
the corresponding event on the gap `[b, b + d]`, with the thresholds `Δ √d`, `δ √d` and `√d`
(`exists_le_measure_gap`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open LatticeProb.CorrelatedBM (recenterPath continuous_recenterPath
  isCorrelatedBM2_map_recenterPath)
open MatedCRTHarmonic.MesoModel (unitRescalePath measurable_unitRescalePath
  isCorrelatedBM2_map_unitRescalePath)

/-- Recentre at `b` and rescale so that the gap `[b, b + d]` becomes `[0, 1]`. -/
private noncomputable def gapMap (b d : ℝ) (p : Path2) : Path2 :=
  unitRescalePath d (recenterPath b 1 p)

private lemma measurable_gapMap (b d : ℝ) : Measurable (gapMap b d) :=
  (measurable_unitRescalePath _).comp (continuous_recenterPath _ _).measurable

private lemma isCorrelatedBM2_map_gapMap {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (b : ℝ) {d : ℝ} (hd : 0 < d) : IsCorrelatedBM2 γ (μ.map (gapMap b d)) := by
  have h := isCorrelatedBM2_map_unitRescalePath hd (isCorrelatedBM2_map_recenterPath hμ b 1 (by simp))
  rwa [Measure.map_map (measurable_unitRescalePath _) (continuous_recenterPath _ _).measurable] at h

private lemma gapMap_fst (b d : ℝ) (p : Path2) (u : ℝ) :
    (gapMap b d p u).1 = (Real.sqrt d)⁻¹ * ((p (b + 1 * (d * u))).1 - (p b).1) := rfl

private lemma gapMap_snd (b d : ℝ) (p : Path2) (u : ℝ) :
    (gapMap b d p u).2 = (Real.sqrt d)⁻¹ * ((p (b + 1 * (d * u))).2 - (p b).2) := rfl

private lemma isClosed_forall_mem (S : Set ℝ) (P : ℝ → Path2 → Prop)
    (h : ∀ s, IsClosed {p : Path2 | P s p}) : IsClosed {p : Path2 | ∀ s ∈ S, P s p} := by
  have : {p : Path2 | ∀ s ∈ S, P s p} = ⋂ s ∈ S, {p : Path2 | P s p} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
  rw [this]
  exact isClosed_biInter fun s _ => h s

/-- The event of `ShimuraLemmaTwo` is closed, hence measurable. -/
private lemma measurableSet_lemmaTwoEvent (Δ δ : ℝ) :
    MeasurableSet {p : Path2 | (∀ s ∈ Icc (0 : ℝ) 1, -Δ ≤ (p s).2 - (p 0).2) ∧
      1 ≤ (p 1).2 - (p 0).2 ∧ (∀ s ∈ Icc (0 : ℝ) 1, (p 1).1 - δ ≤ (p s).1) ∧
      (p 1).1 - (p 0).1 ≤ -1} := by
  have hev : Continuous fun q : Path2 × ℝ => q.1 q.2 := ContinuousEval.continuous_eval
  have hp : ∀ t : ℝ, Continuous fun p : Path2 => p t := fun t =>
    hev.comp (continuous_id.prodMk continuous_const)
  have h1 : ∀ t : ℝ, Continuous fun p : Path2 => (p t).1 := fun t => continuous_fst.comp (hp t)
  have h2 : ∀ t : ℝ, Continuous fun p : Path2 => (p t).2 := fun t => continuous_snd.comp (hp t)
  refine (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))).measurableSet
  · exact isClosed_forall_mem _ _ fun s => isClosed_le continuous_const ((h2 s).sub (h2 0))
  · exact isClosed_le continuous_const ((h2 1).sub (h2 0))
  · exact isClosed_forall_mem _ _ fun s => isClosed_le (((h1 1).sub continuous_const)) (h1 s)
  · exact isClosed_le ((h1 1).sub (h1 0)) continuous_const

/-- **Shimura's Lemma 2 on a gap.** If the unit-interval bound `ShimuraLemmaTwo γ` holds, then for every
`γ`-correlated law, every gap `[b, b + d]` and every `0 < Δ, δ ≤ 1`, with probability at least `c Δ δ`:
the second coordinate stays above its starting value minus `Δ √d` on the gap and ends above it plus `√d`,
while the first coordinate stays above its final value minus `δ √d` and ends below its starting value minus
`√d`. -/
theorem exists_le_measure_gap {γ : ℝ} (hL2 : ShimuraLemmaTwo γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ b d Δ δ : ℝ, 0 < d → 0 < Δ →
      Δ ≤ 1 → 0 < δ → δ ≤ 1 →
        ENNReal.ofReal (c * Δ * δ) ≤
          μ {p | (∀ s ∈ Icc b (b + d), (p b).2 - Δ * Real.sqrt d ≤ (p s).2) ∧
            (p b).2 + Real.sqrt d ≤ (p (b + d)).2 ∧
            (∀ s ∈ Icc b (b + d), (p (b + d)).1 - δ * Real.sqrt d ≤ (p s).1) ∧
            (p (b + d)).1 ≤ (p b).1 - Real.sqrt d} := by
  obtain ⟨c, hc, h⟩ := hL2
  refine ⟨c, hc, fun μ hμ b d Δ δ hd hΔ hΔ1 hδ hδ1 => ?_⟩
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hmain := h _ (isCorrelatedBM2_map_gapMap hμ b hd) Δ δ hΔ hΔ1 hδ hδ1
  rw [Measure.map_apply (measurable_gapMap b d) (measurableSet_lemmaTwoEvent Δ δ)] at hmain
  refine hmain.trans (measure_mono ?_)
  rintro p ⟨e1, e2, e3, e4⟩
  -- the points of the gap correspond to the points of the unit interval
  have hpt : ∀ s ∈ Icc b (b + d), ∃ u ∈ Icc (0 : ℝ) 1, b + 1 * (d * u) = s := by
    intro s hs
    have hcancel : d * ((s - b) / d) = s - b := by field_simp
    refine ⟨(s - b) / d, ⟨div_nonneg (by linarith [hs.1]) hd.le, ?_⟩, ?_⟩
    · rw [div_le_one hd]
      linarith [hs.2]
    · rw [one_mul, hcancel]
      ring
  have h0 : b + 1 * (d * 0) = b := by ring
  have h1' : b + 1 * (d * 1) = b + d := by ring
  have hinv : ∀ X : ℝ, Real.sqrt d * ((Real.sqrt d)⁻¹ * X) = X := fun X =>
    mul_inv_cancel_left₀ hr.ne' X
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hpt s hs
    have := e1 u hu
    rw [gapMap_snd, gapMap_snd, h0, sub_self, mul_zero, sub_zero] at this
    have := mul_le_mul_of_nonneg_left this hr.le
    rw [hinv] at this
    nlinarith
  · have := e2
    rw [gapMap_snd, gapMap_snd, h0, h1', sub_self, mul_zero, sub_zero] at this
    have := mul_le_mul_of_nonneg_left this hr.le
    rw [hinv] at this
    nlinarith
  · obtain ⟨u, hu, rfl⟩ := hpt s hs
    have := e3 u hu
    rw [gapMap_fst, gapMap_fst, h1'] at this
    have := mul_le_mul_of_nonneg_left this hr.le
    have e5 := hinv ((p (b + d)).1 - (p b).1)
    have e6 := hinv ((p (b + 1 * (d * u))).1 - (p b).1)
    nlinarith
  · have := e4
    rw [gapMap_fst, gapMap_fst, h0, h1', sub_self, mul_zero, sub_zero] at this
    have := mul_le_mul_of_nonneg_left this hr.le
    rw [hinv] at this
    nlinarith

end MatedCRT.PeanosphereTriplePoints
