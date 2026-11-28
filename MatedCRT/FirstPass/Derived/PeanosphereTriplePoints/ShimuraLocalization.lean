import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps

/-!
# Localization of the opposite-side minimum property

Let `μ` be the law of a two-sided correlated Brownian pair `(L, R)` and let
`UnitOppositeSideMin X Y` say that some time of `[0, 1]` is a minimum of `X` on the preceding
window of length `2` and of `Y`
on the following window of length `2`.  If this event is null for every correlated Brownian law,
then almost surely no time `t` is a minimum of `L` on a left neighbourhood and of `R` on a right
neighbourhood, and likewise with the roles of the two coordinates exchanged.

* The set of paths violating `NoOppositeSideMin L R` is covered by the countably many events
  "a time of `[m 2⁻ʳ, (m + 1) 2⁻ʳ]` is a minimum of `L` on the preceding window of length `2 ⁻ʳ⁺¹`
  and of `R` on the following one", for `r ∈ ℕ` and `m ∈ ℤ`.
* Each such event is the preimage of the unit event under the map that recentres the path at
  `m 2⁻ʳ` and rescales time by `2⁻ʳ` and space by `2^{r/2}`.  This map carries a correlated
  Brownian law to a correlated Brownian law, so the event is null.
* The order `(R, L)` follows from the order `(L, R)` applied to the time-reversed path.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open LatticeProb.CorrelatedBM (recenterPath continuous_recenterPath
  isCorrelatedBM2_map_recenterPath)
open MatedCRTHarmonic.MesoModel (unitRescalePath measurable_unitRescalePath
  isCorrelatedBM2_map_unitRescalePath)

/-- Recentre at `m 2⁻ʳ` and rescale so that the mesh `2⁻ʳ` becomes `1`. -/
private noncomputable def dyadicMap (r : ℕ) (m : ℤ) (p : Path2) : Path2 :=
  unitRescalePath ((1 / 2 : ℝ) ^ r) (recenterPath ((m : ℝ) * (1 / 2 : ℝ) ^ r) 1 p)

private lemma measurable_dyadicMap (r : ℕ) (m : ℤ) : Measurable (dyadicMap r m) :=
  (measurable_unitRescalePath _).comp (continuous_recenterPath _ _).measurable

private lemma isCorrelatedBM2_map_dyadicMap {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (r : ℕ) (m : ℤ) :
    IsCorrelatedBM2 γ (μ.map (dyadicMap r m)) := by
  have h := isCorrelatedBM2_map_unitRescalePath (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) r)
    (isCorrelatedBM2_map_recenterPath hμ ((m : ℝ) * (1 / 2 : ℝ) ^ r) 1 (by simp))
  rwa [Measure.map_map (measurable_unitRescalePath _) (continuous_recenterPath _ _).measurable]
    at h

private lemma dyadicMap_fst (r : ℕ) (m : ℤ) (p : Path2) (u : ℝ) :
    (dyadicMap r m p u).1 = (Real.sqrt ((1 / 2 : ℝ) ^ r))⁻¹ *
      ((p ((m : ℝ) * (1 / 2 : ℝ) ^ r + 1 * ((1 / 2 : ℝ) ^ r * u))).1 -
        (p ((m : ℝ) * (1 / 2 : ℝ) ^ r)).1) := rfl

private lemma dyadicMap_snd (r : ℕ) (m : ℤ) (p : Path2) (u : ℝ) :
    (dyadicMap r m p u).2 = (Real.sqrt ((1 / 2 : ℝ) ^ r))⁻¹ *
      ((p ((m : ℝ) * (1 / 2 : ℝ) ^ r + 1 * ((1 / 2 : ℝ) ^ r * u))).2 -
        (p ((m : ℝ) * (1 / 2 : ℝ) ^ r)).2) := rfl

/-- The unit event for the localized path is the event on the window `[c, c + ε]`. -/
private lemma unitOppositeSideMin_dyadicMap {r : ℕ} {m : ℤ} {p : Path2} {t : ℝ}
    (ht : t ∈ Icc ((m : ℝ) * (1 / 2 : ℝ) ^ r) ((m : ℝ) * (1 / 2 : ℝ) ^ r + (1 / 2 : ℝ) ^ r))
    (hX : ∀ s ∈ Icc (t - 2 * (1 / 2 : ℝ) ^ r) t, (p t).1 ≤ (p s).1)
    (hY : ∀ s ∈ Icc t (t + 2 * (1 / 2 : ℝ) ^ r), (p t).2 ≤ (p s).2) :
    UnitOppositeSideMin (fun u => (dyadicMap r m p u).1) (fun u => (dyadicMap r m p u).2) := by
  set ε : ℝ := (1 / 2 : ℝ) ^ r with hε_def
  have hε : 0 < ε := pow_pos (by norm_num) r
  set c : ℝ := (m : ℝ) * ε with hc
  have hpos : 0 ≤ (Real.sqrt ε)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have htε : ε * ((t - c) / ε) = t - c := by field_simp
  have hpt : c + 1 * (ε * ((t - c) / ε)) = t := by rw [htε]; ring
  refine ⟨(t - c) / ε, ⟨div_nonneg (sub_nonneg.2 ht.1) hε.le, ?_⟩, ?_, ?_⟩
  · rw [div_le_one hε]
    linarith [ht.2]
  · intro s hs
    beta_reduce
    rw [dyadicMap_fst, dyadicMap_fst, ← hε_def, ← hc, hpt]
    refine mul_le_mul_of_nonneg_left (sub_le_sub_right (hX _ ⟨?_, ?_⟩) _) hpos
    · nlinarith [mul_le_mul_of_nonneg_left hs.1 hε.le]
    · nlinarith [mul_le_mul_of_nonneg_left hs.2 hε.le]
  · intro s hs
    beta_reduce
    rw [dyadicMap_snd, dyadicMap_snd, ← hε_def, ← hc, hpt]
    refine mul_le_mul_of_nonneg_left (sub_le_sub_right (hY _ ⟨?_, ?_⟩) _) hpos
    · nlinarith [mul_le_mul_of_nonneg_left hs.1 hε.le]
    · nlinarith [mul_le_mul_of_nonneg_left hs.2 hε.le]

private lemma measure_dyadic_eq_zero {γ : ℝ}
    (hunit : ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      μ {p | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} = 0)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (r : ℕ) (m : ℤ) :
    μ {p | UnitOppositeSideMin (fun u => (dyadicMap r m p u).1)
      (fun u => (dyadicMap r m p u).2)} = 0 := by
  have h0 := hunit _ (isCorrelatedBM2_map_dyadicMap hμ r m)
  refine le_antisymm ?_ bot_le
  calc μ {p | UnitOppositeSideMin (fun u => (dyadicMap r m p u).1)
        (fun u => (dyadicMap r m p u).2)}
      ≤ μ.map (dyadicMap r m)
          {q | UnitOppositeSideMin (fun t => (q t).1) (fun t => (q t).2)} :=
        Measure.le_map_apply (measurable_dyadicMap r m).aemeasurable
          {q | UnitOppositeSideMin (fun t => (q t).1) (fun t => (q t).2)}
    _ = 0 := h0

private lemma left_min_closed {X : ℝ → ℝ} {t h δ : ℝ} (hδ : δ < h)
    (hleft : ∀ s ∈ Ioo (t - h) t, X t ≤ X s) : ∀ s ∈ Icc (t - δ) t, X t ≤ X s := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with rfl | hlt
  · exact le_rfl
  · exact hleft s ⟨by linarith [hs.1], hlt⟩

private lemma right_min_closed {Y : ℝ → ℝ} {t h δ : ℝ} (hδ : δ < h)
    (hright : ∀ s ∈ Ioo t (t + h), Y t ≤ Y s) : ∀ s ∈ Icc t (t + δ), Y t ≤ Y s := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hlt
  · exact le_rfl
  · exact hright s ⟨hlt, by linarith [hs.2]⟩

/-- The order `(L, R)` of the opposite-side minimum property. -/
private lemma ae_noOppositeSideMin_fst_snd {γ : ℝ}
    (hunit : ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      μ {p | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} = 0)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ p ∂μ, NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2) := by
  have hnull : μ (⋃ rm : ℕ × ℤ, {p | UnitOppositeSideMin (fun u => (dyadicMap rm.1 rm.2 p u).1)
      (fun u => (dyadicMap rm.1 rm.2 p u).2)}) = 0 :=
    measure_iUnion_null fun rm => measure_dyadic_eq_zero hunit hμ rm.1 rm.2
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
  intro t h hh hleft hright
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hh) (by norm_num : (1 / 2 : ℝ) < 1)
  have hε : 0 < (1 / 2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hδ : 2 * (1 / 2 : ℝ) ^ r < h := by linarith
  set ε : ℝ := (1 / 2 : ℝ) ^ r with hε_def
  refine hp (mem_iUnion.2 ⟨(r, ⌊t / ε⌋), ?_⟩)
  have h1 : (⌊t / ε⌋ : ℝ) ≤ t / ε := Int.floor_le _
  have h2 : t / ε < (⌊t / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊t / ε⌋ : ℝ) * ε ≤ t := (le_div_iff₀ hε).1 h1
  have h4 : t < (⌊t / ε⌋ : ℝ) * ε + ε := by
    have := (div_lt_iff₀ hε).1 h2
    linarith
  show UnitOppositeSideMin (fun u => (dyadicMap r ⌊t / ε⌋ p u).1)
    (fun u => (dyadicMap r ⌊t / ε⌋ p u).2)
  exact unitOppositeSideMin_dyadicMap ⟨h3, h4.le⟩
    (left_min_closed (X := fun t => (p t).1) hδ hleft)
    (right_min_closed (Y := fun t => (p t).2) hδ hright)

private lemma recenter_neg_apply (p : Path2) (u : ℝ) :
    recenterPath 0 (-1) p u = p (-u) - p 0 := by
  have : recenterPath 0 (-1) p u = p (0 + -1 * u) - p 0 := rfl
  rw [this, zero_add, neg_one_mul]

private lemma noOppositeSideMin_swap_of_reverse (p : Path2)
    (h : NoOppositeSideMin (fun t => (recenterPath 0 (-1) p t).1)
      (fun t => (recenterPath 0 (-1) p t).2)) :
    NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1) := by
  intro t k hk hleft hright
  refine h (-t) k hk ?_ ?_
  · intro s hs
    have hmem : -s ∈ Ioo t (t + k) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := sub_le_sub_right (hright (-s) hmem) (p 0).1
    simpa only [recenter_neg_apply, neg_neg, Prod.fst_sub] using this
  · intro s hs
    have hmem : -s ∈ Ioo (t - k) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := sub_le_sub_right (hleft (-s) hmem) (p 0).2
    simpa only [recenter_neg_apply, neg_neg, Prod.snd_sub] using this

/-- Almost surely no time is a minimum of one coordinate on a left neighbourhood and of the other
on a right neighbourhood, provided this is null on the unit scale for every correlated Brownian
law. -/
theorem ae_noOppositeSideMin_of_unit {γ : ℝ}
    (hunit : ∀ μ : MeasureTheory.Measure Path2, IsCorrelatedBM2 γ μ →
      μ {p | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} = 0)
    {μ : MeasureTheory.Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ p ∂μ, NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2) ∧
      NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1) := by
  have hrev := ae_noOppositeSideMin_fst_snd hunit (isCorrelatedBM2_map_recenterPath hμ 0 (-1)
    (by simp))
  have hrev' := ae_of_ae_map (continuous_recenterPath 0 (-1)).measurable.aemeasurable hrev
  filter_upwards [ae_noOppositeSideMin_fst_snd hunit hμ, hrev'] with p h1 h2
  exact ⟨h1, noOppositeSideMin_swap_of_reverse p h2⟩

/-- Localization of Shimura's theorem: the unit event being null for every correlated Brownian
law implies the opposite-side minimum property for every such law. -/
theorem shimuraLocalization_holds (γ : ℝ) : ShimuraLocalization γ :=
  fun hunit _ hμ => ae_noOppositeSideMin_of_unit hunit hμ

end MatedCRT.PeanosphereTriplePoints
