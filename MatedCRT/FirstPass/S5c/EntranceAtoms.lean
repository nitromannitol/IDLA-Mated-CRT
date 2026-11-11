import MatedCRT.FirstPass.S5c.NewMass
import MatedCRT.FirstPass.S5c.ScaleNull

/-!
# FIRST PASS, stopped clause of 5.1: fixed-deterministic-time union claim (G-stopped Gap 1 repair, items 2-4)

For a monotone family `Λ` of open sets and a rational closed disk `C`, the entrance time `τ_C = inf {s > 0 : C ⊆ Λ_s}`.
If a new point of `Λ_t` appears (`NewMassAt`), some rational disk `C` witnesses `τ_C = t` (`entranceTime_eq_of_newMass`,
and the countable representation of `NewMass.lean`). Hence the positive-probability times of the new-mass event lie in the
countable union of the positive atoms of the laws of the `τ_C` (Mathlib `countable_meas_pos_of_disjoint_iUnion`). With the
scale invariance of the event probabilities (EXTERNAL: the printed scaling of the cone family, IDLA lines 597-602, plus law
invariance; a named hypothesis `hscale` here), `null_of_scale_invariant` gives `P (NewMassAt Λ t) = 0` for every `t > 0`:
`Λ_t = ⋃_{s<t} Λ_s` almost surely for each fixed deterministic `t`. The measurability of the entrance-time level sets is
the compact-set decoder input, a named hypothesis `hentr`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The entrance time of a set `C` into the monotone family `Λ`: the first mass `s > 0` with `C ⊆ Λ_s`. -/
noncomputable def entranceTime (Λ : ℝ → Set ℂ) (C : Set ℂ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ C ⊆ Λ s}

/-- If `C ⊆ Λ_t` and no rational earlier member contains `C`, the entrance time of `C` is `t`. -/
theorem entranceTime_eq_of_newMass {Λ : ℝ → Set ℂ} {t : ℝ} {C : Set ℂ} (ht : 0 < t)
    (hmono : MonotoneOn Λ (Ioi 0)) (hsub : C ⊆ Λ t)
    (hno : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ (q : ℝ)) :
    entranceTime Λ C = t := by
  have hmem : t ∈ {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨ht, hsub⟩
  have hbdd : BddBelow {s : ℝ | 0 < s ∧ C ⊆ Λ s} := ⟨0, fun s hs => hs.1.le⟩
  refine le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨t, hmem⟩ fun s hs => ?_)
  rcases le_or_gt t s with h | h
  · exact h
  · exfalso
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < t from h)
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans hs.1 hq1
    exact hno q hq0 hq2 (fun x hx => hmono (mem_Ioi.2 hs.1) (mem_Ioi.2 hq0) hq1.le (hs.2 hx))

/-- A new point at time `t` of a monotone open family is witnessed by a rational disk whose entrance time is `t`. -/
theorem exists_entrance_eq_of_newMass {Λ : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn Λ (Ioi 0)) (hopen : ∀ s : ℝ, 0 < s → IsOpen (Λ s))
    (h : NewMassAt Λ t) : ∃ (c : ℚ × ℚ) (r : ℚ), entranceTime Λ (ratDisk c r) = t := by
  obtain ⟨c, r, _, hsub, hno⟩ := (newMassAt_iff_ratDisk ht hmono hopen).1 h
  exact ⟨c, r, entranceTime_eq_of_newMass ht hmono hsub hno⟩

/-- The positive-probability entrance times of a random variable are countable: its level sets are measurable and
pairwise disjoint, and a probability measure charges only countably many of them. -/
theorem countable_positive_entrance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → ℝ} (hτ : ∀ t : ℝ, MeasurableSet {ω | τ ω = t}) :
    {t : ℝ | 0 < P {ω | τ ω = t}}.Countable := by
  have hdisj : Pairwise (fun t t' : ℝ => Disjoint {ω | τ ω = t} {ω | τ ω = t'}) := by
    intro t t' htt'
    refine Set.disjoint_left.2 ?_
    intro ω h1 h2
    exact htt' (h1.symm.trans h2)
  exact Measure.countable_meas_pos_of_disjoint_iUnion (fun t => hτ t) hdisj

/-- **Fixed-deterministic-time union claim** (G-stopped Gap 1 repair): for a monotone family of open sets with
measurable entrance-time level sets and a scale-invariant probability of the new-mass event, the new-mass event is null
at every positive time. -/
theorem newMass_null_of_scale_invariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Λ : Ω → ℝ → Set ℂ}
    (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0)) (hopen : ∀ ω, ∀ s : ℝ, 0 < s → IsOpen (Λ ω s))
    (hentr : ∀ (c : ℚ × ℚ) (r : ℚ) (t : ℝ), MeasurableSet {ω | entranceTime (Λ ω) (ratDisk c r) = t})
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P {ω | NewMassAt (Λ ω) (b * t)} = P {ω | NewMassAt (Λ ω) t})
    (t : ℝ) (ht : 0 < t) : P {ω | NewMassAt (Λ ω) t} = 0 := by
  set E' : ℝ → Set Ω := fun s => {ω | 0 < s ∧ NewMassAt (Λ ω) s} with hE'
  have hscale' : ∀ b s : ℝ, 0 < b → 0 < s → P (E' (b * s)) = P (E' s) := by
    intro b s hb hs
    have e1 : E' (b * s) = {ω | NewMassAt (Λ ω) (b * s)} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨mul_pos hb hs, h⟩⟩
    have e2 : E' s = {ω | NewMassAt (Λ ω) s} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
    rw [e1, e2, hscale b s hb hs]
  have hcount : {s : ℝ | 0 < P (E' s)}.Countable := by
    have hsub : {s : ℝ | 0 < P (E' s)} ⊆
        ⋃ i : (ℚ × ℚ) × ℚ, {s : ℝ | 0 < P {ω | entranceTime (Λ ω) (ratDisk i.1 i.2) = s}} := by
      intro s hs
      by_contra hno
      have hnull : ∀ i : (ℚ × ℚ) × ℚ, P {ω | entranceTime (Λ ω) (ratDisk i.1 i.2) = s} = 0 := by
        intro i
        by_contra hi
        exact hno (mem_iUnion.2 ⟨i, pos_iff_ne_zero.2 hi⟩)
      have hcovs : E' s ⊆ ⋃ i : (ℚ × ℚ) × ℚ, {ω | entranceTime (Λ ω) (ratDisk i.1 i.2) = s} := by
        rintro ω ⟨hs0, hNA⟩
        obtain ⟨c, r, hτ⟩ := exists_entrance_eq_of_newMass hs0 (hmono ω) (hopen ω) hNA
        exact mem_iUnion.2 ⟨(c, r), hτ⟩
      have hle : P (E' s) ≤ P (⋃ i : (ℚ × ℚ) × ℚ, {ω | entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) :=
        measure_mono hcovs
      have h0 : P (⋃ i : (ℚ × ℚ) × ℚ, {ω | entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) = 0 :=
        measure_iUnion_null hnull
      exact (not_le.2 hs) (hle.trans_eq h0)
    exact Set.Countable.mono hsub
      (Set.countable_iUnion fun i => countable_positive_entrance P (hentr i.1 i.2))
  have heq : E' t = {ω | NewMassAt (Λ ω) t} := by
    ext ω
    exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
  rw [← heq]
  exact null_of_scale_invariant P E' hscale' hcount t ht

end MatedCRT.S5c
