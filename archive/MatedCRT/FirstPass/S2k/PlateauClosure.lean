import Mathlib.Analysis.Complex.Basic
import MatedCRT.FirstPass.S2k.PlateauTonelli

/-! # FIRST PASS S2k: the deterministic closure argument of section 4.2 (cycle note)

Written argument: `notes/fp-gaps/CHATGPT-closure-inside-cycle.md`, section 4.2 ("Suppose closure containment fails at some
`0 < t < T`"). Given the identification `Λ_t = L_t` of the stopped cone family with the source family (equation (16),
obtained from section 3.2 and HB Theorem 5.5 and is an input of the caller), the closure containment before the stopping
time follows from the absence of a plateau of the maximal modulus at radius `1/2` (equation (15)). Only elementary
real analysis and the topology of `ℂ` are used here. -/

open Metric Set Filter Topology

namespace MatedCRT.FirstPass.S2k

/-- The maximal modulus `R(t) = max {|z| : z ∈ cl L_t}` of a set of the source family, written as a supremum (cycle note,
equation (9)). For a nonempty compact set this supremum is the maximum. -/
noncomputable def maxNormRadius (S : Set ℂ) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' S)

/-- **Closure containment from the absence of a plateau at radius `1/2` (cycle note, section 4.2).** Let `Λ_t = L_t` for
`0 < t < T` (identification (16)), let `Λ_t ⊆ B_{1/2}` (confinement), let the source family `L` be nondecreasing on
`(0, T)`, and let no two rational times `0 < p < q < T` have `R(p) = R(q) = 1/2` (the good event (15) at radius `1/2`).
Then `cl Λ_t ⊆ B_{1/2}` for every `t ∈ (0, T)`. -/
theorem closure_inside_halfBall_of_plateau_free (L Λ : ℝ → Set ℂ) (T : ℝ)
    (hΛ : ∀ t ∈ Ioo (0 : ℝ) T, Λ t = L t)
    (hconf : ∀ t ∈ Ioo (0 : ℝ) T, Λ t ⊆ ball (0 : ℂ) (1 / 2))
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t < T → L s ⊆ L t)
    (hgood : ∀ p q : ℚ, 0 < (p : ℝ) → (p : ℝ) < q → (q : ℝ) < T →
      ¬ (maxNormRadius (closure (L p)) = 1 / 2 ∧ maxNormRadius (closure (L q)) = 1 / 2)) :
    ∀ t ∈ Ioo (0 : ℝ) T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2) := by
  -- closures of the family lie in the closed ball of radius 1/2
  have hcl : ∀ s ∈ Ioo (0 : ℝ) T, closure (L s) ⊆ closedBall (0 : ℂ) (1 / 2) := by
    intro s hs
    rw [← hΛ s hs]
    exact (closure_mono (hconf s hs)).trans closure_ball_subset_closedBall
  have hbdd : ∀ s ∈ Ioo (0 : ℝ) T, BddAbove ((fun z : ℂ => ‖z‖) '' closure (L s)) := by
    intro s hs
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := hcl s hs hz
    rw [mem_closedBall_zero_iff] at this
    exact this
  have hmax : ∀ s ∈ Ioo (0 : ℝ) T, maxNormRadius (closure (L s)) ≤ 1 / 2 := by
    intro s hs
    refine Real.sSup_le ?_ (by norm_num)
    rintro _ ⟨z, hz, rfl⟩
    have := hcl s hs hz
    rw [mem_closedBall_zero_iff] at this
    exact this
  have hattain : ∀ s ∈ Ioo (0 : ℝ) T, ∀ z ∈ closure (L s), ‖z‖ ≤ maxNormRadius (closure (L s)) :=
    fun s hs z hz => le_csSup (hbdd s hs) (mem_image_of_mem _ hz)
  intro t ht
  by_contra hnot
  obtain ⟨x, hxΛ, hxn⟩ := Set.not_subset.1 hnot
  have hxL : x ∈ closure (L t) := by
    rw [hΛ t ht] at hxΛ
    exact hxΛ
  have hx1 : ‖x‖ = 1 / 2 := by
    have h1 : ‖x‖ ≤ 1 / 2 := by
      have := hcl t ht hxL
      rwa [mem_closedBall_zero_iff] at this
    have h2 : 1 / 2 ≤ ‖x‖ := by
      rw [mem_ball_zero_iff] at hxn
      exact not_lt.1 hxn
    exact le_antisymm h1 h2
  -- the maximal modulus at `t` is exactly `1/2`
  have hRt : maxNormRadius (closure (L t)) = 1 / 2 := by
    have h := hattain t ht x hxL
    rw [hx1] at h
    exact le_antisymm (hmax t ht) h
  -- rational times `t < p < q < T`
  obtain ⟨p, hpt, hpT⟩ := exists_rat_btwn ht.2
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hp : (p : ℝ) ∈ Ioo (0 : ℝ) T := ⟨lt_trans ht.1 hpt, hpT⟩
  have hq : (q : ℝ) ∈ Ioo (0 : ℝ) T := ⟨lt_trans (lt_trans ht.1 hpt) hpq, hqT⟩
  have hRge : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) T → t < s → 1 / 2 ≤ maxNormRadius (closure (L s)) := by
    intro s hs hts
    rw [← hRt]
    unfold maxNormRadius
    refine csSup_le_csSup (hbdd s hs) ⟨‖x‖, mem_image_of_mem _ hxL⟩ ?_
    exact image_mono (closure_mono (hmono t s ht.1 hts.le hs.2))
  have hRp : maxNormRadius (closure (L p)) = 1 / 2 :=
    le_antisymm (hmax p hp) (hRge p hp hpt)
  have hRq : maxNormRadius (closure (L q)) = 1 / 2 :=
    le_antisymm (hmax q hq) (hRge q hq (lt_trans hpt hpq))
  exact hgood p q (lt_trans ht.1 hpt) hpq hqT ⟨hRp, hRq⟩

/-- **Good-event form of section 4.2.** If, at the outcome `ω`, the value `1/2` is not a plateau value of the maximal
moduli `R(q) = maxNormRadius (closure (L_q))` of the source family (the event whose probability vanishes by (15)),
then closure containment before the stopping time holds for every stopped family `Λ` with `Λ_t = L_t` and
`Λ_t ⊆ B_{1/2}` on `(0, T)`. -/
theorem closure_inside_of_not_plateau {Ω : Type*} (L : Ω → ℝ → Set ℂ) (Λ : ℝ → Set ℂ) (T : ℝ) (ω : Ω)
    (hΛ : ∀ t ∈ Ioo (0 : ℝ) T, Λ t = L ω t)
    (hconf : ∀ t ∈ Ioo (0 : ℝ) T, Λ t ⊆ ball (0 : ℂ) (1 / 2))
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t < T → L ω s ⊆ L ω t)
    (hnp : (1 / 2 : ℝ) ∉ plateauValues (fun (q : ℚ) (ω' : Ω) => maxNormRadius (closure (L ω' (q : ℝ)))) ω) :
    ∀ t ∈ Ioo (0 : ℝ) T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2) := by
  refine closure_inside_halfBall_of_plateau_free (L ω) Λ T hΛ hconf hmono ?_
  intro p q hp hpq _ ⟨h1, h2⟩
  apply hnp
  refine ⟨p, q, ?_, ?_, h1, h2⟩
  · exact_mod_cast hp
  · exact_mod_cast hpq

end MatedCRT.FirstPass.S2k
