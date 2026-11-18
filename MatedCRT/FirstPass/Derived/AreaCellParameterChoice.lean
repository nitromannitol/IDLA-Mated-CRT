import Mathlib

/-! # Choice of the parameters of the common-radius transfer

The shifted area-cell transfer for covering balls of a common radius takes, as one hypothesis, a
list of positive tolerances, a compact set, and a finite covering of the thickened domain by balls
of one radius, all compatible with the collar constant of the uniform transfer.  This file shows
that such a list exists for every positive constant: the tolerances and the horizon budget depend
only on the error budget `r`, the collar constant is then used to fix `δ`, and the covering is
by finitely many balls of radius `δ / 80` around points of the thickened domain.

The general statement is for a proper metric space; the second lemma gives the collar data
(concentric open, compact and compact neighbourhoods) of the balls of the covering. -/
set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric
open scoped ENNReal NNReal

universe v

/-- The horizon budget with tolerance `τ = r / 6`: for every number `L` of excursions there is a
positive `b` for which the total error is at most `r`. -/
theorem exists_budget_of_tolerance (r : ℝ≥0) (hr : 0 < r) (L : ℕ) :
    ∃ b : ℝ, 0 < b ∧
      ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
        (ENNReal.ofReal ((r : ℝ) / 6) + ENNReal.ofReal ((r : ℝ) / 6))) +
        (ENNReal.ofReal ((r : ℝ) / 6) + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  refine ⟨(r : ℝ) / (4 * ((L : ℝ) + 1)), by positivity, ?_⟩
  set b : ℝ := (r : ℝ) / (4 * ((L : ℝ) + 1)) with hbdef
  have hb : 0 < b := by positivity
  have hτ : (0 : ℝ) < (r : ℝ) / 6 := by positivity
  have hL : ((L : ℝ≥0∞) + 1) = ENNReal.ofReal ((L : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp
  have hLb : ((L : ℝ≥0∞) + 1) * ENNReal.ofReal b = ENNReal.ofReal (((L : ℝ) + 1) * b) := by
    rw [hL, ENNReal.ofReal_mul hL1.le]
  rw [hLb, ← ENNReal.ofReal_add hτ.le hτ.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add hτ.le (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have : ((L : ℝ) + 1) * b = (r : ℝ) / 4 := by
    rw [hbdef]; field_simp
  rw [this]; linarith

/-- Parameters of the common-radius transfer: tolerances `η` and `τ` depending only on the error
budget `r`; and, for every positive collar constant `c`, a finite family of centers, a common
radius `ρ`, a margin, and the scales `a, e, δ, mesh`, `K` and a compact set `C`, compatible with
the constraints of the transfer. -/
theorem exists_common_radius_parameters {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {U : Set X} (hUb : Bornology.IsBounded U) (r : ℝ≥0) (hr : 0 < r) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      (∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
        ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b + (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
          (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞)) ∧
      ∀ c : ℝ, 0 < c → ∃ (J : Type v) (_ : Fintype J) (center : J → X)
        (margin ρ K a e δ mesh : ℝ) (C : Set X),
        0 < margin ∧ margin ≤ ρ ∧ 0 < K ∧ 0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
        a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧
        ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
        4 * ρ + 3 * a + 2 * K ≤ e ∧ IsCompact C ∧ thickening δ U ⊆ C ∧
        thickening δ U ⊆ ⋃ j, ball (center j) (margin / 4) ∧
        (∀ j, closure (ball (center j) ρ) ⊆ C) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨(r : ℝ) / 4, (r : ℝ) / 6, by positivity, by positivity,
    exists_budget_of_tolerance r hr, ?_⟩
  intro c hc
  set δ : ℝ := min c (r : ℝ) with hδdef
  have hδ : 0 < δ := lt_min hc hr'
  have hδc : δ ≤ c := min_le_left _ _
  have hδr : δ ≤ (r : ℝ) := min_le_right _ _
  set margin : ℝ := δ / 20 with hmargin
  have hm : 0 < margin := by positivity
  -- finite covering of the thickened domain by balls of radius `margin / 4`
  have hbdd : Bornology.IsBounded (thickening δ U) := hUb.thickening
  have hcpt : IsCompact (closure (thickening δ U)) := hbdd.isCompact_closure
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hcpt (show 0 < margin / 4 by positivity)
  have : Finite t := htf.to_subtype
  let J : Type v := ULift.{v} (Fin (Nat.card t))
  have hJ : Finite J := inferInstanceAs (Finite (ULift (Fin (Nat.card t))))
  let e0 : t ≃ Fin (Nat.card t) := Finite.equivFin t
  let center : J → X := fun j => ((e0.symm j.down : t) : X)
  have hcover : thickening δ U ⊆ ⋃ j, ball (center j) (margin / 4) := by
    intro x hx
    have hx' : x ∈ ⋃ y ∈ t, ball y (margin / 4) := hcov (subset_closure hx)
    simp only [mem_iUnion] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    simp only [mem_iUnion]
    refine ⟨ULift.up (e0 ⟨y, hy⟩), ?_⟩
    show x ∈ ball ((e0.symm (e0 ⟨y, hy⟩) : t) : X) (margin / 4)
    rw [Equiv.symm_apply_apply]
    exact hxy
  let C : Set X := closure (thickening δ U ∪ ⋃ j, ball (center j) (margin))
  have hCb : Bornology.IsBounded (thickening δ U ∪ ⋃ j, ball (center j) (margin)) :=
    hbdd.union (Bornology.isBounded_iUnion.2 fun j => isBounded_ball)
  refine ⟨J, inferInstanceAs (Fintype (ULift (Fin (Nat.card t)))), center, margin, margin, δ / 20, δ / 20, δ / 2, δ, δ / 20, C,
    hm, le_rfl, by positivity, by positivity, by positivity, hδ, by positivity,
    by linarith, hδc, by linarith, ?_, by linarith, hCb.isCompact_closure,
    (subset_union_left).trans subset_closure, hcover, fun j => closure_mono ?_⟩
  · have h1 : (0 : ℝ) ≤ δ / 20 + δ / 2 + (r : ℝ) / 4 := by positivity
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr').2 (by linarith)
  · exact fun x hx => Or.inr (mem_iUnion.2 ⟨j, hx⟩)

/-- Concentric collar data of the balls of the covering: for balls of a common radius `ρ ≥ margin`
there are open bounded sets `Us j` (the balls), compact sets `Is j ⊆ Us j` containing the balls of
radius `margin / 2`, compact sets `Ks j ⊆ Us j` and positive radii such that every point within
the radius of `Is j` lies in `Ks j`. -/
theorem exists_ball_collar_data {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {J : Type*} (center : J → X) {margin ρ : ℝ} (hm : 0 < margin) (hmρ : margin ≤ ρ) :
    ∃ (Us Is Ks : J → Set X) (radius : J → ℝ),
      (∀ j, Us j = ball (center j) ρ) ∧ (∀ j, ball (center j) (margin / 2) ⊆ Is j) ∧
      (∀ j, Is j ⊆ ball (center j) ρ) ∧
      (∀ j, IsOpen (Us j)) ∧ (∀ j, Bornology.IsBounded (Us j)) ∧
      (∀ j, IsCompact (Is j)) ∧ (∀ j, Is j ⊆ Us j) ∧
      (∀ j, IsCompact (Ks j)) ∧ (∀ j, Ks j ⊆ Us j) ∧ (∀ j, 0 < radius j) ∧
      (∀ j x, x ∈ Is j → ∀ y, dist y x < radius j → y ∈ Ks j) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hm hmρ
  have hgap : 0 < (ρ - margin / 2) / 2 := by linarith
  refine ⟨fun j => ball (center j) ρ, fun j => closedBall (center j) (margin / 2),
    fun j => closedBall (center j) (margin / 2 + (ρ - margin / 2) / 2),
    fun _ => (ρ - margin / 2) / 2, fun _ => rfl, fun j => ball_subset_closedBall, ?_,
    fun _ => isOpen_ball, fun _ => isBounded_ball, fun _ => isCompact_closedBall _ _, ?_,
    fun _ => isCompact_closedBall _ _, ?_, fun _ => hgap, ?_⟩
  · intro j x hx
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith
  · intro j x hx
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith
  · intro j x hx
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith
  · intro j x hx y hy
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle y x (center j)
    linarith

end MatedCRT
