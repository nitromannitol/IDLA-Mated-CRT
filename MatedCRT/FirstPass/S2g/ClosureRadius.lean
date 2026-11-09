import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S2g.HalfBallStop

/-!
# Closure radius and the canonical half-ball stopping (fp-S2g, q1)

Connection step of `notes/fp-gaps/CHATGPT-q1-open-steps.md` Section 3 (H4, H5, H8). For `L ⊆ ℂ` let `closureRadius L`
be the supremum of `‖x‖` over `closure L`, the radius of the smallest closed disc centred at `0` containing the closure
(Armitage-Gardiner, the radius about a point). For an open set inside `B_{3/4}` and `0 ≤ a`, `L ⊆ B_a` (open ball) if and
only if `closureRadius L ≤ a`. This turns the containment stopping predicate of the canonical half-ball time (`B_{1/2}`
in the printed statement, lines 533-537) into the level-set predicate of `sup_level_radius_eq`.

The main theorem `stopped_halfBall_of_closureRadius` is stated for an arbitrary family `L : ℝ → Set ℂ` of open sets.
Its hypotheses are the pathwise inputs of the obstacle family (monotonicity, Hausdorff/closure continuity, the pole,
non-emptiness at small times, boundedness of the stopping set); they are not proved here.
-/

namespace MatedCRT

open Set Filter Topology Metric

/-- The radius of the closure of `L` about the origin: the supremum of `‖x‖` over `x ∈ closure L`. -/
noncomputable def closureRadius (L : Set ℂ) : ℝ :=
  sSup ((fun x : ℂ => ‖x‖) '' closure L)

/-- An open set inside the closed disc `B̄_a` lies in the open disc `B_a` (an open set cannot touch its bounding circle
from inside: a point of the circle has points of the set beyond it). -/
theorem open_subset_ball_of_subset_closedBall {L : Set ℂ} {a : ℝ} (hL : IsOpen L)
    (h : L ⊆ closedBall 0 a) : L ⊆ ball 0 a := by
  intro x hx
  rw [mem_ball_zero_iff]
  by_contra hna
  have ha : a ≤ ‖x‖ := not_lt.mp hna
  have hxa : ‖x‖ ≤ a := mem_closedBall_zero_iff.mp (h hx)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hL x hx
  have key : ∃ y ∈ L, a < ‖y‖ := by
    rcases eq_or_ne x 0 with hx0 | hx0
    · refine ⟨((ε / 2 : ℝ) : ℂ), hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, hx0, sub_zero, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        rw [hx0, norm_zero] at ha
        linarith
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hne : ‖x‖ ≠ 0 := hxpos.ne'
      set δ : ℝ := ε / (2 * ‖x‖) with hδ
      have hδpos : 0 < δ := by positivity
      have hδx : δ * ‖x‖ = ε / 2 := by
        rw [hδ]
        field_simp
      refine ⟨((1 + δ : ℝ) : ℂ) * x, hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show ((1 + δ : ℝ) : ℂ) * x - x = (δ : ℂ) * x by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
        linarith
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have hexp : (1 + δ) * ‖x‖ = ‖x‖ + δ * ‖x‖ := by ring
        linarith
  obtain ⟨y, hyL, hy⟩ := key
  have hya : ‖y‖ ≤ a := mem_closedBall_zero_iff.mp (h hyL)
  linarith

/-- Every point of the closure of a set inside `B_{3/4}` has norm at most the closure radius. -/
theorem norm_le_closureRadius {L : Set ℂ} (hb : L ⊆ ball 0 (3 / 4)) {x : ℂ} (hx : x ∈ closure L) :
    ‖x‖ ≤ closureRadius L := by
  have hcl : closure L ⊆ closedBall 0 (3 / 4) :=
    closure_minimal (hb.trans ball_subset_closedBall) isClosed_closedBall
  refine le_csSup ⟨3 / 4, fun y hy => ?_⟩ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hy
  exact mem_closedBall_zero_iff.mp (hcl hz)

/-- A set inside `B̄_a` (with `0 ≤ a`) has closure radius at most `a`. -/
theorem closureRadius_le_of_subset_ball {L : Set ℂ} {a : ℝ} (ha : 0 ≤ a) (h : L ⊆ ball 0 a) :
    closureRadius L ≤ a := by
  refine Real.sSup_le ?_ ha
  rintro _ ⟨z, hz, rfl⟩
  have hcl : closure L ⊆ closedBall 0 a :=
    closure_minimal (h.trans ball_subset_closedBall) isClosed_closedBall
  exact mem_closedBall_zero_iff.mp (hcl hz)

/-- **Connection lemma** (CHATGPT-q1-open-steps.md H5). For an open set `L ⊆ B_{3/4}` and `0 ≤ a`:
`L ⊆ B_a` if and only if `closureRadius L ≤ a`. -/
theorem subset_ball_iff_closureRadius_le {L : Set ℂ} {a : ℝ} (hL : IsOpen L) (hb : L ⊆ ball 0 (3 / 4))
    (ha : 0 ≤ a) : L ⊆ ball 0 a ↔ closureRadius L ≤ a := by
  constructor
  · intro h
    exact closureRadius_le_of_subset_ball ha h
  · intro h
    apply open_subset_ball_of_subset_closedBall hL
    intro x hx
    exact mem_closedBall_zero_iff.mpr ((norm_le_closureRadius hb (subset_closure hx)).trans h)

/-- **Canonical half-ball stopping of an open increasing family** (CHATGPT-q1-open-steps.md H4, H5, H8, deterministic part).
Let `L t` be open subsets of `B_{3/4}` with `L t ⊆ L s` for `0 < t ≤ s`, the closure radius continuous on `(0, ∞)`,
the pole `0` in `L t` for `t > 0`, some `L s ⊆ B_{1/2}` with `s > 0`, and bounded stopping set
`{t > 0 : L t ⊆ B_{1/2}}`. Then `T = sup {t > 0 : L t ⊆ B_{1/2}}` is positive, `L t ⊆ B_{1/2}` for `0 < t < T`, and
`L` is stopped at `∂B_{1/2}` at `T` in the sense of `IsStoppedAtHalfBall`. -/
theorem stopped_halfBall_of_closureRadius {L : ℝ → Set ℂ}
    (hopen : ∀ t, IsOpen (L t)) (hsub : ∀ t, L t ⊆ ball 0 (3 / 4))
    (hmono : MonotoneOn L (Ioi 0))
    (hcont : ContinuousOn (fun t => closureRadius (L t)) (Ioi 0))
    (hpole : ∀ t, 0 < t → (0 : ℂ) ∈ L t)
    (hne : ∃ s : ℝ, 0 < s ∧ L s ⊆ ball 0 (1 / 2))
    (hbdd : BddAbove {t : ℝ | 0 < t ∧ L t ⊆ ball 0 (1 / 2)}) :
    IsStoppedAtHalfBall L (sSup {t : ℝ | 0 < t ∧ L t ⊆ ball 0 (1 / 2)}) ∧
      0 < sSup {t : ℝ | 0 < t ∧ L t ⊆ ball 0 (1 / 2)} := by
  have hRS : ∀ t, 0 < t → (L t ⊆ ball 0 (1 / 2) ↔ closureRadius (L t) ≤ 1 / 2) := fun t _ =>
    subset_ball_iff_closureRadius_le (hopen t) (hsub t) (by norm_num)
  have hSR : {t : ℝ | 0 < t ∧ L t ⊆ ball 0 (1 / 2)} = {t : ℝ | 0 < t ∧ closureRadius (L t) ≤ 1 / 2} := by
    ext t
    constructor
    · rintro ⟨ht, h⟩
      exact ⟨ht, (hRS t ht).mp h⟩
    · rintro ⟨ht, h⟩
      exact ⟨ht, (hRS t ht).mpr h⟩
  obtain ⟨s0, hs0, hLs0⟩ := hne
  have hsR : ∃ s : ℝ, 0 < s ∧ closureRadius (L s) ≤ 1 / 2 := ⟨s0, hs0, (hRS s0 hs0).mp hLs0⟩
  have hbddR : BddAbove {t : ℝ | 0 < t ∧ closureRadius (L t) ≤ 1 / 2} := by
    rw [← hSR]
    exact hbdd
  have hsup := sup_level_radius_eq (R := fun t => closureRadius (L t)) hcont hsR hbddR
  rw [hSR]
  have hTpos : 0 < sSup {t : ℝ | 0 < t ∧ closureRadius (L t) ≤ 1 / 2} := hsup.1
  have hSne : {t : ℝ | 0 < t ∧ closureRadius (L t) ≤ 1 / 2}.Nonempty := ⟨s0, hs0, (hRS s0 hs0).mp hLs0⟩
  refine ⟨?_, hTpos⟩
  unfold IsStoppedAtHalfBall
  refine ⟨?_, ?_⟩
  · -- containment below the supremum, through a later time in the stopping set
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    obtain ⟨s, hsS, hts⟩ := exists_lt_of_lt_csSup hSne htT
    have hsL : L s ⊆ ball 0 (1 / 2) := (hRS s hsS.1).mpr hsS.2
    exact (hmono (show t ∈ Ioi 0 from ht0) (show s ∈ Ioi 0 from hsS.1) hts.le).trans hsL
  · -- the stopping at `∂B_{1/2}`: every smaller radius is exceeded at some time before `T`
    intro r hr
    rcases le_or_gt 0 r with hr0 | hr0
    · obtain ⟨t, ht, hrt⟩ := hsup.2.2 r hr
      refine ⟨t, ht, fun hsub' => ?_⟩
      have hle : closureRadius (L t) ≤ r := (subset_ball_iff_closureRadius_le (hopen t) (hsub t) hr0).mp hsub'
      exact absurd hrt (not_lt.mpr hle)
    · refine ⟨sSup {t : ℝ | 0 < t ∧ closureRadius (L t) ≤ 1 / 2} / 2, ⟨by linarith, by linarith⟩,
        fun hsub' => ?_⟩
      have h0 := mem_ball_zero_iff.mp (hsub' (hpole _ (by linarith)))
      rw [norm_zero] at h0
      linarith

end MatedCRT
