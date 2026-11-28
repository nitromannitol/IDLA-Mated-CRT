import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.TripleCoverSim

/-!
# Components of the minimum-joined relation near a crossing pair

Let `X`, `Y` be coordinates in the sense of `Coord`, with no opposite-side minima in either
order. Starting from a time `t` that is the left end of its classes in both coordinates, the
component of `t` for `Jrel X Y` is explored by two alternating walks: from a valley `z` go up to
`hi P z`, then down to `lo Q (hi P z)`, where `(P, Q)` is `(X, Y)` or `(Y, X)`. The set `Wset`
of all times whose classes meet such a valley is closed under the two relations, and the walks
are confined to explicit intervals. A time `t'` to the right of `t` whose `X`-class is nested
inside the `X`-class of `t` and whose `Y`-class crosses it therefore lies outside the component
of `t`.
-/

set_option autoImplicit false

open Set Filter Topology

namespace MatedCRT.PeanosphereTriplePoints

variable {X Y P Q : ℝ → ℝ}

/-- The valleys of the walk that goes up along `P` and down along `Q`, started at `t`. -/
inductive Val (P Q : ℝ → ℝ) (t : ℝ) : ℝ → Prop
  | base : Val P Q t t
  | step {z : ℝ} : Val P Q t z → lo Q (hi P z) < hi P z → Val P Q t (lo Q (hi P z))

/-- The times whose `P`- or `Q`-class contains a valley of the walk. -/
def Wgen (P Q : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  {z | ∃ v, Val P Q t v ∧ (Sim P v z ∨ Sim Q v z)}

theorem Val.lo_eq (hP : Coord P) (hQ : Coord Q) (hPQ : NoOppositeSideMin P Q) {t : ℝ}
    (h0 : lo P t = t ∧ lo Q t = t) {z : ℝ} (hz : Val P Q t z) : lo P z = z ∧ lo Q z = z := by
  induction hz with
  | base => exact h0
  | @step z _ hlt _ =>
    have hv : lo Q (hi P z) < hi P z := hlt
    refine ⟨?_, lo_lo hQ _⟩
    by_contra hne
    have hlt' : lo P (lo Q (hi P z)) < lo Q (hi P z) :=
      lt_of_le_of_ne (lo_le hP _) hne
    have hhi : lo Q (hi P z) < hi Q (lo Q (hi P z)) := by
      rw [← hi_eq_of_sim hQ (sim_lo hQ (hi P z))]
      exact lt_of_lt_of_le hv (le_hi hQ _)
    exact not_lo_hi hP hQ hPQ _ ⟨hlt', hhi⟩

theorem Val.step_facts (hP : Coord P) (hQ : Coord Q) (hPQ : NoOppositeSideMin P Q) {t : ℝ}
    (h0 : lo P t = t ∧ lo Q t = t) {z : ℝ} (hz : Val P Q t z) (hlt : lo Q (hi P z) < hi P z) :
    z < hi P z ∧ hi Q (hi P z) = hi P z := by
  have K := hz.lo_eq hP hQ hPQ h0
  have hzp : z < hi P z := by
    refine lt_of_le_of_ne (le_hi hP z) fun h => ?_
    have : lo Q (hi P z) = hi P z := by rw [← h, K.2]
    rw [this] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hzp, ?_⟩
  have hl : lo P (hi P z) < hi P z := by
    rw [← lo_eq_of_sim hP (sim_hi hP z), K.1]
    exact hzp
  exact hi_eq_of_lo_lt hP hQ hPQ hl

theorem Wgen_closure (hP : Coord P) (hQ : Coord Q) (hPQ : NoOppositeSideMin P Q)
    (hQP : NoOppositeSideMin Q P) {t : ℝ} (h0 : lo P t = t ∧ lo Q t = t) {z w : ℝ}
    (hz : z ∈ Wgen P Q t) (hw : Sim P z w ∨ Sim Q z w) :
    w ∈ Wgen P Q t ∪ Wgen Q P t := by
  obtain ⟨v, hv, hzv⟩ := hz
  have K := hv.lo_eq hP hQ hPQ h0
  rcases hzv with hzv | hzv
  · -- `z` lies in the `P`-class of `v`
    have hlz : lo P z = v := by rw [lo_eq_of_sim hP (sim_symm hzv), K.1]
    have hhz : hi P z = hi P v := hi_eq_of_sim hP (sim_symm hzv)
    rcases hw with hw | hw
    · exact Or.inl ⟨v, hv, Or.inl (sim_trans hzv hw)⟩
    · by_cases hzeq : z = v
      · exact Or.inl ⟨v, hv, by rw [← hzeq]; exact Or.inr hw⟩
      have hlt : lo P z < z :=
        lt_of_le_of_ne (lo_le hP z) (by rw [hlz]; exact fun h => hzeq h.symm)
      by_cases htop : z < hi P z
      · obtain ⟨hq1, hq2⟩ := mid_other hP hQ hPQ hQP hlt htop
        have := sim_eq_of_singleton hQ hq1 hq2 hw
        subst this
        exact Or.inl ⟨v, hv, Or.inl hzv⟩
      · have htop' : hi P z = z := le_antisymm (not_lt.1 htop) (le_hi hP z)
        have hzz : z = hi P v := by rw [← hhz, htop']
        have hq2 : hi Q z = z := hi_eq_of_lo_lt hP hQ hPQ hlt
        by_cases hq : lo Q z < z
        · have hstep : lo Q (hi P v) < hi P v := by rw [← hzz]; exact hq
          refine Or.inl ⟨lo Q (hi P v), Val.step hv hstep, Or.inr ?_⟩
          rw [← hzz]
          exact sim_trans (sim_symm (sim_lo hQ z)) hw
        · have hq1 : lo Q z = z := le_antisymm (lo_le hQ z) (not_lt.1 hq)
          have := sim_eq_of_singleton hQ hq1 hq2 hw
          subst this
          exact Or.inl ⟨v, hv, Or.inl hzv⟩
  · -- `z` lies in the `Q`-class of `v`
    have hlz : lo Q z = v := by rw [lo_eq_of_sim hQ (sim_symm hzv), K.2]
    have hhz : hi Q z = hi Q v := hi_eq_of_sim hQ (sim_symm hzv)
    rcases hw with hw | hw
    · by_cases hzeq : z = v
      · exact Or.inl ⟨v, hv, by rw [← hzeq]; exact Or.inl hw⟩
      have hlt : lo Q z < z :=
        lt_of_le_of_ne (lo_le hQ z) (by rw [hlz]; exact fun h => hzeq h.symm)
      by_cases htop : z < hi Q z
      · obtain ⟨hq1, hq2⟩ := mid_other hQ hP hQP hPQ hlt htop
        have := sim_eq_of_singleton hP hq1 hq2 hw
        subst this
        exact Or.inl ⟨v, hv, Or.inr hzv⟩
      · have htop' : hi Q z = z := le_antisymm (not_lt.1 htop) (le_hi hQ z)
        have hq2 : hi P z = z := hi_eq_of_lo_lt hQ hP hQP hlt
        by_cases hq : lo P z < z
        · by_cases hvt : v = t
          · subst hvt
            have hzz : z = hi Q v := by rw [← hhz, htop']
            have hstep : lo P (hi Q v) < hi Q v := by rw [← hzz]; exact hq
            refine Or.inr ⟨lo P (hi Q v), Val.step Val.base hstep, Or.inr ?_⟩
            rw [← hzz]
            exact sim_trans (sim_symm (sim_lo hP z)) hw
          · have hv' := hv
            cases hv' with
            | base => exact absurd rfl hvt
            | @step z0 hz0 hlt0 =>
              obtain ⟨-, hk2⟩ := Val.step_facts hP hQ hPQ h0 hz0 hlt0
              have hsp : Sim Q (hi P z0) (lo Q (hi P z0)) := sim_lo hQ _
              have h1 : hi Q z = hi P z0 := by
                rw [hhz, ← hi_eq_of_sim hQ hsp, hk2]
              have hzz : z = hi P z0 := by rw [← h1, htop']
              refine Or.inl ⟨z0, hz0, Or.inl ?_⟩
              rw [hzz] at hw
              exact sim_trans (sim_hi hP z0) hw
        · have hq1 : lo P z = z := le_antisymm (lo_le hP z) (not_lt.1 hq)
          have := sim_eq_of_singleton hP hq1 hq2 hw
          subst this
          exact Or.inl ⟨v, hv, Or.inr hzv⟩
    · exact Or.inl ⟨v, hv, Or.inr (sim_trans hzv hw)⟩

theorem Val_X_inv (hX : Coord X) (hY : Coord Y) (h1 : NoOppositeSideMin X Y) {t t' : ℝ}
    (h0 : lo X t = t ∧ lo Y t = t) (htt' : t < t') (hu : t' < hi X t) (hw : hi X t < hi Y t')
    {z : ℝ} (hz : Val X Y t z) : z = t ∨ (t' < z ∧ z ≤ hi X t) := by
  induction hz with
  | base => exact Or.inl rfl
  | @step z hz hlt ih =>
    obtain ⟨hzp, hYp⟩ := Val.step_facts hX hY h1 h0 hz hlt
    have hp : t' < hi X z ∧ hi X z ≤ hi X t := by
      rcases ih with rfl | ⟨hz1, hz2⟩
      · exact ⟨hu, le_rfl⟩
      · refine ⟨hz1.trans hzp, ?_⟩
        by_contra hgt
        rw [not_le] at hgt
        rcases hz2.eq_or_lt with heq | hlt2
        · have : hi X z = hi X t := by rw [heq, hi_hi hX t]
          linarith
        · exact no_cross hX (by linarith) hlt2 hgt (sim_hi hX t) (sim_hi hX z)
    obtain ⟨hp1, hp2⟩ := hp
    right
    have hle : lo Y (hi X z) ≤ hi X z := lo_le hY _
    refine ⟨?_, hle.trans hp2⟩
    by_contra hnot
    rw [not_lt] at hnot
    rcases hnot.eq_or_lt with heq | hlt3
    · have hs : Sim Y (hi X z) t' := by
        have := sim_lo hY (hi X z)
        rwa [heq] at this
      have h5 : hi Y (hi X z) = hi Y t' := hi_eq_of_sim hY hs
      rw [hYp] at h5
      linarith
    · exact no_cross hY hlt3 hp1 (lt_of_le_of_lt hp2 hw) (sim_symm (sim_lo hY _))
        (sim_hi hY t')

theorem Val_Y_inv (hX : Coord X) (hY : Coord Y) (h2 : NoOppositeSideMin Y X) {t : ℝ}
    (h0 : lo Y t = t ∧ lo X t = t) (hv : hi X t < hi Y t) {z : ℝ} (hz : Val Y X t z) :
    z = t ∨ z < t ∨ hi X t < z := by
  induction hz with
  | base => exact Or.inl rfl
  | @step z hz hlt ih =>
    obtain ⟨hzp, hXp⟩ := Val.step_facts hY hX h2 h0 hz hlt
    have K := hz.lo_eq hY hX h2 h0
    have hC : hi Y z < t ∨ hi X t < hi Y z := by
      rcases ih with rfl | hz1 | hz1
      · exact Or.inr hv
      · rcases lt_trichotomy (hi Y z) t with h | h | h
        · exact Or.inl h
        · exfalso
          have hs : Sim Y z t := by
            have := sim_hi hY z
            rwa [h] at this
          have h4 := lo_eq_of_sim hY hs
          rw [K.1, h0.1] at h4
          linarith
        · rcases lt_trichotomy (hi Y z) (hi Y t) with h' | h' | h'
          · exact (no_cross hY hz1 h h' (sim_hi hY z) (sim_hi hY t)).elim
          · exfalso
            have hs : Sim Y z t := by
              have h5 := sim_hi hY z
              rw [h'] at h5
              exact sim_trans h5 (sim_symm (sim_hi hY t))
            have h4 := lo_eq_of_sim hY hs
            rw [K.1, h0.1] at h4
            linarith
          · exact Or.inr (hv.trans h')
      · exact Or.inr (hz1.trans hzp)
    right
    have hle : lo X (hi Y z) ≤ hi Y z := lo_le hX _
    rcases hC with hC | hC
    · exact Or.inl (lt_of_le_of_lt hle hC)
    · by_contra hnot
      rw [not_or, not_lt, not_lt] at hnot
      obtain ⟨hn1, hn2⟩ := hnot
      have hsp : Sim X (hi Y z) (lo X (hi Y z)) := sim_lo hX _
      rcases hn1.eq_or_lt with h | h
      · have e : hi X (hi Y z) = hi X t := by rw [hi_eq_of_sim hX hsp, ← h]
        rw [hXp] at e
        linarith
      · rcases hn2.eq_or_lt with h' | h'
        · have e : hi X (hi Y z) = hi X t := by rw [hi_eq_of_sim hX hsp, h', hi_hi hX t]
          rw [hXp] at e
          linarith
        · exact no_cross hX h h' hC (sim_hi hX t) (sim_symm hsp)

/-- A time `t'` whose `Y`-class crosses the `X`-class of `t` is not joined to `t`. -/
theorem not_jrel_of_cross (hX : Coord X) (hY : Coord Y) (h1 : NoOppositeSideMin X Y)
    (h2 : NoOppositeSideMin Y X) {t t' : ℝ} (h0 : lo X t = t ∧ lo Y t = t)
    (h0' : lo X t' = t' ∧ lo Y t' = t') (htt' : t < t') (hu : t' < hi X t)
    (hw : hi X t < hi Y t') (hv : hi X t < hi Y t) : ¬ Jrel X Y t t' := by
  have hclosed : ∀ z w, z ∈ Wgen X Y t ∪ Wgen Y X t → (Sim X z w ∨ Sim Y z w) →
      w ∈ Wgen X Y t ∪ Wgen Y X t := by
    rintro z w (hz | hz) hw'
    · exact Wgen_closure hX hY h1 h2 h0 hz hw'
    · rw [union_comm]
      exact Wgen_closure hY hX h2 h1 ⟨h0.2, h0.1⟩ hz hw'.symm
  have htW : t ∈ Wgen X Y t ∪ Wgen Y X t := Or.inl ⟨t, Val.base, Or.inl (sim_refl X t)⟩
  have key : ∀ a b, Jrel X Y a b →
      (a ∈ Wgen X Y t ∪ Wgen Y X t ↔ b ∈ Wgen X Y t ∪ Wgen Y X t) := by
    intro a b hab
    induction hab with
    | rel a b h =>
      exact ⟨fun ha => hclosed a b ha h, fun hb => hclosed b a hb (h.imp sim_symm sim_symm)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  intro hJ
  have hmem := (key t t' hJ).1 htW
  rcases hmem with ⟨v, hv1, hs⟩ | ⟨v, hv1, hs⟩
  · have K := hv1.lo_eq hX hY h1 h0
    have hvt : v = t' := by
      rcases hs with hs | hs
      · rw [← K.1, lo_eq_of_sim hX hs, h0'.1]
      · rw [← K.2, lo_eq_of_sim hY hs, h0'.2]
    subst hvt
    rcases Val_X_inv hX hY h1 h0 htt' hu hw hv1 with h | h
    · linarith
    · exact lt_irrefl _ h.1
  · have K := hv1.lo_eq hY hX h2 ⟨h0.2, h0.1⟩
    have hvt : v = t' := by
      rcases hs with hs | hs
      · rw [← K.1, lo_eq_of_sim hY hs, h0'.2]
      · rw [← K.2, lo_eq_of_sim hX hs, h0'.1]
    subst hvt
    rcases Val_Y_inv hX hY h2 ⟨h0.2, h0.1⟩ hv hv1 with h | h | h
    · linarith
    · linarith
    · linarith

end MatedCRT.PeanosphereTriplePoints
