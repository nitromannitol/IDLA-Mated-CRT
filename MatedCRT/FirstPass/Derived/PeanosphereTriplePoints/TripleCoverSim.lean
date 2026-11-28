import Mathlib
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.PathProperties

/-!
# Minimum-joined times of a continuous function

For a continuous function `X : ℝ → ℝ` that is unbounded below in both time directions and takes
distinct values at distinct local minima, two times `a`, `b` are `Sim X`-related when
`X a = X b` is the minimum of `X` on the interval between them. This is an equivalence relation.
The class of a time `z` lies in the interval `[lo X z, hi X z]`, where `hi X z` is the first time
after `z` at which `X` falls strictly below `X z`, and `lo X z` is the last such time before `z`.

Two functions satisfying the no-opposite-side-minimum hypothesis in both orders cannot have a
time which is the right end of a class of one and the left end of a class of the other.
-/

set_option autoImplicit false

open Set Filter Topology

namespace MatedCRT.PeanosphereTriplePoints

/-- A continuous function, unbounded below in both directions, with distinct values at distinct
local minima. -/
structure Coord (X : ℝ → ℝ) : Prop where
  cont : Continuous X
  below_right : ∀ M T : ℝ, ∃ t ≥ T, X t < M
  below_left : ∀ M T : ℝ, ∃ t ≤ T, X t < M
  locMin_ne : ∀ a b : ℝ, a ≠ b → IsLocalMin X a → IsLocalMin X b → X a ≠ X b

/-- `a` and `b` are joined by a minimum of `X`. -/
def Sim (X : ℝ → ℝ) (a b : ℝ) : Prop := X a = X b ∧ ∀ u ∈ uIcc a b, X a ≤ X u

theorem sim_refl (X : ℝ → ℝ) (a : ℝ) : Sim X a a :=
  ⟨rfl, fun u hu => by
    rw [uIcc_self, mem_singleton_iff] at hu
    exact (congrArg X hu).ge⟩

theorem sim_symm {X : ℝ → ℝ} {a b : ℝ} (h : Sim X a b) : Sim X b a :=
  ⟨h.1.symm, fun u hu => by
    rw [uIcc_comm] at hu
    rw [← h.1]
    exact h.2 u hu⟩

theorem sim_trans {X : ℝ → ℝ} {a b c : ℝ} (h1 : Sim X a b) (h2 : Sim X b c) : Sim X a c := by
  refine ⟨h1.1.trans h2.1, fun u hu => ?_⟩
  rcases Set.uIcc_subset_uIcc_union_uIcc (a := a) (b := b) (c := c) hu with h | h
  · exact h1.2 u h
  · rw [h1.1]
    exact h2.2 u h

/-- Time reversal of a function. -/
def rev (X : ℝ → ℝ) : ℝ → ℝ := fun s => X (-s)

theorem rev_rev (X : ℝ → ℝ) : rev (rev X) = X := by
  funext s
  simp [rev]

theorem mem_uIcc_neg {u a b : ℝ} : -u ∈ uIcc (-a) (-b) ↔ u ∈ uIcc a b := by
  simp only [mem_uIcc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      constructor <;> linarith
    · left
      constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      constructor <;> linarith
    · left
      constructor <;> linarith

theorem sim_rev_iff {X : ℝ → ℝ} {a b : ℝ} : Sim (rev X) a b ↔ Sim X (-a) (-b) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    have hu' : -u ∈ uIcc a b := by
      simpa using (mem_uIcc_neg (u := u) (a := -a) (b := -b)).2 hu
    have := h2 (-u) hu'
    simpa [rev] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    have := h2 (-u) (mem_uIcc_neg.2 hu)
    simpa [rev] using this

theorem isLocalMin_of_Ioo {X : ℝ → ℝ} {m p q : ℝ} (hp : p < m) (hq : m < q)
    (h : ∀ x ∈ Ioo p q, X m ≤ X x) : IsLocalMin X m :=
  Filter.mem_of_superset (Ioo_mem_nhds hp hq) h

theorem isLocalMin_rev_of {X : ℝ → ℝ} {a : ℝ} (h : IsLocalMin X (-a)) :
    IsLocalMin (rev X) a := by
  have h' : ∀ᶠ y in 𝓝 (-a), X (-a) ≤ X y := h
  have := (continuous_neg.tendsto a).eventually h'
  exact this.mono fun x hx => by simpa [rev] using hx

theorem isLocalMin_of_rev {X : ℝ → ℝ} {a : ℝ} (h : IsLocalMin (rev X) a) :
    IsLocalMin X (-a) := by
  have h' : IsLocalMin (rev (rev X)) (-a) := isLocalMin_rev_of (a := -a) (by simpa using h)
  rwa [rev_rev] at h'

theorem coord_rev {X : ℝ → ℝ} (hX : Coord X) : Coord (rev X) where
  cont := hX.cont.comp continuous_neg
  below_right M T := by
    obtain ⟨t, ht, h⟩ := hX.below_left M (-T)
    exact ⟨-t, by linarith, by simpa [rev] using h⟩
  below_left M T := by
    obtain ⟨t, ht, h⟩ := hX.below_right M (-T)
    exact ⟨-t, by linarith, by simpa [rev] using h⟩
  locMin_ne a b hab ha hb := by
    have := hX.locMin_ne (-a) (-b) (fun h => hab (neg_injective h)) (isLocalMin_of_rev ha)
      (isLocalMin_of_rev hb)
    simpa [rev] using this

variable {X Y : ℝ → ℝ}

/-- The first time after `z` at which `X` is strictly below `X z`. -/
noncomputable def hi (X : ℝ → ℝ) (z : ℝ) : ℝ := sInf {s | z ≤ s ∧ X s < X z}

/-- The last time before `z` at which `X` is strictly below `X z`. -/
noncomputable def lo (X : ℝ → ℝ) (z : ℝ) : ℝ := -hi (rev X) (-z)

theorem hiSet_nonempty (hX : Coord X) (z : ℝ) : {s | z ≤ s ∧ X s < X z}.Nonempty := by
  obtain ⟨s, hs, hlt⟩ := hX.below_right (X z) z
  exact ⟨s, hs, hlt⟩

theorem hiSet_bddBelow (X : ℝ → ℝ) (z : ℝ) : BddBelow {s | z ≤ s ∧ X s < X z} :=
  ⟨z, fun _ hs => hs.1⟩

theorem le_hi (hX : Coord X) (z : ℝ) : z ≤ hi X z :=
  le_csInf (hiSet_nonempty hX z) fun _ hs => hs.1

theorem X_hi_le (hX : Coord X) (z : ℝ) : X (hi X z) ≤ X z := by
  have hmem := csInf_mem_closure (hiSet_nonempty hX z) (hiSet_bddBelow X z)
  have hcl : IsClosed {s : ℝ | X s ≤ X z} := isClosed_le hX.cont continuous_const
  have : closure {s | z ≤ s ∧ X s < X z} ⊆ {s | X s ≤ X z} :=
    closure_minimal (fun s hs => hs.2.le) hcl
  exact this hmem

theorem ge_of_lt_hi {z s : ℝ} (hzs : z ≤ s) (hs : s < hi X z) : X z ≤ X s := by
  by_contra h
  rw [not_le] at h
  have : hi X z ≤ s := csInf_le (hiSet_bddBelow X z) ⟨hzs, h⟩
  linarith

theorem X_hi_ge (hX : Coord X) (z : ℝ) : X z ≤ X (hi X z) := by
  rcases (le_hi hX z).eq_or_lt with h | h
  · exact (congrArg X h).le
  · have hcl : IsClosed {s : ℝ | X z ≤ X s} := isClosed_le continuous_const hX.cont
    have hsub : Ico z (hi X z) ⊆ {s | X z ≤ X s} := fun s hs => ge_of_lt_hi hs.1 hs.2
    have := closure_minimal hsub hcl
    rw [closure_Ico h.ne] at this
    exact this ⟨h.le, le_rfl⟩

theorem X_hi (hX : Coord X) (z : ℝ) : X (hi X z) = X z :=
  le_antisymm (X_hi_le hX z) (X_hi_ge hX z)

theorem sim_hi (hX : Coord X) (z : ℝ) : Sim X z (hi X z) := by
  refine ⟨(X_hi hX z).symm, fun u hu => ?_⟩
  rw [uIcc_of_le (le_hi hX z)] at hu
  rcases hu.2.eq_or_lt with h | h
  · rw [h]
    exact (X_hi hX z).ge
  · exact ge_of_lt_hi hu.1 h

theorem exists_lt_hi_add (hX : Coord X) (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, hi X z < s ∧ s < hi X z + ε ∧ X s < X z := by
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt (hiSet_nonempty hX z)
    (show hi X z < hi X z + ε by linarith)
  have hle : hi X z ≤ s := csInf_le (hiSet_bddBelow X z) hs
  refine ⟨s, lt_of_le_of_ne hle ?_, hlt, hs.2⟩
  intro h
  have h2 := hs.2
  rw [← h, X_hi hX z] at h2
  exact lt_irrefl _ h2

theorem le_hi_of_sim (hX : Coord X) {z w : ℝ} (h : Sim X z w) (hzw : z ≤ w) : w ≤ hi X z := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_lt_hi_add hX z (sub_pos.2 hlt)
  have hs : s ∈ uIcc z w := by
    rw [uIcc_of_le hzw]
    exact ⟨(le_hi hX z).trans hs1.le, by linarith⟩
  exact absurd (h.2 s hs) (not_le.2 hs3)

theorem sim_le_hi (hX : Coord X) {z w : ℝ} (h : Sim X z w) : w ≤ hi X z := by
  rcases le_total z w with hzw | hwz
  · exact le_hi_of_sim hX h hzw
  · exact hwz.trans (le_hi hX z)

theorem hi_eq_of_sim (hX : Coord X) {z w : ℝ} (h : Sim X z w) : hi X z = hi X w :=
  le_antisymm
    (le_hi_of_sim hX (sim_trans (sim_symm h) (sim_hi hX z)) (sim_le_hi hX h))
    (le_hi_of_sim hX (sim_trans h (sim_hi hX w)) (sim_le_hi hX (sim_symm h)))

theorem hi_hi (hX : Coord X) (z : ℝ) : hi X (hi X z) = hi X z :=
  (hi_eq_of_sim hX (sim_hi hX z)).symm

theorem lo_le (hX : Coord X) (z : ℝ) : lo X z ≤ z := by
  have := le_hi (coord_rev hX) (-z)
  unfold lo
  linarith

theorem sim_lo (hX : Coord X) (z : ℝ) : Sim X z (lo X z) := by
  have := sim_hi (coord_rev hX) (-z)
  rw [sim_rev_iff] at this
  simpa [lo] using this

theorem sim_ge_lo (hX : Coord X) {z w : ℝ} (h : Sim X z w) : lo X z ≤ w := by
  have := sim_le_hi (coord_rev hX) (z := -z) (w := -w) (sim_rev_iff.2 (by simpa using h))
  unfold lo
  linarith

theorem lo_eq_of_sim (hX : Coord X) {z w : ℝ} (h : Sim X z w) : lo X z = lo X w := by
  have := hi_eq_of_sim (coord_rev hX) (z := -z) (w := -w) (sim_rev_iff.2 (by simpa using h))
  unfold lo
  rw [this]

theorem lo_lo (hX : Coord X) (z : ℝ) : lo X (lo X z) = lo X z :=
  (lo_eq_of_sim hX (sim_lo hX z)).symm

theorem sim_eq_of_singleton (hX : Coord X) {z w : ℝ} (hlo : lo X z = z) (hhi : hi X z = z)
    (h : Sim X z w) : w = z := by
  have h1 := sim_le_hi hX h
  have h2 := sim_ge_lo hX h
  rw [hhi] at h1
  rw [hlo] at h2
  exact le_antisymm h1 h2

/-- Strictly interlacing arcs of one coordinate cannot both be joined. -/
theorem no_cross (hX : Coord X) {a a' b b' : ℝ} (h1 : a < a') (h2 : a' < b) (h3 : b < b')
    (s1 : Sim X a b) (s2 : Sim X a' b') : False := by
  have hm1 : ∀ u ∈ Icc a b, X a ≤ X u := fun u hu =>
    s1.2 u (by rw [uIcc_of_le (by linarith)]; exact hu)
  have hm2 : ∀ u ∈ Icc a' b', X a' ≤ X u := fun u hu =>
    s2.2 u (by rw [uIcc_of_le (by linarith)]; exact hu)
  have e1 : X a ≤ X a' := hm1 a' ⟨h1.le, h2.le⟩
  have e2 : X a' ≤ X b := hm2 b ⟨h2.le, h3.le⟩
  have e3 : X a = X b := s1.1
  have e4 : X a' = X b := le_antisymm e2 (by linarith)
  have hb : IsLocalMin X b := by
    refine isLocalMin_of_Ioo (p := a) (q := b') (by linarith) h3 fun x hx => ?_
    rcases le_total x b with hxb | hbx
    · rw [← e3]
      exact hm1 x ⟨hx.1.le, hxb⟩
    · rw [← e4]
      exact hm2 x ⟨by linarith [hx.1], hx.2.le⟩
  have ha' : IsLocalMin X a' := by
    refine isLocalMin_of_Ioo (p := a) (q := b') h1 (by linarith) fun x hx => ?_
    rcases le_total x b with hxb | hbx
    · rw [e4, ← e3]
      exact hm1 x ⟨hx.1.le, hxb⟩
    · exact hm2 x ⟨by linarith [hx.1], hx.2.le⟩
  exact hX.locMin_ne a' b (ne_of_lt h2) ha' hb e4

/-- A left partner of `τ` and a right minimum of `Y` at `τ` contradict the no-opposite-side
hypothesis. -/
theorem not_left_right (h : NoOppositeSideMin X Y) {a τ c : ℝ} (ha : a < τ) (hc : τ < c)
    (hX : Sim X a τ) (hY : ∀ s ∈ Icc τ c, Y τ ≤ Y s) : False := by
  refine h τ (min (τ - a) (c - τ)) (lt_min (by linarith) (by linarith)) (fun s hs => ?_)
    (fun s hs => ?_)
  · have hs' : s ∈ uIcc a τ := by
      rw [uIcc_of_le ha.le]
      exact ⟨by linarith [hs.1, min_le_left (τ - a) (c - τ)], hs.2.le⟩
    rw [← hX.1]
    exact hX.2 s hs'
  · exact hY s ⟨hs.1.le, by linarith [hs.2, min_le_right (τ - a) (c - τ)]⟩

theorem not_lo_hi (hX : Coord X) (hY : Coord Y) (h : NoOppositeSideMin X Y) (τ : ℝ) :
    ¬ (lo X τ < τ ∧ τ < hi Y τ) := by
  rintro ⟨h1, h2⟩
  refine not_left_right h h1 h2 (sim_symm (sim_lo hX τ)) fun s hs => ?_
  exact (sim_hi hY τ).2 s (by rw [uIcc_of_le (le_hi hY τ)]; exact hs)

theorem hi_eq_of_lo_lt (hX : Coord X) (hY : Coord Y) (h : NoOppositeSideMin X Y) {τ : ℝ}
    (hl : lo X τ < τ) : hi Y τ = τ :=
  le_antisymm (not_lt.1 fun h2 => not_lo_hi hX hY h τ ⟨hl, h2⟩) (le_hi hY τ)

theorem lo_eq_of_lt_hi (hX : Coord X) (hY : Coord Y) (h : NoOppositeSideMin X Y) {τ : ℝ}
    (hl : τ < hi Y τ) : lo X τ = τ :=
  le_antisymm (lo_le hX τ) (not_lt.1 fun h2 => not_lo_hi hX hY h τ ⟨h2, hl⟩)

/-- A time with a left partner of `X` and a right partner of `X` has no partners of `Y`. -/
theorem mid_other (hX : Coord X) (hY : Coord Y) (hXY : NoOppositeSideMin X Y)
    (hYX : NoOppositeSideMin Y X) {m : ℝ} (h1 : lo X m < m) (h2 : m < hi X m) :
    lo Y m = m ∧ hi Y m = m :=
  ⟨lo_eq_of_lt_hi hY hX hYX h2, hi_eq_of_lo_lt hX hY hXY h1⟩

/-- A time at which `Y` has a right minimum is the left end of its `X`-class. -/
theorem lo_eq_of_right_min (hX : Coord X) (h : NoOppositeSideMin X Y) {τ c : ℝ} (hc : τ < c)
    (hY : ∀ s ∈ Icc τ c, Y τ ≤ Y s) : lo X τ = τ := by
  by_contra hne
  have hlt : lo X τ < τ := lt_of_le_of_ne (lo_le hX τ) hne
  exact not_left_right h hlt hc (sim_symm (sim_lo hX τ)) hY

/-- The relation joining times through minima of `X` or of `Y`. -/
def Jrel (X Y : ℝ → ℝ) : ℝ → ℝ → Prop :=
  Relation.EqvGen fun a b => Sim X a b ∨ Sim Y a b

end MatedCRT.PeanosphereTriplePoints
