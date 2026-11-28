import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.TripleCoverSets

/-!
# The cover of the multiply visited times

For a traversal `η` whose fibres are the classes of `Jrel X Y`, every time visited three times is
joined to either a local minimum of `X` or `Y`, or to a time `τ` that is the left end (or the right
end) of nonsingleton classes of both coordinates. In the second case the compact sets `Eset`
(or their time reversals) contain `τ`. This file collects the symmetries (swapping the two
coordinates, reversing time), the structure of a class with at least three times, and the cover.
-/

set_option autoImplicit false

open Set Filter Topology

namespace MatedCRT.PeanosphereTriplePoints

variable {X Y P Q : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### Symmetries -/

theorem jrel_swap {s t : ℝ} : Jrel Y X s t ↔ Jrel X Y s t := by
  have key : ∀ {A B : ℝ → ℝ} (a b : ℝ), (Sim A a b ∨ Sim B a b) → (Sim B a b ∨ Sim A a b) :=
    fun _ _ h => h.symm
  exact ⟨fun h => Relation.EqvGen.mono key _ _ h, fun h => Relation.EqvGen.mono key _ _ h⟩

theorem setup_swap (h : Setup X Y η) : Setup Y X η :=
  ⟨h.coordY, h.coordX, h.noYX, h.noXY, fun s t => (h.fib s t).trans jrel_swap.symm⟩

theorem eqvGen_neg {r r' : ℝ → ℝ → Prop} (hr : ∀ a b, r a b → r' (-a) (-b)) {a b : ℝ}
    (h : Relation.EqvGen r a b) : Relation.EqvGen r' (-a) (-b) := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (hr a b h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem jrel_rev_iff {s t : ℝ} : Jrel (rev X) (rev Y) s t ↔ Jrel X Y (-s) (-t) := by
  constructor
  · intro h
    exact eqvGen_neg (r := fun a b => Sim (rev X) a b ∨ Sim (rev Y) a b)
      (r' := fun a b => Sim X a b ∨ Sim Y a b) (fun a b hab => by
      rcases hab with hab | hab
      · left
        exact sim_rev_iff.1 hab
      · right
        exact sim_rev_iff.1 hab) h
  · intro h
    have := eqvGen_neg (r := fun a b => Sim X a b ∨ Sim Y a b)
      (r' := fun a b => Sim (rev X) a b ∨ Sim (rev Y) a b) (fun a b hab => by
      rcases hab with hab | hab
      · left
        rw [sim_rev_iff]
        simpa using hab
      · right
        rw [sim_rev_iff]
        simpa using hab) h
    rw [neg_neg, neg_neg] at this
    exact this

theorem noOpp_rev (h : NoOppositeSideMin Y X) : NoOppositeSideMin (rev X) (rev Y) := by
  intro t hh hpos hleft hright
  refine h (-t) hh hpos (fun s hs => ?_) (fun s hs => ?_)
  · have := hright (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa [rev] using this
  · have := hleft (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa [rev] using this

theorem setup_rev (h : Setup X Y η) : Setup (rev X) (rev Y) (fun s => η (-s)) :=
  ⟨coord_rev h.coordX, coord_rev h.coordY, noOpp_rev h.noYX, noOpp_rev h.noXY,
    fun s t => (h.fib (-s) (-t)).trans jrel_rev_iff.symm⟩

theorem nowhereMonotone_rev (h : NowhereMonotone X) : NowhereMonotone (rev X) := by
  intro a b hab
  have hX := h (-b) (-a) (by linarith)
  have hmem : ∀ {x : ℝ}, x ∈ Icc (-b) (-a) → -x ∈ Icc a b := fun hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  constructor
  · intro hm
    apply hX.2
    intro x hx y hy hxy
    have := hm (hmem hy) (hmem hx) (by linarith)
    simpa [rev] using this
  · intro hm
    apply hX.1
    intro x hx y hy hxy
    have := hm (hmem hy) (hmem hx) (by linarith)
    simpa [rev] using this

theorem lo_rev_neg (X : ℝ → ℝ) (τ : ℝ) : lo (rev X) (-τ) = -hi X τ := by
  unfold lo
  rw [rev_rev, neg_neg]

theorem hi_rev_neg (X : ℝ → ℝ) (τ : ℝ) : hi (rev X) (-τ) = -lo X τ := by
  unfold lo
  ring

/-! ### Middle points -/

/-- A time strictly inside its class. -/
def Mid (X : ℝ → ℝ) (m : ℝ) : Prop := lo X m < m ∧ m < hi X m

theorem Mid.isLocalMin (hX : Coord X) {m : ℝ} (h : Mid X m) : IsLocalMin X m := by
  refine isLocalMin_of_Ioo h.1 h.2 fun x hx => ?_
  rcases le_total x m with hxm | hmx
  · exact (sim_lo hX m).2 x (by rw [uIcc_of_ge (lo_le hX m)]; exact ⟨hx.1.le, hxm⟩)
  · exact (sim_hi hX m).2 x (by rw [uIcc_of_le (le_hi hX m)]; exact ⟨hmx, hx.2.le⟩)

theorem eq_lo_or_hi (hQ : Coord Q) {z w : ℝ} (h : Sim Q z w) (hm : ¬ Mid Q w) :
    w = lo Q z ∨ w = hi Q z := by
  have h1 : lo Q w = lo Q z := (lo_eq_of_sim hQ h).symm
  have h2 : hi Q w = hi Q z := (hi_eq_of_sim hQ h).symm
  by_contra hne
  rw [not_or] at hne
  apply hm
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact lt_of_le_of_ne (sim_ge_lo hQ h) (Ne.symm hne.1)
  · rw [h2]
    exact lt_of_le_of_ne (sim_le_hi hQ h) hne.2

theorem three_in_two {a b t1 t2 t3 : ℝ} (h12 : t1 < t2) (h23 : t2 < t3)
    (h1 : t1 = a ∨ t1 = b) (h2 : t2 = a ∨ t2 = b) (h3 : t3 = a ∨ t3 = b) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> linarith

theorem sim_of_jrel_step {a b : ℝ} (h : Sim X a b ∨ Sim Y a b) : Jrel X Y a b :=
  Relation.EqvGen.rel _ _ h

/-- If `t1` is a singleton class of `P` and every time of its `Q`-class is too, the component
of `t1` is its `Q`-class. -/
theorem single_class (hP : Coord P) {t1 : ℝ}
    (hall : ∀ m, Sim Q t1 m → lo P m = m ∧ hi P m = m) {w : ℝ} (hw : Jrel P Q t1 w) :
    Sim Q t1 w := by
  have hclosed : ∀ a b, (Sim P a b ∨ Sim Q a b) → Sim Q t1 a → Sim Q t1 b := by
    intro a b h ha
    rcases h with h | h
    · have := sim_eq_of_singleton hP (hall a ha).1 (hall a ha).2 h
      rw [this]
      exact ha
    · exact sim_trans ha h
  have key : ∀ a b, Jrel P Q a b → (Sim Q t1 a ↔ Sim Q t1 b) := by
    intro a b hab
    induction hab with
    | rel a b h => exact ⟨hclosed a b h, hclosed b a (h.imp sim_symm sim_symm)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key t1 w hw).1 (sim_refl Q t1)

theorem pair_class (hX : Coord X) (hY : Coord Y) {p q : ℝ} (h1 : lo X p = p) (h2 : hi X p = q)
    (h3 : lo Y p = p) (h4 : hi Y p = q)
    (hnm : ∀ w, Jrel X Y p w → ¬ Mid X w ∧ ¬ Mid Y w) {w : ℝ} (hw : Jrel X Y p w) :
    w = p ∨ w = q := by
  have hpq : Jrel X Y p q := sim_of_jrel_step (Or.inl (by rw [← h2]; exact sim_hi hX p))
  have hmem : ∀ m, (m = p ∨ m = q) → Jrel X Y p m := by
    rintro m (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact hpq
  have hclosed : ∀ a b, (Sim X a b ∨ Sim Y a b) → (a = p ∨ a = q) → (b = p ∨ b = q) := by
    intro a b h ha
    have hab : Jrel X Y p b := Relation.EqvGen.trans _ _ _ (hmem a ha) (sim_of_jrel_step h)
    have hsim : ∀ {c : ℝ → ℝ} (hc : Coord c), lo c p = p → hi c p = q → Sim c a b →
        ¬ Mid c b → (b = p ∨ b = q) := by
      intro c hc hlo hhi hab' hnmb
      have hsa : Sim c p a := by
        rcases ha with ha | ha
        · rw [ha]
          exact sim_refl c p
        · rw [ha]
          have := sim_hi hc p
          rwa [hhi] at this
      have hsb : Sim c p b := sim_trans hsa hab'
      have e1 := eq_lo_or_hi hc hsb hnmb
      rw [hlo, hhi] at e1
      exact e1
    rcases h with h | h
    · exact hsim hX h1 h2 h ((hnm b hab).1)
    · exact hsim hY h3 h4 h ((hnm b hab).2)
  have key : ∀ a b, Jrel X Y a b → ((a = p ∨ a = q) ↔ (b = p ∨ b = q)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact ⟨hclosed a b h, hclosed b a (h.imp sim_symm sim_symm)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key p w hw).1 (Or.inl rfl)

theorem sing_of_not_lt (hX : Coord X) {τ : ℝ} (h : ¬ lo X τ < hi X τ) :
    lo X τ = τ ∧ hi X τ = τ := by
  have h1 := lo_le hX τ
  have h2 := le_hi hX τ
  rw [not_lt] at h
  exact ⟨by linarith, by linarith⟩

theorem end_or (hX : Coord X) {τ : ℝ} (h : lo X τ < hi X τ) (hm : ¬ Mid X τ) :
    (lo X τ = τ ∧ τ < hi X τ) ∨ (lo X τ < τ ∧ hi X τ = τ) := by
  have h1 := lo_le hX τ
  have h2 := le_hi hX τ
  by_cases hl : lo X τ = τ
  · left
    exact ⟨hl, by linarith⟩
  · right
    have hl' : lo X τ < τ := lt_of_le_of_ne h1 hl
    refine ⟨hl', ?_⟩
    by_contra hh
    exact hm ⟨hl', lt_of_le_of_ne h2 (fun e => hh e.symm)⟩

theorem lo_lt_hi_of_sim (hX : Coord X) {a b : ℝ} (hab : a ≠ b) (h : Sim X a b) :
    lo X b < hi X b := by
  have h1 := sim_ge_lo hX (sim_symm h)
  have h2 := sim_le_hi hX (sim_symm h)
  have h3 := lo_le hX b
  have h4 := le_hi hX b
  by_contra h'
  rw [not_lt] at h'
  exact hab (le_antisymm (by linarith) (by linarith))

/-- A class with three times contains a middle point, or a time `τ` that is the left end of both
of its classes with different right ends, or the right end of both with different left ends. -/
theorem structure_cover (hS : Setup X Y η) {t1 t2 t3 : ℝ} (h12 : t1 < t2) (h23 : t2 < t3)
    (e12 : η t1 = η t2) (e23 : η t2 = η t3) :
    (∃ m, η m = η t1 ∧ (IsLocalMin X m ∨ IsLocalMin Y m)) ∨
    (∃ τ, η τ = η t1 ∧ lo X τ = τ ∧ lo Y τ = τ ∧ τ < hi X τ ∧ τ < hi Y τ ∧ hi X τ ≠ hi Y τ) ∨
    (∃ τ, η τ = η t1 ∧ hi X τ = τ ∧ hi Y τ = τ ∧ lo X τ < τ ∧ lo Y τ < τ ∧
      lo X τ ≠ lo Y τ) := by
  have hX := hS.coordX
  have hY := hS.coordY
  have hC : ∀ m, η m = η t1 ↔ Jrel X Y t1 m := fun m => by
    rw [eq_comm]
    exact hS.fib t1 m
  have J2 : Jrel X Y t1 t2 := (hS.fib t1 t2).1 e12
  have J3 : Jrel X Y t1 t3 := (hS.fib t1 t3).1 (e12.trans e23)
  have J1 : Jrel X Y t1 t1 := Relation.EqvGen.refl _
  by_cases hmid : ∃ m, Jrel X Y t1 m ∧ (Mid X m ∨ Mid Y m)
  · obtain ⟨m, hm, hmm⟩ := hmid
    left
    refine ⟨m, (hC m).2 hm, ?_⟩
    rcases hmm with h | h
    · exact Or.inl (h.isLocalMin hX)
    · exact Or.inr (h.isLocalMin hY)
  right
  have hnm : ∀ m, Jrel X Y t1 m → ¬ Mid X m ∧ ¬ Mid Y m := fun m hm =>
    ⟨fun h => hmid ⟨m, hm, Or.inl h⟩, fun h => hmid ⟨m, hm, Or.inr h⟩⟩
  have hboth : ∃ τ, Jrel X Y t1 τ ∧ lo X τ < hi X τ ∧ lo Y τ < hi Y τ := by
    by_contra hno
    have hno' : ∀ τ, Jrel X Y t1 τ → ¬ lo X τ < hi X τ ∨ ¬ lo Y τ < hi Y τ := by
      intro τ hτ
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact hno ⟨τ, hτ, hc.1, hc.2⟩
    have hin3 : ∀ {a b : ℝ}, (∀ w, Jrel X Y t1 w → w = a ∨ w = b) → False := fun {a b} h =>
      three_in_two h12 h23 (h t1 J1) (h t2 J2) (h t3 J3)
    rcases hno' t1 J1 with hx | hy
    · have hsx := sing_of_not_lt hX hx
      have hall : ∀ m, Sim Y t1 m → lo X m = m ∧ hi X m = m := by
        intro m hm
        by_cases hmt : m = t1
        · rw [hmt]
          exact hsx
        · apply sing_of_not_lt hX
          intro hlt
          have hrel : Jrel X Y t1 m := sim_of_jrel_step (Or.inr hm)
          rcases hno' m hrel with h | h
          · exact h hlt
          · exact h (lo_lt_hi_of_sim hY (Ne.symm hmt) hm)
      refine hin3 (a := lo Y t1) (b := hi Y t1) fun w hw => ?_
      exact eq_lo_or_hi hY (single_class hX hall hw) (hnm w hw).2
    · have hsy := sing_of_not_lt hY hy
      have hall : ∀ m, Sim X t1 m → lo Y m = m ∧ hi Y m = m := by
        intro m hm
        by_cases hmt : m = t1
        · rw [hmt]
          exact hsy
        · apply sing_of_not_lt hY
          intro hlt
          have hrel : Jrel X Y t1 m := sim_of_jrel_step (Or.inl hm)
          rcases hno' m hrel with h | h
          · exact h (lo_lt_hi_of_sim hX (Ne.symm hmt) hm)
          · exact h hlt
      refine hin3 (a := lo X t1) (b := hi X t1) fun w hw => ?_
      exact eq_lo_or_hi hX (single_class hY hall (jrel_swap.2 hw)) (hnm w hw).1
  obtain ⟨τ, hτ, hnx, hny⟩ := hboth
  have hnmτ := hnm τ hτ
  have hJτ : ∀ w, Jrel X Y τ w → Jrel X Y t1 w := fun w hw =>
    Relation.EqvGen.trans _ _ _ hτ hw
  have hJτ' : ∀ w, Jrel X Y t1 w → Jrel X Y τ w := fun w hw =>
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hτ) hw
  rcases end_or hX hnx hnmτ.1 with ⟨hxl, hxh⟩ | ⟨hxl, hxh⟩ <;>
    rcases end_or hY hny hnmτ.2 with ⟨hyl, hyh⟩ | ⟨hyl, hyh⟩
  · left
    refine ⟨τ, (hC τ).2 hτ, hxl, hyl, hxh, hyh, fun heq => ?_⟩
    have key : ∀ w, Jrel X Y τ w → w = τ ∨ w = hi X τ := fun w hw =>
      pair_class hX hY (p := τ) (q := hi X τ) hxl rfl hyl heq.symm
        (fun w' hw' => hnm w' (hJτ w' hw')) hw
    exact three_in_two h12 h23 (key t1 (hJτ' t1 J1)) (key t2 (hJτ' t2 J2))
      (key t3 (hJτ' t3 J3))
  · exact (not_lo_hi hY hX hS.noYX τ ⟨hyl, hxh⟩).elim
  · exact (not_lo_hi hX hY hS.noXY τ ⟨hxl, hyh⟩).elim
  · right
    refine ⟨τ, (hC τ).2 hτ, hxh, hyh, hxl, hyl, fun heq => ?_⟩
    have hJp : Jrel X Y t1 (lo X τ) :=
      Relation.EqvGen.trans _ _ _ hτ (sim_of_jrel_step (Or.inl (sim_lo hX τ)))
    have h2' : hi X (lo X τ) = τ := by
      rw [← hi_eq_of_sim hX (sim_lo hX τ), hxh]
    have h4' : hi Y (lo X τ) = τ := by
      rw [heq, ← hi_eq_of_sim hY (sim_lo hY τ), hyh]
    have h3' : lo Y (lo X τ) = lo X τ := by
      rw [heq, lo_lo hY]
    have key : ∀ w, Jrel X Y (lo X τ) w → w = lo X τ ∨ w = τ := fun w hw =>
      pair_class hX hY (p := lo X τ) (q := τ) (lo_lo hX τ) h2' h3' h4'
        (fun w' hw' => hnm w' (Relation.EqvGen.trans _ _ _ hJp hw')) hw
    have hs : ∀ w, Jrel X Y t1 w → Jrel X Y (lo X τ) w := fun w hw =>
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hJp) hw
    exact three_in_two h12 h23 (key t1 (hs t1 J1)) (key t2 (hs t2 J2)) (key t3 (hs t3 J3))

theorem exists_mem_Eset (hX : Coord X) (hY : Coord Y) {τ : ℝ} (h1 : τ < hi X τ)
    (h2 : hi X τ < hi Y τ) :
    ∃ (a b q r : ℚ) (n : ℕ), (a : ℝ) < b ∧ (b : ℝ) < q ∧ (q : ℝ) < r ∧
      τ ∈ Eset X Y a b q r n := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hq1
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show τ - 1 < τ by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h2
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_lt_hi_add hX τ (show 0 < (r : ℝ) - hi X τ by linarith)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < X τ - X s by linarith)
  refine ⟨a, b, q, r, n, ha2.trans hb1, hb2, hq2.trans hr1, ⟨ha2.le, hb1.le⟩, ?_, ?_,
    ⟨s, ⟨by linarith, by linarith⟩, by linarith⟩⟩
  · intro s' hs'
    exact (sim_hi hX τ).2 s' (by
      rw [uIcc_of_le (le_hi hX τ)]
      exact ⟨hs'.1, hs'.2.trans hq2.le⟩)
  · intro s' hs'
    exact (sim_hi hY τ).2 s' (by
      rw [uIcc_of_le (le_hi hY τ)]
      exact ⟨hs'.1, hs'.2.trans (hr2.le)⟩)

/-- The family of compact sets of times for the ordered pair `(X, Y)`. -/
def FamE (X Y : ℝ → ℝ) : Set (Set ℝ) :=
  ⋃ (a : ℚ) (b : ℚ) (q : ℚ) (r : ℚ) (n : ℕ) (_ : (a : ℝ) < b ∧ (b : ℝ) < q ∧ (q : ℝ) < r),
    {Eset X Y a b q r n}

theorem mem_FamE {a b q r : ℚ} {n : ℕ} (h1 : (a : ℝ) < b) (h2 : (b : ℝ) < q) (h3 : (q : ℝ) < r) :
    Eset X Y a b q r n ∈ FamE X Y := by
  simp only [FamE, mem_iUnion, mem_singleton_iff]
  exact ⟨a, b, q, r, n, ⟨h1, h2, h3⟩, rfl⟩

theorem FamE_countable : (FamE X Y).Countable := by
  unfold FamE
  exact countable_iUnion fun _ => countable_iUnion fun _ => countable_iUnion fun _ =>
    countable_iUnion fun _ => countable_iUnion fun _ => countable_iUnion fun _ =>
    countable_singleton _

theorem FamE_props (hS : Setup X Y η) (hmono : NowhereMonotone X) :
    ∀ E ∈ FamE X Y, IsCompact E ∧ interior E = ∅ ∧ InjOn η E := by
  intro E hE
  simp only [FamE, mem_iUnion, mem_singleton_iff] at hE
  obtain ⟨a, b, q, r, n, ⟨h1, h2, h3⟩, rfl⟩ := hE
  exact ⟨isCompact_Eset hS.coordX hS.coordY h3.le n, interior_Eset_eq_empty hmono h2 n,
    Eset_injOn hS h2 h3 n⟩

/-- The image of a set of times under time reversal. -/
def negImage (E : Set ℝ) : Set ℝ := (fun s => -s) '' E

theorem negImage_props {E : Set ℝ} {η : ℝ → ℂ}
    (h : IsCompact E ∧ interior E = ∅ ∧ InjOn (fun s => η (-s)) E) :
    IsCompact (negImage E) ∧ interior (negImage E) = ∅ ∧ InjOn η (negImage E) := by
  refine ⟨h.1.image continuous_neg, ?_, ?_⟩
  · refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hsub : Metric.ball (-x) ε ⊆ E := by
      intro y hy
      have hy' : -y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq] at hy ⊢
        rw [show -y - x = -(y - -x) by ring, abs_neg]
        exact hy
      obtain ⟨z, hz, hzy⟩ := interior_subset (hball hy')
      have hzy' : z = y := by simpa using hzy
      rw [← hzy']
      exact hz
    have hmem : -x ∈ interior E :=
      (Metric.isOpen_ball.subset_interior_iff).2 hsub (Metric.mem_ball_self hε)
    rw [h.2.1] at hmem
    exact hmem
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [h.2.2 hx' hy' hxy]

/-- The countable family of compact sets of times covering the triple points. -/
def SetS (X Y : ℝ → ℝ) : Set (Set ℝ) :=
  ((fun m : ℝ => ({m} : Set ℝ)) '' ({m | IsLocalMin X m} ∪ {m | IsLocalMin Y m})) ∪
  (FamE X Y ∪ FamE Y X ∪ negImage '' FamE (rev X) (rev Y) ∪ negImage '' FamE (rev Y) (rev X))

theorem SetS_countable (hX : Coord X) (hY : Coord Y) : (SetS X Y).Countable := by
  unfold SetS
  exact (((countable_isLocalMin hX).union (countable_isLocalMin hY)).image _).union
    ((((FamE_countable).union FamE_countable).union (FamE_countable.image _)).union
      (FamE_countable.image _))

theorem SetS_props (hS : Setup X Y η) (hXm : NowhereMonotone X) (hYm : NowhereMonotone Y) :
    ∀ E ∈ SetS X Y, IsCompact E ∧ interior E = ∅ ∧ InjOn η E := by
  intro E hE
  rcases hE with ⟨m, _, rfl⟩ | (((hE | hE) | ⟨E', hE', rfl⟩) | ⟨E', hE', rfl⟩)
  · exact ⟨isCompact_singleton, interior_singleton m, injOn_singleton _ _⟩
  · exact FamE_props hS hXm E hE
  · exact FamE_props (setup_swap hS) hYm E hE
  · exact negImage_props (FamE_props (setup_rev hS) (nowhereMonotone_rev hXm) E' hE')
  · exact negImage_props (FamE_props (setup_rev (setup_swap hS)) (nowhereMonotone_rev hYm) E' hE')

theorem SetS_cover (hS : Setup X Y η) {t1 t2 t3 : ℝ} (h12 : t1 < t2) (h23 : t2 < t3)
    (e12 : η t1 = η t2) (e23 : η t2 = η t3) : ∃ E ∈ SetS X Y, η t1 ∈ η '' E := by
  have hX := hS.coordX
  have hY := hS.coordY
  rcases structure_cover hS h12 h23 e12 e23 with
    ⟨m, hm, hmm⟩ | ⟨τ, hτ, h1, h2, h3, h4, h5⟩ | ⟨τ, hτ, h1, h2, h3, h4, h5⟩
  · exact ⟨{m}, Or.inl ⟨m, hmm, rfl⟩, m, rfl, hm⟩
  · rcases lt_or_gt_of_ne h5 with hlt | hgt
    · obtain ⟨a, b, q, r, n, hab, hbq, hqr, hmem⟩ := exists_mem_Eset hX hY h3 hlt
      exact ⟨Eset X Y a b q r n, Or.inr (Or.inl (Or.inl (Or.inl (mem_FamE hab hbq hqr)))),
        τ, hmem, hτ⟩
    · obtain ⟨a, b, q, r, n, hab, hbq, hqr, hmem⟩ := exists_mem_Eset hY hX h4 hgt
      exact ⟨Eset Y X a b q r n, Or.inr (Or.inl (Or.inl (Or.inr (mem_FamE hab hbq hqr)))),
        τ, hmem, hτ⟩
  · have hX' := coord_rev hX
    have hY' := coord_rev hY
    have e1 : hi (rev X) (-τ) = -lo X τ := hi_rev_neg X τ
    have e2 : hi (rev Y) (-τ) = -lo Y τ := hi_rev_neg Y τ
    rcases lt_or_gt_of_ne h5 with hlt | hgt
    · obtain ⟨a, b, q, r, n, hab, hbq, hqr, hmem⟩ := exists_mem_Eset hY' hX'
        (τ := -τ) (by rw [e2]; linarith) (by rw [e1, e2]; linarith)
      refine ⟨negImage (Eset (rev Y) (rev X) a b q r n),
        Or.inr (Or.inr ⟨_, mem_FamE hab hbq hqr, rfl⟩), τ, ⟨-τ, hmem, by simp⟩, hτ⟩
    · obtain ⟨a, b, q, r, n, hab, hbq, hqr, hmem⟩ := exists_mem_Eset hX' hY'
        (τ := -τ) (by rw [e1]; linarith) (by rw [e1, e2]; linarith)
      refine ⟨negImage (Eset (rev X) (rev Y) a b q r n),
        Or.inr (Or.inl (Or.inr ⟨_, mem_FamE hab hbq hqr, rfl⟩)), τ, ⟨-τ, hmem, by simp⟩, hτ⟩

end MatedCRT.PeanosphereTriplePoints
