import MatedCRT.Defs.WalkDisconnection
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Joint measurability of the walk disconnection event

The bounded joint Borel component of `walkDisconnectsBeforeHit`, as a function of the edge
multiplicities `m`, the target set `A`, the starting vertex `y` and the path `x`. The target set is coded
by a `Bool`-valued function `b`, `A = {v | b v = true}`, so that all four arguments carry product
σ-algebras (`ℤ → ℤ → ℕ`, `ℤ → Bool`, `ℤ`, `ℕ → ℤ`; all factors are discrete).

This is the countable integer-test argument of `notes/wpn-steps2/steps2-r3.tex:414-420`, made explicit:

* the trace `walkTraceBefore x (vHitTime A x)` is a countable union over the time `n` of finite avoidance
  conditions on the coordinates of `x` (`mem_walkTraceBefore_vHitTime_iff_bool`);
* reachability in the induced graph `G.induce S` is the existence of a finite path witness, a list of
  vertices of `S` (`exists_isFinitePath_of_reachable`, `reachable_of_isFinitePath`), so the absence of a
  path is a countable intersection of finite conditions;
* `graphDisconnects` is a countable intersection over the target vertices `a` of a finite-path condition
  (`graphDisconnects_iff_forall`, `walkDisconnectsBeforeHit_iff`).

The main results are `measurableSet_walkDisconnectsBeforeHit` and
`measurable_walkDisconnectsBeforeHit_indicator`. Reused: `natCast_lt_vExitTime_iff` of
`MatedCRT.Proofs.IDLA.Measurable`, and the definitions of `MatedCRT.Defs.WalkDisconnection`.
Not treated here: quantification over centres and radii, universal measurability, probability estimates.
-/

namespace MatedCRT

open MeasureTheory Set

/-- The parameter space `(m, b, y, x)` of the disconnection event: edge multiplicities `m`, target set
`A = {v | b v = true}` coded by `b`, starting vertex `y` and path `x`. -/
abbrev DisconParam : Type := (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × (ℕ → ℤ)

/-! ### The trace and the hitting time as countable path tests -/

/-- `k < vHitTime B x` iff the path avoids `B` up to time `k`. -/
theorem natCast_lt_vHitTime_iff {B : Set ℤ} {x : ℕ → ℤ} {k : ℕ} :
    (k : ℕ∞) < vHitTime B x ↔ ∀ j ≤ k, x j ∉ B := by
  unfold vHitTime
  simp only [natCast_lt_vExitTime_iff, mem_compl_iff]

/-- `w` lies in the trace `walkTraceBefore x (vHitTime A x)` iff the path is at `w` at some time `n` and has
avoided the target set up to time `n`: a countable union of finite avoidance conditions. -/
theorem mem_walkTraceBefore_vHitTime_iff_bool (b : ℤ → Bool) (x : ℕ → ℤ) (w : ℤ) :
    w ∈ walkTraceBefore x (vHitTime {v | b v = true} x) ↔
      ∃ n : ℕ, (∀ j ≤ n, ¬ b (x j) = true) ∧ x n = w := by
  simp [walkTraceBefore, natCast_lt_vHitTime_iff]

/-! ### Finite paths in an induced subgraph -/

/-- `IsFinitePath G S y a l`: the list `l` lists the vertices after `y` of a path of `G` from `y` to `a`
all of whose vertices lie in `S`. For `l = []` this says `y = a ∈ S`; for `w :: l` it says that `y ∈ S`,
that `y` and `w` are adjacent in `G`, and that `l` is a path from `w` to `a` in `S`. -/
def IsFinitePath (G : SimpleGraph ℤ) (S : Set ℤ) : ℤ → ℤ → List ℤ → Prop
  | y, a, [] => y = a ∧ y ∈ S
  | y, a, w :: l => y ∈ S ∧ G.Adj y w ∧ IsFinitePath G S w a l

theorem IsFinitePath.mem_start {G : SimpleGraph ℤ} {S : Set ℤ} {y a : ℤ} {l : List ℤ}
    (h : IsFinitePath G S y a l) : y ∈ S := by
  cases l with
  | nil => exact (show y = a ∧ y ∈ S from h).2
  | cons w l => exact (show y ∈ S ∧ G.Adj y w ∧ IsFinitePath G S w a l from h).1

/-- A walk in the induced subgraph `G.induce S` yields a finite path witness in `S`. -/
theorem exists_isFinitePath_of_reachable {G : SimpleGraph ℤ} {S : Set ℤ} {u v : S}
    (h : (G.induce S).Reachable u v) : ∃ l : List ℤ, IsFinitePath G S u.1 v.1 l := by
  obtain ⟨p⟩ := h
  induction p with
  | @nil x => exact ⟨[], show x.1 = x.1 ∧ x.1 ∈ S from ⟨rfl, x.2⟩⟩
  | @cons u' v' w' hadj _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨v'.1 :: l, show u'.1 ∈ S ∧ G.Adj u'.1 v'.1 ∧ IsFinitePath G S v'.1 w'.1 l from
      ⟨u'.2, hadj, hl⟩⟩

/-- A finite path witness in `S` yields a walk in the induced subgraph `G.induce S`. -/
theorem reachable_of_isFinitePath {G : SimpleGraph ℤ} {S : Set ℤ} (l : List ℤ) :
    ∀ {y a : ℤ} (hy : y ∈ S) (ha : a ∈ S), IsFinitePath G S y a l →
      (G.induce S).Reachable ⟨y, hy⟩ ⟨a, ha⟩ := by
  induction l with
  | nil =>
    intro y a hy ha h
    obtain ⟨rfl, _⟩ := (show y = a ∧ y ∈ S from h)
    exact SimpleGraph.Reachable.refl _
  | cons w l ih =>
    intro y a hy ha h
    obtain ⟨_, hyw, hwa⟩ := (show y ∈ S ∧ G.Adj y w ∧ IsFinitePath G S w a l from h)
    exact ((show (G.induce S).Adj ⟨y, hy⟩ ⟨w, hwa.mem_start⟩ from hyw).reachable).trans
      (ih hwa.mem_start ha hwa)

/-- `graphDisconnects` as a countable intersection: every target vertex `a ∈ A` is in `K`, or `y` is in
`K`, or no finite path from `y` to `a` avoids `K`. -/
theorem graphDisconnects_iff_forall (G : SimpleGraph ℤ) (K A : Set ℤ) (y : ℤ) :
    graphDisconnects G K y A ↔
      ∀ a ∈ A, y ∈ K ∨ a ∈ K ∨ ¬ ∃ l : List ℤ, IsFinitePath G Kᶜ y a l := by
  unfold graphDisconnects
  constructor
  · intro h a ha
    by_cases hyK : y ∈ K
    · exact Or.inl hyK
    by_cases hak : a ∈ K
    · exact Or.inr (Or.inl hak)
    refine Or.inr (Or.inr ?_)
    rintro ⟨l, hl⟩
    have hyK' : y ∈ Kᶜ := hyK
    have hak' : a ∈ Kᶜ := hak
    exact h hyK a ha hak (reachable_of_isFinitePath (G := G) (S := Kᶜ) l hyK' hak' hl)
  · intro h hy a ha hak hreach
    rcases h a ha with h1 | h1 | h1
    · exact hy h1
    · exact hak h1
    · exact h1 (exists_isFinitePath_of_reachable hreach)

/-- The disconnection event of the walk, in terms of the trace and finite paths. -/
theorem walkDisconnectsBeforeHit_iff (m : ℤ → ℤ → ℕ) (A : Set ℤ) (y : ℤ) (x : ℕ → ℤ) :
    walkDisconnectsBeforeHit m A y x ↔
      ∀ a ∈ A, y ∈ walkTraceBefore x (vHitTime A x) ∨ a ∈ walkTraceBefore x (vHitTime A x) ∨
        ¬ ∃ l : List ℤ, IsFinitePath (adjGraph m) (walkTraceBefore x (vHitTime A x))ᶜ y a l :=
  graphDisconnects_iff_forall _ _ _ _

/-- The trace read off a parameter `p = (m, b, y, x)`. -/
abbrev traceOf (p : DisconParam) : Set ℤ :=
  walkTraceBefore p.2.2.2 (vHitTime {v | p.2.1 v = true} p.2.2.2)

/-! ### Measurable coordinates of the parameter space -/

theorem measurable_edgeMult (u w : ℤ) : Measurable fun p : DisconParam => p.1 u w :=
  (measurable_pi_apply w).comp ((measurable_pi_apply u).comp measurable_fst)

theorem measurable_targetCode (z : ℤ) : Measurable fun p : DisconParam => p.2.1 z :=
  (measurable_pi_apply z).comp (measurable_fst.comp measurable_snd)

theorem measurable_startVertex : Measurable fun p : DisconParam => p.2.2.1 :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_pathCoord (k : ℕ) : Measurable fun p : DisconParam => p.2.2.2 k :=
  (measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurableSet_target_eq (z : ℤ) (c : Bool) :
    MeasurableSet {p : DisconParam | p.2.1 z = c} :=
  measurable_targetCode z (measurableSet_singleton c)

theorem measurableSet_start_eq (z : ℤ) : MeasurableSet {p : DisconParam | p.2.2.1 = z} :=
  measurable_startVertex (measurableSet_singleton z)

theorem measurableSet_path_eq (k : ℕ) (z : ℤ) : MeasurableSet {p : DisconParam | p.2.2.2 k = z} :=
  measurable_pathCoord k (measurableSet_singleton z)

/-- The coordinate of the path is read through the target code: `{p | b (x k) = c}` is measurable, a
countable union over the value `z = x k` of the products of two coordinate events. -/
theorem measurableSet_target_path (k : ℕ) (c : Bool) :
    MeasurableSet {p : DisconParam | p.2.1 (p.2.2.2 k) = c} := by
  have h : {p : DisconParam | p.2.1 (p.2.2.2 k) = c} =
      ⋃ z : ℤ, {p : DisconParam | p.2.2.2 k = z} ∩ {p : DisconParam | p.2.1 z = c} := by
    ext p
    simp
  rw [h]
  exact MeasurableSet.iUnion fun z =>
    (measurableSet_path_eq k z).inter (measurableSet_target_eq z c)

/-- The trace membership event `{p | w ∈ traceOf p}` is measurable. -/
theorem measurableSet_mem_traceOf (w : ℤ) : MeasurableSet {p : DisconParam | w ∈ traceOf p} := by
  have h : {p : DisconParam | w ∈ traceOf p} =
      ⋃ n : ℕ, (⋂ j ∈ Iic n, {p : DisconParam | p.2.1 (p.2.2.2 j) = true}ᶜ) ∩
        {p : DisconParam | p.2.2.2 n = w} := by
    ext p
    simp [traceOf, mem_walkTraceBefore_vHitTime_iff_bool]
  rw [h]
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ (measurableSet_path_eq n w)
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    (measurableSet_target_path j true).compl

/-- The adjacency event `{p | (adjGraph m).Adj u w}` of the multigraph `m = p.1`. -/
theorem measurableSet_adj (u w : ℤ) : MeasurableSet {p : DisconParam | (adjGraph p.1).Adj u w} := by
  have h : {p : DisconParam | (adjGraph p.1).Adj u w} =
      {_p : DisconParam | u ≠ w} ∩
        ({p : DisconParam | p.1 u w ≠ 0} ∪ {p : DisconParam | p.1 w u ≠ 0}) := by
    ext p
    simp [adjGraph, SimpleGraph.fromRel_adj]
  rw [h]
  exact (MeasurableSet.const (u ≠ w)).inter
    ((measurable_edgeMult u w (measurableSet_singleton (0 : ℕ)).compl).union
      (measurable_edgeMult w u (measurableSet_singleton (0 : ℕ)).compl))

/-- The finite-path condition from a fixed start `y₀` and list `l`, with the trace removed. -/
theorem measurableSet_isFinitePath (a : ℤ) (l : List ℤ) :
    ∀ y₀ : ℤ, MeasurableSet {p : DisconParam | IsFinitePath (adjGraph p.1) (traceOf p)ᶜ y₀ a l} := by
  induction l with
  | nil =>
    intro y₀
    exact (MeasurableSet.const (y₀ = a)).inter (measurableSet_mem_traceOf y₀).compl
  | cons w l ih =>
    intro y₀
    exact (measurableSet_mem_traceOf y₀).compl.inter ((measurableSet_adj y₀ w).inter (ih w))

/-- The existence of a finite path from `y₀` to `a` avoiding the trace: a countable union over lists. -/
theorem measurableSet_exists_isFinitePath (a y₀ : ℤ) :
    MeasurableSet {p : DisconParam | ∃ l : List ℤ, IsFinitePath (adjGraph p.1) (traceOf p)ᶜ y₀ a l} := by
  have h : {p : DisconParam | ∃ l : List ℤ, IsFinitePath (adjGraph p.1) (traceOf p)ᶜ y₀ a l} =
      ⋃ l : List ℤ, {p : DisconParam | IsFinitePath (adjGraph p.1) (traceOf p)ᶜ y₀ a l} := by
    ext p
    simp
  rw [h]
  exact MeasurableSet.iUnion fun l => measurableSet_isFinitePath a l y₀

/-! ### Closure of measurable events under the logical operations used -/

/-- A predicate whose start vertex is the coordinate `p.2.2.1`: measurable once each fixed start is. -/
theorem measurableSet_of_start (F : ℤ → Set DisconParam) (hF : ∀ y₀ : ℤ, MeasurableSet (F y₀)) :
    MeasurableSet {p : DisconParam | p ∈ F p.2.2.1} := by
  have h : {p : DisconParam | p ∈ F p.2.2.1} = ⋃ y₀ : ℤ, {p : DisconParam | p.2.2.1 = y₀} ∩ F y₀ := by
    ext p
    simp
  rw [h]
  exact MeasurableSet.iUnion fun y₀ => (measurableSet_start_eq y₀).inter (hF y₀)

theorem measurableSet_setOf_forall_int {Φ : ℤ → DisconParam → Prop}
    (h : ∀ a : ℤ, MeasurableSet {p : DisconParam | Φ a p}) :
    MeasurableSet {p : DisconParam | ∀ a : ℤ, Φ a p} := by
  have h' : {p : DisconParam | ∀ a : ℤ, Φ a p} = ⋂ a : ℤ, {p : DisconParam | Φ a p} := by
    ext p
    simp
  rw [h']
  exact MeasurableSet.iInter h

theorem measurableSet_setOf_imp {P Q : DisconParam → Prop}
    (hP : MeasurableSet {p : DisconParam | P p}) (hQ : MeasurableSet {p : DisconParam | Q p}) :
    MeasurableSet {p : DisconParam | P p → Q p} := by
  have h : {p : DisconParam | P p → Q p} = {p : DisconParam | P p}ᶜ ∪ {p : DisconParam | Q p} := by
    ext p
    simp [imp_iff_not_or]
  rw [h]
  exact hP.compl.union hQ

theorem measurableSet_setOf_or {P Q : DisconParam → Prop}
    (hP : MeasurableSet {p : DisconParam | P p}) (hQ : MeasurableSet {p : DisconParam | Q p}) :
    MeasurableSet {p : DisconParam | P p ∨ Q p} := by
  have h : {p : DisconParam | P p ∨ Q p} = {p : DisconParam | P p} ∪ {p : DisconParam | Q p} := by
    ext p
    simp
  rw [h]
  exact hP.union hQ

/-! ### The disconnection event: joint measurability and its bounded indicator -/

/-- The disconnection event `{p | walkDisconnectsBeforeHit m A y x}` is a measurable subset of the
parameter space `(m, b, y, x)`: it is a countable intersection over the target vertices `a` of conditions
built from the trace and from countably many finite path tests. -/
theorem measurableSet_walkDisconnectsBeforeHit :
    MeasurableSet {p : DisconParam |
      walkDisconnectsBeforeHit p.1 {v | p.2.1 v = true} p.2.2.1 p.2.2.2} := by
  have h : {p : DisconParam | walkDisconnectsBeforeHit p.1 {v | p.2.1 v = true} p.2.2.1 p.2.2.2} =
      {p : DisconParam | ∀ a : ℤ, p.2.1 a = true →
        (p.2.2.1 ∈ traceOf p ∨ a ∈ traceOf p ∨
          ¬ ∃ l : List ℤ, IsFinitePath (adjGraph p.1) (traceOf p)ᶜ p.2.2.1 a l)} := by
    ext p
    exact walkDisconnectsBeforeHit_iff p.1 {v | p.2.1 v = true} p.2.2.1 p.2.2.2
  rw [h]
  refine measurableSet_setOf_forall_int fun a => measurableSet_setOf_imp
    (measurableSet_target_eq a true) (measurableSet_setOf_or ?_ (measurableSet_setOf_or
      (measurableSet_mem_traceOf a) ?_))
  · exact measurableSet_of_start (fun y₀ => {p : DisconParam | y₀ ∈ traceOf p})
      (fun y₀ => measurableSet_mem_traceOf y₀)
  · exact (measurableSet_of_start (fun y₀ => {p : DisconParam | ∃ l : List ℤ,
      IsFinitePath (adjGraph p.1) (traceOf p)ᶜ y₀ a l})
      (fun y₀ => measurableSet_exists_isFinitePath a y₀)).compl

open Classical in
/-- Bounded joint Borel component: the indicator of the disconnection event is a measurable function of
`(m, b, y, x)` with values in `[0, 1]`. -/
theorem measurable_walkDisconnectsBeforeHit_indicator :
    Measurable (fun p : DisconParam =>
      if walkDisconnectsBeforeHit p.1 {v | p.2.1 v = true} p.2.2.1 p.2.2.2 then (1 : ℝ) else 0) ∧
    ∀ p : DisconParam,
      (if walkDisconnectsBeforeHit p.1 {v | p.2.1 v = true} p.2.2.1 p.2.2.2 then (1 : ℝ) else 0) ∈
        Icc (0 : ℝ) 1 := by
  refine ⟨Measurable.ite measurableSet_walkDisconnectsBeforeHit measurable_const measurable_const, ?_⟩
  intro p
  split_ifs <;> norm_num

/-- Pull-back along a measurable state map `Φ : Ω → (m, b, y, x)`: the disconnection event of the state
`Φ ω` is measurable in `ω`. This is the form used when the parameters are random. -/
theorem measurableSet_walkDisconnectsBeforeHit_comp {Ω : Type*} [MeasurableSpace Ω]
    {Φ : Ω → DisconParam} (hΦ : Measurable Φ) :
    MeasurableSet {ω : Ω |
      walkDisconnectsBeforeHit (Φ ω).1 {v | (Φ ω).2.1 v = true} (Φ ω).2.2.1 (Φ ω).2.2.2} :=
  hΦ measurableSet_walkDisconnectsBeforeHit

open Classical in
/-- Pull-back of the bounded indicator along a measurable state map `Φ : Ω → (m, b, y, x)`. -/
theorem measurable_walkDisconnectsBeforeHit_indicator_comp {Ω : Type*} [MeasurableSpace Ω]
    {Φ : Ω → DisconParam} (hΦ : Measurable Φ) :
    Measurable (fun ω : Ω =>
      if walkDisconnectsBeforeHit (Φ ω).1 {v | (Φ ω).2.1 v = true} (Φ ω).2.2.1 (Φ ω).2.2.2
      then (1 : ℝ) else 0) :=
  measurable_walkDisconnectsBeforeHit_indicator.1.comp hΦ

end MatedCRT
