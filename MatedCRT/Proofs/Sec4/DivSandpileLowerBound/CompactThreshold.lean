import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.InnerNeighborhoodMeasurable

/-! # Compact threshold tests for random inner neighbourhoods -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- An inequality on a closed superlevel set in a compact space is equivalent
to inequalities on slightly larger open superlevel sets with relaxed bounds. -/
theorem compact_superlevel_inequality_iff {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    (∀ x, a ≤ f x → b ≤ g x) ↔
      ∀ m : ℕ, ∃ n : ℕ, ∀ x, a - 1 / ((n : ℝ) + 1) < f x →
        b - 1 / ((m : ℝ) + 1) ≤ g x := by
  constructor
  · intro h m
    let B : Set X := {x | g x ≤ b - 1 / ((m : ℝ) + 1)}
    have hBclosed : IsClosed B := isClosed_le hg continuous_const
    have hBcompact : IsCompact B := hBclosed.isCompact
    by_cases hB : B.Nonempty
    · obtain ⟨z, hz, hmax⟩ := hBcompact.exists_isMaxOn hB hf.continuousOn
      have hzlt : f z < a := by
        by_contra hzge
        have hz' := h z (le_of_not_gt hzge)
        have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        change g z ≤ b - 1 / ((m : ℝ) + 1) at hz
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hzlt)
      refine ⟨n, ?_⟩
      intro x hx
      by_contra hxg
      have hxB : x ∈ B := le_of_lt (lt_of_not_ge hxg)
      have hmax' := hmax hxB
      change f x ≤ f z at hmax'
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      by_contra hxg
      exact hB ⟨x, le_of_lt (lt_of_not_ge hxg)⟩
  · intro h x hax
    by_contra hx
    have hgap : 0 < b - g x := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
    obtain ⟨n, hn⟩ := h m
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hgx := hn x (by linarith)
    linarith

/-- Relaxed open-superlevel tests need only be checked on a dense set. -/
theorem compact_superlevel_inequality_iff_dense {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (D : Set X) (hD : Dense D) (a b : ℝ) :
    (∀ x, a ≤ f x → b ≤ g x) ↔
      ∀ m : ℕ, ∃ n : ℕ, ∀ x ∈ D, a - 1 / ((n : ℝ) + 1) < f x →
        b - 1 / ((m : ℝ) + 1) ≤ g x := by
  rw [compact_superlevel_inequality_iff f g hf hg a b]
  constructor
  · intro h m
    obtain ⟨n, hn⟩ := h m
    exact ⟨n, fun x _ => hn x⟩
  · intro h m
    obtain ⟨n, hn⟩ := h m
    refine ⟨n, ?_⟩
    intro x hfx
    by_contra hxg
    let U : Set X := {y | a - 1 / ((n : ℝ) + 1) < f y ∧
      g y < b - 1 / ((m : ℝ) + 1)}
    have hU : IsOpen U := (isOpen_lt continuous_const hf).inter (isOpen_lt hg continuous_const)
    obtain ⟨y, hyD, hyU⟩ := hD.exists_mem_open hU ⟨x, hfx, lt_of_not_ge hxg⟩
    exact (not_le_of_gt hyU.2) (hn y hyD hyU.1)

/-- Null measurability of a random inequality over a compact superlevel set,
from countably many open-level tests and almost-sure continuity. -/
theorem nullMeasurableSet_compact_superlevel_inequality
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (P : Measure Ω) (F G : Ω → X → ℝ) (D : Set X) (hDc : D.Countable) (hD : Dense D)
    (a b : ℝ)
    (hF : ∀ n : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | a - 1 / ((n : ℝ) + 1) < F ω x} P)
    (hG : ∀ m : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | b - 1 / ((m : ℝ) + 1) ≤ G ω x} P)
    (hcont : ∀ᵐ ω ∂P, Continuous (F ω) ∧ Continuous (G ω)) :
    NullMeasurableSet {ω | ∀ x, a ≤ F ω x → b ≤ G ω x} P := by
  let : Countable D := hDc.to_subtype
  have htest : ∀ m n : ℕ, ∀ x : D, NullMeasurableSet
      {ω | a - 1 / ((n : ℝ) + 1) < F ω x →
        b - 1 / ((m : ℝ) + 1) ≤ G ω x} P := by
    intro m n x
    convert (hF n x x.property).compl.union (hG m x x.property) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  have hm := NullMeasurableSet.iInter fun m =>
    NullMeasurableSet.iUnion fun n => NullMeasurableSet.iInter (htest m n)
  apply hm.congr
  filter_upwards [hcont] with ω hω
  apply propext
  simpa only [mem_iInter, mem_iUnion, mem_ofPred_eq, Subtype.forall] using
    (compact_superlevel_inequality_iff_dense (F ω) (G ω) hω.1 hω.2 D hD a b).symm

/-- The compact superlevel criterion localized to a null-measurable event;
continuity and the point tests are required only on that event. -/
theorem nullMeasurableSet_compact_superlevel_inequality_on
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (P : Measure Ω) (E : Set Ω) (hE : NullMeasurableSet E P)
    (F G : Ω → X → ℝ) (D : Set X) (hDc : D.Countable) (hD : Dense D) (a b : ℝ)
    (hF : ∀ n : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | ω ∈ E ∧ a - 1 / ((n : ℝ) + 1) < F ω x} P)
    (hG : ∀ m : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | ω ∈ E ∧ b - 1 / ((m : ℝ) + 1) ≤ G ω x} P)
    (hcont : ∀ᵐ ω ∂P, ω ∈ E → Continuous (F ω) ∧ Continuous (G ω)) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∀ x, a ≤ F ω x → b ≤ G ω x} P := by
  let : Countable D := hDc.to_subtype
  have htest : ∀ m n : ℕ, ∀ x : D, NullMeasurableSet
      {ω | ω ∈ E ∧ (a - 1 / ((n : ℝ) + 1) < F ω x →
        b - 1 / ((m : ℝ) + 1) ≤ G ω x)} P := by
    intro m n x
    convert (hE.diff (hF n x x.property)).union (hG m x x.property) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_union, Set.mem_sdiff, imp_iff_not_or]
    tauto
  have hm := hE.inter (NullMeasurableSet.iInter fun m =>
    NullMeasurableSet.iUnion fun n => NullMeasurableSet.iInter (htest m n))
  apply hm.congr
  filter_upwards [hcont] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_iInter, mem_iUnion, mem_ofPred_eq, Subtype.forall]
  constructor
  · rintro ⟨hωE, h⟩
    have hc := hω hωE
    refine ⟨hωE, (compact_superlevel_inequality_iff_dense (F ω) (G ω) hc.1 hc.2 D hD a b).mpr ?_⟩
    intro m
    obtain ⟨n, hn⟩ := h m
    exact ⟨n, fun x hx => (hn x hx).2⟩
  · rintro ⟨hωE, h⟩
    have hc := hω hωE
    have h' := (compact_superlevel_inequality_iff_dense (F ω) (G ω) hc.1 hc.2 D hD a b).mp h
    refine ⟨hωE, ?_⟩
    intro m
    obtain ⟨n, hn⟩ := h' m
    exact ⟨n, fun x hx => ⟨hωE, hn x hx⟩⟩

end MatedCRT
