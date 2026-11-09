import MatedCRT.Defs.Notation
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Compactness.Compact

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §2): measurable inclusion codes for the cluster

For a countable dense set `D ⊆ ℂ` and an open set `S ⊆ ℂ` (the cluster `cluster μ ρ 0 t`,
Harmonic-Balls-LQG Defs/Obstacle.lean:69), the cluster family is `Λ = interior (closure S)`
(`SatisfiesObstacleCharacterization`, MatedCRT/Defs/Setting.lean:262). Two deterministic facts:
* `ball c r ⊆ Λ` iff every point `q ∈ D ∩ ball c r` lies in `closure S`, i.e. `S ∩ D` approaches `q` at every scale;
* for compact `C`, `C ⊆ Λ` iff finitely many balls `ball d (1/(n+1))`, `d ∈ D`, lie in `Λ` and cover `C`
  (Lindelöf/compactness, Armitage-Gardiner).
Measure-theoretic consequence: if `S ω` is open for almost every `ω` and each point event `{ω | d ∈ S ω}`,
`d ∈ D`, is null measurable, then `{ω | C ⊆ interior (closure (S ω))}` is null measurable for compact `C`.
The point events are the threshold events of `nullMeasurableSet_threshold` (MatedCRT/FirstPass/S1c/Measurability.lean).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- The rational-type balls of the covering: centre `d ∈ D`, radius `1/(n+1)`. -/
def codeBall (D : Set ℂ) (i : D × ℕ) : Set ℂ :=
  ball (i.1 : ℂ) (1 / ((i.2 : ℝ) + 1))

/-- A ball lies in the interior of the closure of an open set iff its points of `D` lie in the closure. -/
theorem inclBall_iff_dense {D S : Set ℂ} (hD : Dense D) (hS : IsOpen S) (c : ℂ) (r : ℝ) :
    ball c r ⊆ interior (closure S) ↔
      ∀ q ∈ D ∩ ball c r, ∀ n : ℕ, ∃ p ∈ D ∩ S, dist p q < 1 / ((n : ℝ) + 1) := by
  constructor
  · intro h q hq n
    have hqS : q ∈ closure S := interior_subset (h hq.2)
    obtain ⟨b, hbS, hb⟩ := Metric.mem_closure_iff.1 hqS (1 / ((n : ℝ) + 1)) (by positivity)
    have hU : IsOpen (S ∩ ball q (1 / ((n : ℝ) + 1))) := hS.inter isOpen_ball
    obtain ⟨p, hpD, hpU⟩ := hD.exists_mem_open hU ⟨b, hbS, by rw [mem_ball, dist_comm]; exact hb⟩
    exact ⟨p, ⟨hpD, hpU.1⟩, mem_ball.1 hpU.2⟩
  · intro h
    have hsub : ball c r ∩ D ⊆ closure S := by
      intro q hq
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      obtain ⟨p, ⟨_, hpS⟩, hdist⟩ := h q ⟨hq.2, hq.1⟩ n
      exact ⟨p, hpS, by rw [dist_comm]; exact lt_trans hdist hn⟩
    have hcl : ball c r ⊆ closure S :=
      (hD.open_subset_closure_inter (isOpen_ball : IsOpen (ball c r))).trans
        (closure_minimal hsub isClosed_closure)
    exact ((isOpen_ball : IsOpen (ball c r))).subset_interior_iff.2 hcl

/-- A compact set lies in the interior of the closure iff finitely many code balls lie in it and cover it. -/
theorem inclCompact_iff_cover {D S : Set ℂ} (hD : Dense D) {C : Set ℂ} (hC : IsCompact C) :
    C ⊆ interior (closure S) ↔
      ∃ F : Finset (D × ℕ), (C ⊆ ⋃ i ∈ F, codeBall D i) ∧
        ∀ i ∈ F, codeBall D i ⊆ interior (closure S) := by
  classical
  constructor
  · intro hCΛ
    have hΛo : IsOpen (interior (closure S)) := isOpen_interior
    have hcover : ∀ x ∈ C, ∃ i : D × ℕ, x ∈ codeBall D i ∧ codeBall D i ⊆ interior (closure S) := by
      intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΛo x (hCΛ hx)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hU : IsOpen (ball x (1 / ((n : ℝ) + 1))) := isOpen_ball
      obtain ⟨d, hdD, hd⟩ := hD.exists_mem_open hU ⟨x, mem_ball_self hpos⟩
      have hdx : dist d x < 1 / ((n : ℝ) + 1) := mem_ball.1 hd
      refine ⟨(⟨d, hdD⟩, n), ?_, ?_⟩
      · show x ∈ ball d (1 / ((n : ℝ) + 1))
        rw [mem_ball, dist_comm]
        exact hdx
      · intro y hy
        apply hball
        have hy' : dist y d < 1 / ((n : ℝ) + 1) := mem_ball.1 hy
        rw [mem_ball]
        have := dist_triangle y d x
        linarith
    let U : {i : D × ℕ // codeBall D i ⊆ interior (closure S)} → Set ℂ := fun i => codeBall D i.1
    have hUo : ∀ i, IsOpen (U i) := fun i => isOpen_ball
    have hcov : C ⊆ ⋃ i, U i := by
      intro x hx
      obtain ⟨i, hxi, hiΛ⟩ := hcover x hx
      exact mem_iUnion.2 ⟨⟨i, hiΛ⟩, hxi⟩
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUo hcov
    refine ⟨t.image Subtype.val, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, hxi⟩
    · intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hj
      exact i.2
  · rintro ⟨F, hCF, hF⟩ x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hCF hx)
    exact hF i hi hxi

/-- Null measurability of `{ω | ball c r ⊆ interior (closure (S ω))}` from the point events `{d ∈ S ω}`, `d ∈ D`. -/
theorem nullMeasurableSet_inclBall {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hDc : D.Countable) (hD : Dense D) {S : Ω → Set ℂ}
    (hopen : ∀ᵐ ω ∂P, IsOpen (S ω)) (hpt : ∀ d ∈ D, NullMeasurableSet {ω | d ∈ S ω} P)
    (c : ℂ) (r : ℝ) :
    NullMeasurableSet {ω | ball c r ⊆ interior (closure (S ω))} P := by
  have : Countable (D ∩ ball c r : Set ℂ) := (hDc.mono Set.inter_subset_left).to_subtype
  have : Countable D := hDc.to_subtype
  have hpiece : ∀ (q : ↥(D ∩ ball c r : Set ℂ)) (n : ℕ), NullMeasurableSet
      (⋃ p : D, {ω | (p : ℂ) ∈ S ω ∧ dist (p : ℂ) (q : ℂ) < 1 / ((n : ℝ) + 1)}) P := by
    intro q n
    refine NullMeasurableSet.iUnion fun p => ?_
    have hset : {ω | (p : ℂ) ∈ S ω ∧ dist (p : ℂ) (q : ℂ) < 1 / ((n : ℝ) + 1)} =
        {_ω | dist (p : ℂ) (q : ℂ) < 1 / ((n : ℝ) + 1)} ∩ {ω | (p : ℂ) ∈ S ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_inter_iff]
      exact and_comm
    rw [hset]
    exact (MeasurableSet.const _).nullMeasurableSet.inter (hpt (p : ℂ) p.2)
  have hG : NullMeasurableSet (⋂ (q : ↥(D ∩ ball c r : Set ℂ)), ⋂ (n : ℕ), ⋃ p : D,
      {ω | (p : ℂ) ∈ S ω ∧ dist (p : ℂ) (q : ℂ) < 1 / ((n : ℝ) + 1)}) P :=
    NullMeasurableSet.iInter fun q => NullMeasurableSet.iInter fun n => hpiece q n
  refine NullMeasurableSet.congr hG (Filter.eventuallyEqSet_iff.2 (hopen.mono fun ω hω => ?_))
  simp only [Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [inclBall_iff_dense hD hω c r]
  constructor
  · intro h q hq n
    obtain ⟨p, hpS, hd⟩ := h ⟨q, hq⟩ n
    exact ⟨p.1, ⟨p.2, hpS⟩, hd⟩
  · intro h q n
    obtain ⟨p, ⟨hpD, hpS⟩, hd⟩ := h q.1 q.2 n
    exact ⟨⟨p, hpD⟩, hpS, hd⟩

/-- Null measurability of `{ω | C ⊆ interior (closure (S ω))}` for compact `C` (the cluster inclusion event). -/
theorem nullMeasurableSet_inclCompact {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hDc : D.Countable) (hD : Dense D) {S : Ω → Set ℂ}
    (hopen : ∀ᵐ ω ∂P, IsOpen (S ω)) (hpt : ∀ d ∈ D, NullMeasurableSet {ω | d ∈ S ω} P)
    {C : Set ℂ} (hC : IsCompact C) :
    NullMeasurableSet {ω | C ⊆ interior (closure (S ω))} P := by
  have : Countable D := hDc.to_subtype
  have hball : ∀ i : D × ℕ, NullMeasurableSet {ω | codeBall D i ⊆ interior (closure (S ω))} P :=
    fun i => nullMeasurableSet_inclBall hDc hD hopen hpt (i.1 : ℂ) (1 / ((i.2 : ℝ) + 1))
  have hunion : {ω | C ⊆ interior (closure (S ω))} =
      ⋃ F : Finset (D × ℕ), {ω | (C ⊆ ⋃ i ∈ F, codeBall D i) ∧
        ∀ i ∈ F, codeBall D i ⊆ interior (closure (S ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    exact inclCompact_iff_cover hD hC
  rw [hunion]
  refine NullMeasurableSet.iUnion fun F => ?_
  rw [Set.ofPred_and]
  refine (MeasurableSet.const _).nullMeasurableSet.inter ?_
  have hF : {ω | ∀ i ∈ F, codeBall D i ⊆ interior (closure (S ω))} =
      ⋂ i : F, {ω | codeBall D i.1 ⊆ interior (closure (S ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter]
    exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩
  rw [hF]
  exact NullMeasurableSet.iInter fun i => hball i.1

end MatedCRT.S5c
