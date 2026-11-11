import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Erosion index and Borel measurability of the random-compact infimum

Component of the repaired measurability step `StoppedInteriorMeasurableStep`
(`MatedCRT/Proofs/Sec5/StoppedInterior.lean`).

For a nonempty compact `K ⊆ ℂ` and a continuous `f : A → ℝ` on a compact set `A ⊆ ℂ`, the erosion index is
`J_A(K) = {x ∈ A : closedBall x δ ⊆ K}` and the erosion minimum is `m(K, f) = inf_{x ∈ J_A(K)} f x`, with the real
convention `inf ∅ = 0`. For compact `A` the index set is compact, so the infimum is attained and is the minimum of the
source. The main results:

* `isClosed_closedBall_subset`: the relation `closedBall x δ ⊆ K` is closed in the Hausdorff topology on nonempty
  compacts times the centre, so the erosion index is upper semicontinuous.
* `measurable_erodedMin`: `m` is Borel on `NonemptyCompacts ℂ × C(A, ℝ)` (Hausdorff times compact-open topology, which
  is the uniform topology on the compact `A`), by closed projection along the compact factor `A` and
  `F_σ` strict sublevel sets.
* `measurable_erodedMin_comp`: `ω ↦ m (K ω) (f ω)` is measurable whenever `ω ↦ (K ω, f ω)` is measurable.
* `closedBall_subset_closure_iff`: the regular-open identity `closedBall x δ ⊆ closure Λ ↔ δ ≤ infDist x Λᶜ`
  (Theorem 1.1(a) regularity).

Nothing here assumes a probability space, a field, or a cited result.
-/

open Metric Set Filter Topology MeasureTheory TopologicalSpace

noncomputable section

namespace MatedCRT.StoppedInteriorMargin

/-- The relation `closedBall x δ ⊆ K` between a nonempty compact `K` (Hausdorff topology) and a centre `x` is closed.
If `closedBall x_n δ ⊆ K_n` and `(K_n, x_n) → (K, x)`, then every `y` with `dist y x ≤ δ` lies in `K`: the translate
`y - x + x_n` lies in `K_n`, and `infDist` to `K` is at most `dist x x_n + hausdorffDist K_n K`. -/
theorem isClosed_closedBall_subset (δ : ℝ) :
    IsClosed {q : NonemptyCompacts ℂ × ℂ | closedBall q.2 δ ⊆ (q.1 : Set ℂ)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro qs q hqs hlim
  have hK : Tendsto (fun n => dist (qs n).1 q.1) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((continuous_fst.tendsto q).comp hlim)
  have hx : Tendsto (fun n => dist q.2 (qs n).2) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.1 ((continuous_snd.tendsto q).comp hlim)).congr fun n => dist_comm _ _
  have hsum : Tendsto (fun n => dist q.2 (qs n).2 + dist (qs n).1 q.1) atTop (𝓝 0) := by
    simpa using hx.add hK
  show closedBall q.2 δ ⊆ (q.1 : Set ℂ)
  intro y hy
  have hdy : dist y q.2 ≤ δ := mem_closedBall.1 hy
  have hbound : ∀ n, infDist y (q.1 : Set ℂ) ≤ dist q.2 (qs n).2 + dist (qs n).1 q.1 := by
    intro n
    have hsub : closedBall (qs n).2 δ ⊆ (qs n).1 := hqs n
    have hball : y - q.2 + (qs n).2 ∈ closedBall (qs n).2 δ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, ← dist_eq_norm]
      exact hdy
    have hmem : y - q.2 + (qs n).2 ∈ ((qs n).1 : Set ℂ) := hsub hball
    have h1 : infDist (y - q.2 + (qs n).2) ((qs n).1 : Set ℂ) = 0 := infDist_zero_of_mem hmem
    have hfin : hausdorffEDist ((qs n).1 : Set ℂ) (q.1 : Set ℂ) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded (qs n).1.nonempty q.1.nonempty
        (qs n).1.isCompact.isBounded q.1.isCompact.isBounded
    have h2 := infDist_le_infDist_add_hausdorffDist (x := y - q.2 + (qs n).2) hfin
    have h3 : infDist y (q.1 : Set ℂ) ≤
        infDist (y - q.2 + (qs n).2) (q.1 : Set ℂ) + dist y (y - q.2 + (qs n).2) :=
      infDist_le_infDist_add_dist
    have hd1 : dist y (y - q.2 + (qs n).2) = dist q.2 (qs n).2 := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have hd2 : hausdorffDist ((qs n).1 : Set ℂ) (q.1 : Set ℂ) = dist (qs n).1 q.1 :=
      (TopologicalSpace.NonemptyCompacts.dist_eq).symm
    linarith
  have hle : infDist y (q.1 : Set ℂ) ≤ 0 := ge_of_tendsto hsum (Eventually.of_forall hbound)
  exact (q.1.isCompact.isClosed.mem_iff_infDist_zero q.1.nonempty).2 (le_antisymm hle infDist_nonneg)

variable {A : Set ℂ}

/-- The erosion index `J_A(K) = {x ∈ A : closedBall x δ ⊆ K}`, as a subset of `A`. -/
def erosionIndex (A : Set ℂ) (δ : ℝ) (K : NonemptyCompacts ℂ) : Set A :=
  {x | closedBall (x : ℂ) δ ⊆ (K : Set ℂ)}

/-- The erosion minimum `m(K, f) = inf_{x ∈ J_A(K)} f x`. The real infimum over an empty
index set is `0`, which is the source's convention; for nonempty `J_A(K)` the infimum is attained, so it is the
minimum. -/
def erodedMin (A : Set ℂ) (δ : ℝ) (K : NonemptyCompacts ℂ) (f : C(↥A, ℝ)) : ℝ :=
  ⨅ x : erosionIndex A δ K, f x.1

/-- Strict sublevel sets of the erosion minimum, in terms of the index set. -/
theorem erodedMin_lt_iff (hA : IsCompact A) (δ : ℝ) (K : NonemptyCompacts ℂ) (f : C(↥A, ℝ)) (b : ℝ) :
    erodedMin A δ K f < b ↔
      ((erosionIndex A δ K).Nonempty ∧ ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (K : Set ℂ) ∧ f x < b) ∨
        (¬ (erosionIndex A δ K).Nonempty ∧ 0 < b) := by
  have : CompactSpace ↥A := isCompact_iff_compactSpace.1 hA
  by_cases hne : (erosionIndex A δ K).Nonempty
  · have : Nonempty (erosionIndex A δ K) := hne.to_subtype
    have hbdd : BddBelow (Set.range fun x : erosionIndex A δ K => f x.1) :=
      (isCompact_range f.continuous).bddBelow.mono
        (Set.range_comp_subset_range (fun x : erosionIndex A δ K => x.1) f)
    rw [erodedMin, ciInf_lt_iff hbdd]
    constructor
    · rintro ⟨x, hx⟩
      exact Or.inl ⟨hne, x.1, x.2, hx⟩
    · rintro (⟨-, x, hx, hfx⟩ | ⟨hn, -⟩)
      · exact ⟨⟨x, hx⟩, hfx⟩
      · exact absurd hne hn
  · have hempty : IsEmpty (erosionIndex A δ K) := ⟨fun x => hne ⟨x.1, x.2⟩⟩
    rw [erodedMin, Real.iInf_of_isEmpty]
    constructor
    · intro h
      exact Or.inr ⟨hne, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hne
      · exact h

/-- The set of `(K, f)` for which the erosion index is nonempty is closed (projection along the compact `A`). -/
theorem isClosed_erosion_nonempty (hA : IsCompact A) (δ : ℝ) :
    IsClosed {p : NonemptyCompacts ℂ × C(↥A, ℝ) | (erosionIndex A δ p.1).Nonempty} := by
  have : CompactSpace ↥A := isCompact_iff_compactSpace.1 hA
  have hZ : IsClosed {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A |
      closedBall (z.2 : ℂ) δ ⊆ (z.1.1 : Set ℂ)} :=
    (isClosed_closedBall_subset δ).preimage
      ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have heq : {p : NonemptyCompacts ℂ × C(↥A, ℝ) | (erosionIndex A δ p.1).Nonempty} =
      Prod.fst '' {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A |
        closedBall (z.2 : ℂ) δ ⊆ (z.1.1 : Set ℂ)} := by
    ext p
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(p, x), hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hZ

/-- The set of `(K, f)` with some `x ∈ J_A(K)` and `f x ≤ b` is closed. -/
theorem isClosed_erosion_le (hA : IsCompact A) (δ b : ℝ) :
    IsClosed {p : NonemptyCompacts ℂ × C(↥A, ℝ) |
      ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x ≤ b} := by
  have : CompactSpace ↥A := isCompact_iff_compactSpace.1 hA
  have hA1 : IsClosed {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A | closedBall (z.2 : ℂ) δ ⊆ (z.1.1 : Set ℂ)} :=
    (isClosed_closedBall_subset δ).preimage
      ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hcont : Continuous fun z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A => z.1.2 z.2 :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hA2 : IsClosed {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A | z.1.2 z.2 ≤ b} :=
    isClosed_le hcont continuous_const
  have hZ : IsClosed {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A |
      closedBall (z.2 : ℂ) δ ⊆ (z.1.1 : Set ℂ) ∧ z.1.2 z.2 ≤ b} := hA1.inter hA2
  have heq : {p : NonemptyCompacts ℂ × C(↥A, ℝ) |
      ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x ≤ b} =
      Prod.fst '' {z : (NonemptyCompacts ℂ × C(↥A, ℝ)) × ↥A |
        closedBall (z.2 : ℂ) δ ⊆ (z.1.1 : Set ℂ) ∧ z.1.2 z.2 ≤ b} := by
    ext p
    constructor
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨(p, x), ⟨hx1, hx2⟩, rfl⟩
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      exact ⟨z.2, hz1, hz2⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hZ

/-- Strict sublevel sets are countable unions of closed sets (`F_σ`). -/
theorem erosion_lt_eq_iUnion (δ b : ℝ) :
    {p : NonemptyCompacts ℂ × C(↥A, ℝ) | ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x < b} =
      ⋃ q : ℚ, ({p : NonemptyCompacts ℂ × C(↥A, ℝ) |
        ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x ≤ q} ∩ {_p | (q : ℝ) < b}) := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx2
    exact ⟨q, ⟨x, hx1, hq1.le⟩, hq2⟩
  · rintro ⟨q, ⟨x, hx1, hx2⟩, hqb⟩
    exact ⟨x, hx1, lt_of_le_of_lt hx2 hqb⟩

/-- **Borel measurability of the erosion minimum** on `NonemptyCompacts ℂ × C(A, ℝ)` (a Borel
function of `(K, f)`). The codomain is `ℝ` with its Borel σ-algebra and the domain carries the Borel σ-algebra of the
product topology. -/
theorem measurable_erodedMin (hA : IsCompact A) (δ : ℝ) :
    @Measurable (NonemptyCompacts ℂ × C(↥A, ℝ)) ℝ (borel _) _ (fun p => erodedMin A δ p.1 p.2) := by
  let _inst : MeasurableSpace (NonemptyCompacts ℂ × C(↥A, ℝ)) := borel _
  have : BorelSpace (NonemptyCompacts ℂ × C(↥A, ℝ)) := ⟨rfl⟩
  refine measurable_of_Iio fun b => ?_
  have hN : MeasurableSet {p : NonemptyCompacts ℂ × C(↥A, ℝ) | (erosionIndex A δ p.1).Nonempty} :=
    (isClosed_erosion_nonempty hA δ).measurableSet
  have hE : MeasurableSet {p : NonemptyCompacts ℂ × C(↥A, ℝ) |
      ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x < b} := by
    rw [erosion_lt_eq_iUnion]
    exact MeasurableSet.iUnion fun q =>
      ((isClosed_erosion_le hA δ q).measurableSet).inter (MeasurableSet.const _)
  have hC : MeasurableSet {_p : NonemptyCompacts ℂ × C(↥A, ℝ) | 0 < b} := MeasurableSet.const _
  have hset : (fun p : NonemptyCompacts ℂ × C(↥A, ℝ) => erodedMin A δ p.1 p.2) ⁻¹' Iio b =
      ({p : NonemptyCompacts ℂ × C(↥A, ℝ) | (erosionIndex A δ p.1).Nonempty} ∩
          {p : NonemptyCompacts ℂ × C(↥A, ℝ) | ∃ x : ↥A, closedBall (x : ℂ) δ ⊆ (p.1 : Set ℂ) ∧ p.2 x < b}) ∪
        ({p : NonemptyCompacts ℂ × C(↥A, ℝ) | (erosionIndex A δ p.1).Nonempty}ᶜ ∩
          {_p : NonemptyCompacts ℂ × C(↥A, ℝ) | 0 < b}) := by
    ext p
    simp only [mem_preimage, mem_Iio, erodedMin_lt_iff hA, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
  rw [hset]
  exact (hN.inter hE).union (hN.compl.inter hC)

/-- **Measurability of the random erosion minimum.** If `ω ↦ (K ω, f ω)` is measurable into the Borel σ-algebra
of `NonemptyCompacts ℂ × C(A, ℝ)`, then `ω ↦ m (K ω) (f ω)` is measurable. This is the only input the
random-compact infimum needs beyond the deterministic identities below. -/
theorem measurable_erodedMin_comp {Ω : Type*} [MeasurableSpace Ω] (hA : IsCompact A) (δ : ℝ)
    (K : Ω → NonemptyCompacts ℂ) (f : Ω → C(↥A, ℝ))
    (hKf : @Measurable Ω (NonemptyCompacts ℂ × C(↥A, ℝ)) _ (borel _) (fun ω => (K ω, f ω))) :
    Measurable fun ω => erodedMin A δ (K ω) (f ω) := by
  let _inst : MeasurableSpace (NonemptyCompacts ℂ × C(↥A, ℝ)) := borel _
  have hc := (measurable_erodedMin hA δ).comp hKf
  exact hc

/-- **Regular-open identity**. For `Λ` regular open (`interior (closure Λ) = Λ`) with
nonempty complement and `δ > 0`: `closedBall x δ ⊆ closure Λ ↔ δ ≤ infDist x Λᶜ`. The nonempty complement is needed,
since `infDist x ∅ = 0`. -/
theorem closedBall_subset_closure_iff {Λ : Set ℂ} (hreg : interior (closure Λ) = Λ) (hne : Λᶜ.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    closedBall x δ ⊆ closure Λ ↔ δ ≤ infDist x Λᶜ := by
  constructor
  · intro h
    have hball : ball x δ ⊆ Λ := by
      have hb := interior_maximal (ball_subset_closedBall.trans h) isOpen_ball
      rwa [hreg] at hb
    rw [le_infDist hne]
    intro y hy
    by_contra hlt
    have hyΛ : y ∈ Λ := hball (by rw [mem_ball, dist_comm]; exact not_le.1 hlt)
    exact (mem_compl_iff Λ y).1 hy hyΛ
  · intro h
    have hball : ball x δ ⊆ Λ := by
      intro y hy
      by_contra hn
      have h1 : infDist x Λᶜ ≤ dist x y := infDist_le_dist_of_mem (mem_compl hn)
      rw [mem_ball, dist_comm] at hy
      linarith
    calc closedBall x δ = closure (ball x δ) := (closure_ball x hδ.ne').symm
      _ ⊆ closure Λ := closure_mono hball

/-- The margin domain `A = {x : s ≤ |x| ≤ R}`, as used with `R = ρ/2`. -/
def marginDomain (s R : ℝ) : Set ℂ := closedBall 0 R ∩ {x : ℂ | s ≤ ‖x‖}

theorem isCompact_marginDomain (s R : ℝ) : IsCompact (marginDomain s R) :=
  (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)

/-- If `U = interior (closure C)` then `U` is regular open (`Λ_t` is regular open as the interior
of the closure of the cluster set, by the obstacle characterization). -/
theorem interior_closure_eq_self_of_eq {U C : Set ℂ} (h : U = interior (closure C)) :
    interior (closure U) = U := by
  refine Subset.antisymm ?_ (interior_maximal subset_closure ?_)
  · calc interior (closure U) ⊆ interior (closure C) := by
          apply interior_mono
          apply closure_minimal _ isClosed_closure
          rw [h]
          exact interior_subset
      _ = U := h.symm
  · rw [h]
    exact isOpen_interior

/-- **Deterministic identity of the erosion minimum with the continuum margin**. If `K` is the
closure of a regular open set `Λ` with nonempty complement, `Λ ⊆ closedBall 0 R`, and `f` equals `g` on the margin
domain, then `m(K, f)` is the raw continuum margin `inf_{x ∈ Λ, s ≤ |x|, δ ≤ dist(x, Λᶜ)} g x` (with the real
convention `inf ∅ = 0`). -/
theorem erodedMin_eq_raw {s R δ : ℝ} {Λ : Set ℂ} (g : ℂ → ℝ) (K : NonemptyCompacts ℂ)
    (f : C(↥(marginDomain s R), ℝ)) (hδ : 0 < δ) (hreg : interior (closure Λ) = Λ) (hne : Λᶜ.Nonempty)
    (hsub : Λ ⊆ closedBall 0 R) (hK : (K : Set ℂ) = closure Λ) (hf : ∀ x : ↥(marginDomain s R), f x = g x.1) :
    erodedMin (marginDomain s R) δ K f = ⨅ y : {x : ℂ | x ∈ Λ ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x Λᶜ}, g y.1 := by
  have key : ∀ x ∈ marginDomain s R,
      closedBall x δ ⊆ (K : Set ℂ) ↔ (x ∈ Λ ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x Λᶜ) := by
    intro x hx
    have hxs : s ≤ ‖x‖ := (Set.mem_inter_iff _ _ _).1 hx |>.2
    rw [hK]
    constructor
    · intro h
      have hd : δ ≤ infDist x Λᶜ := (closedBall_subset_closure_iff hreg hne hδ x).1 h
      have hxΛ : x ∈ Λ := by
        by_contra hn
        have h0 : infDist x Λᶜ = 0 := infDist_zero_of_mem (mem_compl hn)
        linarith
      exact ⟨hxΛ, hxs, hd⟩
    · rintro ⟨-, -, hd⟩
      exact (closedBall_subset_closure_iff hreg hne hδ x).2 hd
  have hrange : Set.range (fun x : erosionIndex (marginDomain s R) δ K => f x.1) =
      Set.range (fun y : {x : ℂ | x ∈ Λ ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x Λᶜ} => g y.1) := by
    ext r
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      have hkey := (key x.1 x.2).1 hx
      exact ⟨⟨x.1, hkey⟩, (hf x).symm⟩
    · rintro ⟨⟨y, hy⟩, rfl⟩
      have hyA : y ∈ marginDomain s R := Set.mem_inter (hsub hy.1) hy.2.1
      exact ⟨⟨⟨y, hyA⟩, (key y hyA).2 hy⟩, hf ⟨y, hyA⟩⟩
  unfold erodedMin iInf
  rw [hrange]

end MatedCRT.StoppedInteriorMargin
