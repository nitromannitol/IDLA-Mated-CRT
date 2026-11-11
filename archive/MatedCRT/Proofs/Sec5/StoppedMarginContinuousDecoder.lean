import MatedCRT.Proofs.Sec5.StoppedInteriorMarginProof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Bases
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Countable Borel decoder of a continuous function from its dense values

The annular continuum-surplus decoder, in the repaired form. Let `A` be a metric space and `a : ℕ → A` a dense sequence. A real
sequence `v` is the sequence of values `(f (a n))ₙ` of a continuous `f : C(A, ℝ)` exactly when it
passes countably many uniform-continuity tests (`DenseUniformTests`). The decoder `denseDecoder a`
returns the unique continuous extension of such `v` and returns `0` for every other `v`.

Proved here, for a compact metric `A` unless noted:
* `exists_continuous_of_denseUniformTests` (any metric `A`): a sequence passing the countable tests
  is the dense-value sequence of a continuous function (`ℝ` is complete);
* `denseExtLocus_eq`: the extension locus is the set of sequences passing the countable tests;
* `measurableSet_denseExtLocus`: the locus is Borel for the product σ-algebra on `ℕ → ℝ`;
* `denseDecoder_recovers`: the decoder recovers every continuous function from its dense values;
* `measurable_denseDecoder`: the decoder is Borel from `ℕ → ℝ` to `C(A, ℝ)` (sup-norm topology);
* `denseDecoder_ae_eq`, `measurable_denseDecoder_comp`: consequences for a random array;
* `marginDomain_denseDecoder`, `marginDomain_continuous_subsingleton`: the margin domain
  `marginDomain s R` with a dense sequence, and the empty case.

Not in this file: the Borel versions of the countably many random values (
"universally measurable on the good field set") and the identity almost surely on `{t < T}`.
They enter only as hypotheses of `denseDecoder_ae_eq`.
-/

open Metric Set Filter Topology MeasureTheory

namespace MatedCRT.StoppedMarginDecoder

variable {A : Type*} [MetricSpace A]

/-- The countable uniform-continuity tests on a real sequence `v` indexed by the points `a n` of
`A`: for every `k` there is `j` such that `|v n - v m| ≤ 1/(k+1)` whenever
`dist (a n) (a m) < 1/(j+1)`. -/
def DenseUniformTests (a : ℕ → A) : Set (ℕ → ℝ) :=
  {v | ∀ k : ℕ, ∃ j : ℕ, ∀ n m : ℕ,
    dist (a n) (a m) < 1 / ((j : ℝ) + 1) → |v n - v m| ≤ 1 / ((k : ℝ) + 1)}

/-- The extension locus: the sequences `(f (a n))ₙ` of values of a continuous `f : A → ℝ`. -/
def DenseExtLocus (a : ℕ → A) : Set (ℕ → ℝ) :=
  {v | ∃ f : C(A, ℝ), ∀ n, f (a n) = v n}

theorem mem_denseUniformTests {a : ℕ → A} {v : ℕ → ℝ} :
    v ∈ DenseUniformTests a ↔ ∀ k : ℕ, ∃ j : ℕ, ∀ n m : ℕ,
      dist (a n) (a m) < 1 / ((j : ℝ) + 1) → |v n - v m| ≤ 1 / ((k : ℝ) + 1) :=
  Iff.rfl

theorem mem_denseExtLocus {a : ℕ → A} {v : ℕ → ℝ} :
    v ∈ DenseExtLocus a ↔ ∃ f : C(A, ℝ), ∀ n, f (a n) = v n :=
  Iff.rfl

/-! ### The countable tests -/

theorem eq_zero_of_forall_le_one_div {x : ℝ} (h : ∀ k : ℕ, |x| ≤ 1 / ((k : ℝ) + 1)) :
    x = 0 := by
  by_contra hx
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.mpr hx)
  linarith [h k]

/-- Tests force equal values at equal points (the decoder is well defined on the subset). -/
theorem denseUniformTests_eq_of {a : ℕ → A} {v : ℕ → ℝ} (hv : v ∈ DenseUniformTests a)
    {n m : ℕ} (h : a n = a m) : v n = v m := by
  have key : ∀ k : ℕ, |v n - v m| ≤ 1 / ((k : ℝ) + 1) := fun k => by
    obtain ⟨j, hj⟩ := mem_denseUniformTests.mp hv k
    exact hj n m (by rw [h, dist_self]; exact one_div_pos.mpr (by positivity))
  exact sub_eq_zero.mp (eq_zero_of_forall_le_one_div key)

/-- The countable tests give the ε-δ uniform continuity on the dense sequence. -/
theorem uniformly_of_denseUniformTests {a : ℕ → A} {v : ℕ → ℝ} (hv : v ∈ DenseUniformTests a) :
    ∀ ε > 0, ∃ δ > 0, ∀ n m : ℕ, dist (a n) (a m) < δ → |v n - v m| ≤ ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj⟩ := mem_denseUniformTests.mp hv k
  exact ⟨1 / ((j : ℝ) + 1), one_div_pos.mpr (by positivity),
    fun n m h => (hj n m h).trans hk.le⟩

/-- Values of a continuous function on a compact metric space pass the countable tests. -/
theorem denseUniformTests_of_continuous [CompactSpace A] (a : ℕ → A) (f : C(A, ℝ)) :
    (fun n => f (a n)) ∈ DenseUniformTests a := by
  refine mem_denseUniformTests.mpr fun k => ?_
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (1 / ((k : ℝ) + 1))
    (one_div_pos.mpr (by positivity))
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j, fun n m h => ?_⟩
  have h' := hfδ (h.trans hj)
  rw [Real.dist_eq] at h'
  exact h'.le

/-! ### Extension from the dense sequence -/

/-- A sequence passing the countable tests is the dense-value sequence of a continuous function on
`A`: the values are uniformly continuous on the dense set, hence extend, since `ℝ` is complete. -/
theorem exists_continuous_of_denseUniformTests {a : ℕ → A} (ha : DenseRange a)
    {v : ℕ → ℝ} (hv : v ∈ DenseUniformTests a) : ∃ f : C(A, ℝ), ∀ n, f (a n) = v n := by
  have hs : Dense (range a) := ha
  -- the values on the dense subset, read off at any index representing the point
  let g : range a → ℝ := fun p => v (Classical.choose p.2)
  have hg_spec : ∀ p : range a, a (Classical.choose p.2) = (p : A) :=
    fun p => Classical.choose_spec p.2
  have hg_eq : ∀ n : ℕ, g ⟨a n, n, rfl⟩ = v n := fun n =>
    denseUniformTests_eq_of hv (hg_spec ⟨a n, n, rfl⟩)
  -- uniform continuity of `g` on the dense subset
  have hg_unif : ∀ ε > 0, ∃ δ > 0, ∀ p q : range a, dist (p : A) q < δ → |g p - g q| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδv⟩ := uniformly_of_denseUniformTests hv ε hε
    refine ⟨δ, hδ, fun p q hpq => ?_⟩
    exact hδv (Classical.choose p.2) (Classical.choose q.2)
      (by rw [hg_spec p, hg_spec q]; exact hpq)
  have hg_cont : Continuous g := by
    refine (Metric.uniformContinuous_iff.mpr fun ε hε => ?_).continuous
    obtain ⟨δ, hδ, hδv⟩ := hg_unif (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    intro p q hpq
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hδv p q hpq) (half_lt_self hε)
  -- every point of `A` is a limit of the values along the dense subset
  have hg_lim : ∀ x : A, ∃ b : ℝ, Tendsto g (comap (Subtype.val : range a → A) (𝓝 x)) (𝓝 b) := by
    intro x
    have : NeBot (comap (Subtype.val : range a → A) (𝓝 x)) :=
      hs.isDenseInducing_val.comap_nhds_neBot x
    have hcau : Cauchy (Filter.map g (comap (Subtype.val : range a → A) (𝓝 x))) := by
      refine Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδv⟩ := hg_unif (ε / 2) (half_pos hε)
      refine ⟨g '' ((Subtype.val : range a → A) ⁻¹' ball x (δ / 2)), ?_, ?_⟩
      · exact Filter.mem_map.mpr (Filter.mem_of_superset
          (preimage_mem_comap (ball_mem_nhds x (half_pos hδ)))
          (subset_preimage_image g _))
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
        have h1 : dist (p : A) x < δ / 2 := hp
        have h2 : dist (q : A) x < δ / 2 := hq
        have hpq : dist (p : A) q < δ := by
          linarith [dist_triangle (p : A) x (q : A), dist_comm (q : A) x]
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hδv p q hpq) (half_lt_self hε)
    obtain ⟨b, hb⟩ := CompleteSpace.complete hcau
    exact ⟨b, hb⟩
  have hF : Continuous (hs.extend g) := hs.continuous_extend hg_lim
  refine ⟨⟨hs.extend g, hF⟩, fun n => ?_⟩
  exact (hs.extend_eq hg_cont ⟨a n, n, rfl⟩).trans (hg_eq n)

/-- Compact case: the extension locus is exactly the set of sequences passing the countable tests. -/
theorem denseExtLocus_eq [CompactSpace A] {a : ℕ → A} (ha : DenseRange a) :
    DenseExtLocus a = DenseUniformTests a := by
  ext v
  constructor
  · intro hv
    obtain ⟨f, hf⟩ := mem_denseExtLocus.mp hv
    have hv' : v = fun n => f (a n) := funext fun n => (hf n).symm
    rw [hv']
    exact denseUniformTests_of_continuous a f
  · intro hv
    exact mem_denseExtLocus.mpr (exists_continuous_of_denseUniformTests ha hv)

/-- The countable tests are a Borel condition on `ℕ → ℝ` (countable intersections and unions of
closed half-space conditions `|v n - v m| ≤ c`). -/
theorem measurableSet_denseUniformTests (a : ℕ → A) : MeasurableSet (DenseUniformTests a) := by
  have hset : DenseUniformTests a = ⋂ k : ℕ, ⋃ j : ℕ, ⋂ n : ℕ, ⋂ m : ℕ,
      {v : ℕ → ℝ | dist (a n) (a m) < 1 / ((j : ℝ) + 1) → |v n - v m| ≤ 1 / ((k : ℝ) + 1)} := by
    ext v
    simp only [mem_denseUniformTests, mem_iInter, mem_iUnion, Set.mem_ofPred_eq]
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => ?_
  by_cases h : dist (a n) (a m) < 1 / ((j : ℝ) + 1)
  · simp only [h, true_implies]
    exact measurableSet_le (continuous_abs.measurable.comp
      ((measurable_pi_apply n).sub (measurable_pi_apply m))) measurable_const
  · simp only [h, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

/-- The extension locus is Borel in `ℕ → ℝ` (product σ-algebra). -/
theorem measurableSet_denseExtLocus [CompactSpace A] {a : ℕ → A} (ha : DenseRange a) :
    MeasurableSet (DenseExtLocus a) := by
  rw [denseExtLocus_eq ha]
  exact measurableSet_denseUniformTests a

/-! ### The decoder -/

open scoped Classical in
/-- **Borel decoder.** The unique continuous extension of the
dense values `v` when `v` extends continuously, and the zero function otherwise. -/
noncomputable def denseDecoder (a : ℕ → A) (v : ℕ → ℝ) : C(A, ℝ) :=
  if h : ∃ f : C(A, ℝ), ∀ n, f (a n) = v n then h.choose else ContinuousMap.const A 0

theorem denseDecoder_spec {a : ℕ → A} {v : ℕ → ℝ} (hv : v ∈ DenseExtLocus a) (n : ℕ) :
    denseDecoder a v (a n) = v n := by
  have h := mem_denseExtLocus.mp hv
  unfold denseDecoder
  split_ifs
  exact h.choose_spec n

/-- Uniqueness: a continuous function with the dense values `v` is the decoded function. -/
theorem denseDecoder_eq_of {a : ℕ → A} (ha : DenseRange a) {v : ℕ → ℝ} {f : C(A, ℝ)}
    (hf : ∀ n, f (a n) = v n) : denseDecoder a v = f := by
  have hs : Dense (range a) := ha
  have hspec : ∀ n, denseDecoder a v (a n) = v n :=
    denseDecoder_spec (mem_denseExtLocus.mpr ⟨f, hf⟩)
  have hEq : EqOn (⇑(denseDecoder a v)) (⇑f) (range a) := by
    rintro _ ⟨n, rfl⟩
    rw [hspec n, hf n]
  exact ContinuousMap.ext fun x =>
    congrFun (Continuous.ext_on hs (denseDecoder a v).continuous f.continuous hEq) x

/-- **Recovery.** The decoder recovers every continuous function from its dense evaluations. -/
theorem denseDecoder_recovers {a : ℕ → A} (ha : DenseRange a) (f : C(A, ℝ)) :
    denseDecoder a (fun n => f (a n)) = f :=
  denseDecoder_eq_of ha fun _ => rfl

theorem denseDecoder_of_not_mem {a : ℕ → A} {v : ℕ → ℝ} (hv : v ∉ DenseExtLocus a) :
    denseDecoder a v = ContinuousMap.const A 0 := by
  unfold denseDecoder
  split_ifs with h'
  · exact absurd (mem_denseExtLocus.mpr h') hv
  · rfl

/-! ### Measurability -/

/-- The distance from the decoded function to a fixed continuous `q` is a Borel function of the
values: on the locus it is the supremum over the dense sequence of `|v n - q (a n)|`. -/
theorem measurable_dist_denseDecoder [CompactSpace A] {a : ℕ → A} (ha : DenseRange a)
    (q : C(A, ℝ)) : Measurable fun v : ℕ → ℝ => dist (denseDecoder a v) q := by
  classical
  have hM : Measurable fun v : ℕ → ℝ => ⨆ n : ℕ, |v n - q (a n)| :=
    Measurable.iSup fun n => continuous_abs.measurable.comp
      ((measurable_pi_apply n).sub measurable_const)
  have hval : ∀ v ∈ DenseExtLocus a,
      dist (denseDecoder a v) q = ⨆ n : ℕ, |v n - q (a n)| := by
    intro v hv
    have hspec := denseDecoder_spec hv
    have hterm : ∀ n : ℕ, |v n - q (a n)| = dist (denseDecoder a v (a n)) (q (a n)) :=
      fun n => by rw [Real.dist_eq, hspec n]
    have hbdd : BddAbove (range fun n : ℕ => |v n - q (a n)|) := by
      refine ⟨dist (denseDecoder a v) q, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (hterm n).le.trans (ContinuousMap.dist_apply_le_dist (a n))
    have hle : ∀ n : ℕ, |v n - q (a n)| ≤ ⨆ n : ℕ, |v n - q (a n)| :=
      fun n => le_ciSup hbdd n
    apply le_antisymm
    · have h0 : 0 ≤ ⨆ n : ℕ, |v n - q (a n)| := (abs_nonneg _).trans (hle 0)
      refine (ContinuousMap.dist_le h0).mpr fun x => ?_
      have hclosed : IsClosed
          {x : A | dist (denseDecoder a v x) (q x) ≤ ⨆ n : ℕ, |v n - q (a n)|} :=
        isClosed_le ((denseDecoder a v).continuous.dist q.continuous) continuous_const
      have hsub : range a ⊆
          {x : A | dist (denseDecoder a v x) (q x) ≤ ⨆ n : ℕ, |v n - q (a n)|} := by
        rintro _ ⟨n, rfl⟩
        rw [Set.mem_ofPred_eq, ← hterm n]
        exact hle n
      exact closure_minimal hsub hclosed (ha x)
    · exact ciSup_le fun n => by
        rw [hterm n]
        exact ContinuousMap.dist_apply_le_dist (a n)
  have hfun : (fun v : ℕ → ℝ => dist (denseDecoder a v) q) =
      (DenseExtLocus a).piecewise (fun v : ℕ → ℝ => ⨆ n : ℕ, |v n - q (a n)|)
        (fun _ : ℕ → ℝ => dist (ContinuousMap.const A (0 : ℝ)) q) := by
    funext v
    by_cases hv : v ∈ DenseExtLocus a
    · rw [hval v hv]
      simp [hv]
    · rw [denseDecoder_of_not_mem hv]
      simp [hv]
  rw [hfun]
  exact Measurable.piecewise (measurableSet_denseExtLocus ha) hM measurable_const

/-- **Borel measurability of the decoder** from `ℕ → ℝ` (product σ-algebra) to `C(A, ℝ)` (Borel
σ-algebra of the sup-norm topology). The balls with centres in a countable dense set and radii
`1/(k+1)` form a countable basis; their preimages are sublevel sets of `dist (denseDecoder a · ) q`. -/
theorem measurable_denseDecoder [CompactSpace A] {a : ℕ → A} (ha : DenseRange a) :
    @Measurable (ℕ → ℝ) C(A, ℝ) MeasurableSpace.pi (borel C(A, ℝ)) (denseDecoder a) := by
  obtain ⟨Q, -, hQd⟩ := TopologicalSpace.exists_countable_dense C(A, ℝ)
  have hB : TopologicalSpace.IsTopologicalBasis
      {U : Set C(A, ℝ) | ∃ q ∈ Q, ∃ k : ℕ, U = ball q (1 / ((k : ℝ) + 1))} := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro U ⟨q, -, k, rfl⟩
      exact isOpen_ball
    · intro F u hF hu
      obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.mp hu F hF
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨q, hqF, hqQ⟩ := Metric.dense_iff.mp hQd F _
        (one_div_pos.mpr (by positivity : (0 : ℝ) < (k : ℝ) + 1))
      refine ⟨ball q (1 / ((k : ℝ) + 1)), ⟨q, hqQ, k, rfl⟩, ?_, fun y hy => hεu ?_⟩
      · rw [mem_ball, dist_comm]
        exact hqF
      · rw [mem_ball]
        have h1 : dist y q < 1 / ((k : ℝ) + 1) := hy
        have h2 : dist q F < 1 / ((k : ℝ) + 1) := hqF
        linarith [dist_triangle y q F]
  rw [hB.borel_eq_generateFrom]
  refine measurable_generateFrom ?_
  rintro U ⟨q, -, k, rfl⟩
  have hmeas : MeasurableSet {v : ℕ → ℝ | dist (denseDecoder a v) q < 1 / ((k : ℝ) + 1)} :=
    measurableSet_lt (measurable_dist_denseDecoder ha q) measurable_const
  exact hmeas

/-! ### Random arrays -/

/-- Recovery almost surely: if almost surely the random values agree with `w ω` on the dense
sequence, the decoded function is `w ω` almost surely. -/
theorem denseDecoder_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : ℕ → A} (ha : DenseRange a) (V : ℕ → Ω → ℝ) (w : Ω → C(A, ℝ))
    (hV : ∀ᵐ ω ∂μ, ∀ n, V n ω = w ω (a n)) :
    ∀ᵐ ω ∂μ, denseDecoder a (fun n => V n ω) = w ω :=
  hV.mono fun _ h => denseDecoder_eq_of ha fun n => (h n).symm

/-- The decoded random function is measurable when the dense values are measurable. -/
theorem measurable_denseDecoder_comp [CompactSpace A] {Ω : Type*} [MeasurableSpace Ω]
    {a : ℕ → A} (ha : DenseRange a) (V : ℕ → Ω → ℝ) (hV : ∀ n, Measurable (V n)) :
    @Measurable Ω C(A, ℝ) _ (borel C(A, ℝ)) fun ω => denseDecoder a (fun n => V n ω) := by
  have hVm : Measurable fun ω (n : ℕ) => V n ω := Measurable.of_eval fun n => hV n
  exact (measurable_denseDecoder ha).comp hVm

/-! ### Empty domain -/

/-- If `B` is empty, all continuous real functions on `B` coincide, so the decoder is trivial. -/
theorem continuousMap_subsingleton_of_isEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B]
    (f g : C(B, ℝ)) : f = g :=
  ContinuousMap.ext fun x => isEmptyElim x

/-! ### The margin domain -/

open MatedCRT.StoppedInteriorMargin in
/-- **Borel decoder on the margin domain `marginDomain s R`.**
If the domain is nonempty it has a dense sequence `a`; `denseDecoder a` is Borel from `ℕ → ℝ` to
`C(marginDomain s R, ℝ)` and recovers every continuous function from its values on `a`. -/
theorem marginDomain_denseDecoder (s R : ℝ) (hne : (marginDomain s R).Nonempty) :
    ∃ a : ℕ → ↥(marginDomain s R), DenseRange a ∧
      @Measurable (ℕ → ℝ) C(↥(marginDomain s R), ℝ) MeasurableSpace.pi (borel _)
        (denseDecoder a) ∧
      ∀ f : C(↥(marginDomain s R), ℝ), denseDecoder a (fun n => f (a n)) = f := by
  have : CompactSpace ↥(marginDomain s R) :=
    isCompact_iff_compactSpace.mp (isCompact_marginDomain s R)
  have : Nonempty ↥(marginDomain s R) := hne.to_subtype
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq ↥(marginDomain s R)
  exact ⟨a, ha, measurable_denseDecoder ha, fun f => denseDecoder_recovers ha f⟩

open MatedCRT.StoppedInteriorMargin in
/-- Empty margin domain (`s > R`): the continuous functions on it form a singleton. -/
theorem marginDomain_continuous_subsingleton (s R : ℝ)
    (hne : ¬(marginDomain s R).Nonempty) (f g : C(↥(marginDomain s R), ℝ)) : f = g := by
  have : IsEmpty ↥(marginDomain s R) :=
    Set.isEmpty_coe_sort.mpr (Set.not_nonempty_iff_eq_empty.mp hne)
  exact continuousMap_subsingleton_of_isEmpty f g

end MatedCRT.StoppedMarginDecoder
