import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClusterExitMeasurable
import HarmonicBalls.Proofs.Potential.GreenBall

/-! # Measurability of regularized random sets -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- A countable point sample determines membership in its closure. -/
theorem nullMeasurableSet_mem_closure_inter_countable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    {C : Set ℂ} (hC : C.Countable)
    (hmem : ∀ z ∈ C, NullMeasurableSet {ω | z ∈ A ω} P) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ closure (A ω ∩ C)} P := by
  classical
  have : Countable C := hC.to_subtype
  let B := TopologicalSpace.countableBasis ℂ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  have hsample : ∀ (b : B) (y : C),
      NullMeasurableSet {ω | (y : ℂ) ∈ (b : Set ℂ) ∧ (y : ℂ) ∈ A ω} P := by
    intro b y
    by_cases hy : (y : ℂ) ∈ (b : Set ℂ)
    · simpa [hy] using hmem y y.property
    · simp [hy]
  have hb : ∀ b : B, NullMeasurableSet
      {ω | x ∈ (b : Set ℂ) → ∃ y : C, (y : ℂ) ∈ (b : Set ℂ) ∧ (y : ℂ) ∈ A ω} P := by
    intro b
    by_cases hx : x ∈ (b : Set ℂ)
    · have h := NullMeasurableSet.iUnion (fun y : C => hsample b y)
      convert h using 1
      ext ω
      simp [hx]
    · simp [hx]
  have h := NullMeasurableSet.iInter hb
  convert h using 1
  ext ω
  simp only [mem_iInter, mem_ofPred_eq]
  rw [(TopologicalSpace.isBasis_countableBasis ℂ).mem_closure_iff]
  constructor
  · intro ha b hxb
    obtain ⟨y, hyb, hyA, hyC⟩ := ha b b.property hxb
    exact ⟨⟨y, hyC⟩, hyb, hyA⟩
  · intro ha b hb hxb
    obtain ⟨y, hyb, hyA⟩ := ha ⟨b, hb⟩ hxb
    exact ⟨y, hyb, hyA, y.property⟩

/-- If a fixed countable dense set samples each random set densely, the
regularized set `interior (closure A)` has null-measurable point membership. -/
theorem nullMeasurableSet_mem_interior_closure_of_countable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    {C : Set ℂ} (hC : C.Countable) (hdense : Dense C)
    (hmem : ∀ z ∈ C, NullMeasurableSet {ω | z ∈ A ω} P)
    (hsample : ∀ᵐ ω ∂P, A ω ⊆ closure (A ω ∩ C)) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ interior (closure (A ω))} P := by
  classical
  have : Countable C := hC.to_subtype
  let B := TopologicalSpace.countableBasis ℂ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  have hclosure : ∀ y : ℂ, NullMeasurableSet {ω | y ∈ closure (A ω)} P := by
    intro y
    have h := nullMeasurableSet_mem_closure_inter_countable P A hC hmem y
    apply h.congr
    filter_upwards [hsample] with ω hω
    have heq : closure (A ω) = closure (A ω ∩ C) :=
      (closure_minimal hω isClosed_closure).antisymm (closure_mono inter_subset_left)
    simp [heq]
  have hpoint : ∀ (b : B) (y : C),
      NullMeasurableSet {ω | (y : ℂ) ∈ (b : Set ℂ) → (y : ℂ) ∈ closure (A ω)} P := by
    intro b y
    by_cases hy : (y : ℂ) ∈ (b : Set ℂ)
    · simpa [hy] using hclosure y
    · simp [hy]
  have hb : ∀ b : B, NullMeasurableSet
      {ω | x ∈ (b : Set ℂ) ∧ ∀ y : C, (y : ℂ) ∈ (b : Set ℂ) →
        (y : ℂ) ∈ closure (A ω)} P := by
    intro b
    by_cases hx : x ∈ (b : Set ℂ)
    · have h := NullMeasurableSet.iInter (fun y : C => hpoint b y)
      convert h using 1
      ext ω
      simp [hx]
    · simp [hx]
  have h := NullMeasurableSet.iUnion hb
  convert h using 1
  ext ω
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · intro hx
    obtain ⟨b, hb, hxb, hbsub⟩ :=
      (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open hx isOpen_interior
    exact ⟨⟨b, hb⟩, hxb, fun y hy => interior_subset (hbsub hy)⟩
  · rintro ⟨b, hxb, hy⟩
    have hbopen : IsOpen (b : Set ℂ) :=
      (TopologicalSpace.isBasis_countableBasis ℂ).isOpen b.property
    have hbsub : (b : Set ℂ) ⊆ closure (A ω) := by
      apply (hdense.open_subset_closure_inter hbopen).trans
      apply closure_minimal _ isClosed_closure
      rintro y ⟨hyb, hyC⟩
      exact hy ⟨y, hyC⟩ hyb
    exact interior_maximal hbsub hbopen hxb

/-- A random set represented by regularized sets at all sufficiently large
indices has null-measurable point membership when those sets have a common
countable sample which is eventually dense in each set. -/
theorem nullMeasurableSet_mem_of_eventual_regularization
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℕ → Set ℂ) (Λ : Ω → Set ℂ) {C : Set ℂ}
    (hC : C.Countable) (hdense : Dense C)
    (hmem : ∀ (n : ℕ) (z : ℂ), z ∈ C → NullMeasurableSet {ω | z ∈ A ω n} P)
    (hsample : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, A ω n ⊆ closure (A ω n ∩ C))
    (hrepr : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, Λ ω = interior (closure (A ω n)))
    (x : ℂ) : NullMeasurableSet {ω | x ∈ Λ ω} P := by
  have hregular : ∀ n : ℕ, NullMeasurableSet
      {ω | x ∈ interior (closure (A ω n ∩ C))} P := by
    intro n
    apply nullMeasurableSet_mem_interior_closure_of_countable P (fun ω => A ω n ∩ C) hC hdense
    · intro z hz
      simpa [hz] using hmem n z hz
    · exact Filter.Eventually.of_forall (fun ω => by simpa [inter_assoc] using
        (subset_closure : A ω n ∩ C ⊆ closure (A ω n ∩ C)))
  have htail : NullMeasurableSet
      {ω | ∃ N : ℕ, ∀ n ≥ N, x ∈ interior (closure (A ω n ∩ C))} P := by
    have hN : ∀ N : ℕ, NullMeasurableSet
        {ω | ∀ n ≥ N, x ∈ interior (closure (A ω n ∩ C))} P := by
      intro N
      have hn : ∀ n : ℕ, NullMeasurableSet
          {ω | N ≤ n → x ∈ interior (closure (A ω n ∩ C))} P := by
        intro n
        by_cases h : N ≤ n
        · simpa [h] using hregular n
        · simp [h]
      convert NullMeasurableSet.iInter hn using 1
      ext ω
      simp
    convert NullMeasurableSet.iUnion hN using 1
    ext ω
    simp
  apply htail.congr
  filter_upwards [hsample, hrepr] with ω ⟨N, hN⟩ ⟨M, hM⟩
  apply propext
  change (∃ K : ℕ, ∀ n ≥ K, x ∈ interior (closure (A ω n ∩ C))) ↔ x ∈ Λ ω
  have heq : ∀ n ≥ max N M, Λ ω = interior (closure (A ω n ∩ C)) := by
    intro n hn
    have hs : closure (A ω n) = closure (A ω n ∩ C) :=
      (closure_minimal (hN n (le_trans (le_max_left _ _) hn)) isClosed_closure).antisymm
        (closure_mono inter_subset_left)
    rw [hM n (le_trans (le_max_right _ _) hn), hs]
  constructor
  · rintro ⟨K, hK⟩
    have hk := hK (max K (max N M)) (le_max_left _ _)
    rw [← heq _ (le_max_right _ _)] at hk
    exact hk
  · intro hx
    exact ⟨max N M, fun n hn => (heq n hn) ▸ hx⟩

/-- A continuum obstacle cluster is densely sampled by a dense set containing
the pole whenever its least supersolution is continuous on the ball. -/
theorem cluster_subset_closure_inter_of_continuous
    (μ : Measure ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) {C : Set ℂ}
    (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hv : ContinuousOn (leastSupersolution μ r 0 t) (ball 0 r)) :
    cluster μ r 0 t ⊆ closure (cluster μ r 0 t ∩ C) := by
  let U : Set ℂ := ball 0 r ∩ ({0} : Set ℂ)ᶜ
  have hU : IsOpen U := isOpen_ball.inter isClosed_singleton.isOpen_compl
  let g : ℂ → ℝ := fun x => leastSupersolution μ r 0 t x +
    t * greenFunction (ball 0 r) 0 x
  have hg : ContinuousOn g U := by
    apply (hv.mono inter_subset_left).add
    exact continuousOn_const.mul ((continuousOn_greenFunction_ball (mem_ball_self hr)).mono inter_subset_right)
  let O : Set ℂ := U ∩ g ⁻¹' Ioi 0
  have hO : IsOpen O := hg.isOpen_inter_preimage hU isOpen_Ioi
  have hOsub : O ⊆ cluster μ r 0 t := by
    intro x hx
    refine ⟨hx.1.1, Or.inr ?_⟩
    have hgap : 0 < g x := hx.2
    dsimp [g] at hgap
    linarith
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact subset_closure ⟨hx, hzero⟩
  · have hxO : x ∈ O := by
      refine ⟨⟨hx.1, by simpa using hx0⟩, ?_⟩
      have hgap := hx.2.resolve_left hx0
      change 0 < g x
      dsimp [g]
      linarith
    exact (closure_mono (inter_subset_inter_left C hOsub))
      (hdense.open_subset_closure_inter hO hxO)

/-- Point membership in a cone harmonic ball is null measurable if its
obstacle clusters admit measurable countable samples. The radius is exhausted
deterministically, and continuity makes the samples eventually dense. -/
theorem nullMeasurableSet_mem_coneFamily_of_cluster_samples
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ) (t : ℝ) (ht : 0 < t)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {C : Set ℂ} (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hmem : ∀ (n : ℕ) (z : ℂ), z ∈ C → NullMeasurableSet
      {ω | z ∈ cluster (μ ω) ((n : ℝ) + 1) 0 t} P)
    (x : ℂ) : NullMeasurableSet {ω | x ∈ Λ ω t} P := by
  have hbound : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Λ ω t = interior (closure (cluster (μ ω) ((n : ℝ) + 1) 0 t)) ∧
      ContinuousOn (leastSupersolution (μ ω) ((n : ℝ) + 1) 0 t)
        (closedBall 0 ((n : ℝ) + 1)) := by
    filter_upwards [hfam] with ω hω
    obtain ⟨R, hR⟩ := (hω.2.1.isBounded t ht).subset_ball (0 : ℂ)
    let r : ℝ := max R 0 + 1
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right R 0]
    have hsub : Λ ω t ⊆ ball 0 r :=
      hR.trans (ball_subset_ball (by dsimp [r]; linarith [le_max_left R 0]))
    obtain ⟨N, hN⟩ := exists_nat_gt r
    refine ⟨N, fun n hn => ?_⟩
    have hrn : r < (n : ℝ) + 1 := by
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h := hω.2.2 t r ht hr hsub ((n : ℝ) + 1) hrn
    exact ⟨h.1, h.2.1⟩
  have hsample : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cluster (μ ω) ((n : ℝ) + 1) 0 t ⊆
        closure (cluster (μ ω) ((n : ℝ) + 1) 0 t ∩ C) := by
    filter_upwards [hbound] with ω ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    apply cluster_subset_closure_inter_of_continuous _ (by positivity) t hdense hzero
    exact ((hN n hn).2).mono ball_subset_closedBall
  apply nullMeasurableSet_mem_of_eventual_regularization P
    (fun ω n => cluster (μ ω) ((n : ℝ) + 1) 0 t) (fun ω => Λ ω t)
    hC hdense hmem hsample
  filter_upwards [hbound] with ω ⟨N, hN⟩
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- Almost-everywhere measurability of continuum least supersolutions at
integer radii implies null measurability of harmonic-ball membership. -/
theorem nullMeasurableSet_mem_coneFamily_of_leastSupersolutions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ) (t : ℝ) (ht : 0 < t)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hv : ∀ (n : ℕ) (z : ℂ), AEMeasurable
      (fun ω => leastSupersolution (μ ω) ((n : ℝ) + 1) 0 t z) P)
    (x : ℂ) : NullMeasurableSet {ω | x ∈ Λ ω t} P := by
  classical
  obtain ⟨C₀, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let C : Set ℂ := C₀ ∪ {0}
  have hC : C.Countable := hcount.union (countable_singleton 0)
  have hCdense : Dense C := hdense.mono subset_union_left
  have hzero : (0 : ℂ) ∈ C := Or.inr rfl
  apply nullMeasurableSet_mem_coneFamily_of_cluster_samples P μ Λ t ht hfam hC hCdense hzero
  intro n z _
  by_cases hz : z ∈ ball (0 : ℂ) ((n : ℝ) + 1)
  · by_cases hz0 : z = 0
    · simp [cluster, hz0]
    · have h := nullMeasurableSet_lt
        (aemeasurable_const : AEMeasurable (fun _ : Ω => -t * greenFunction
          (ball 0 ((n : ℝ) + 1)) 0 z) P) (hv n z)
      convert h using 1
      ext ω
      have hznorm : ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball_zero_iff] using hz
      simp [cluster, hznorm, hz0]
  · have hznorm : ¬ ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball_zero_iff] using hz
    simp [cluster, hznorm]

end MatedCRT
