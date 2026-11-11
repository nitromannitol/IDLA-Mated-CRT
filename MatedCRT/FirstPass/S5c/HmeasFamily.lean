import MatedCRT.FirstPass.S5c.EventualInclusion
import MatedCRT.FirstPass.S5c.B1bThreshold
import MatedCRT.FirstPass.S5c.ClusterOpen
import MatedCRT.FirstPass.S1c.TestDense
import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.FirstPass.Frozen.S2g

/-!
# FIRST PASS, Lemma 5.3: the hmeas input of the entry-time argument

`hmeas : ∀ x t, 0 < t → NullMeasurableSet {ω | ratDisc x ⊆ Λ ω t}` of `exists_entry_free_time` (EntryTimes.lean:104),
for a family `Λ` satisfying `IsConeHarmonicBallFamily` almost surely, is derived here with no openness of the cluster
at a fixed radius and no restriction to `{t < T}`:

* point events at radius `R > 0`: `{ω | d ∈ cluster (μ ω) R 0 u}` are null measurable by the leastSupersolution
  threshold (`nullMeasurableSet_lt_leastSupersolution_rat`, AE form), the pole and the points outside `B_R` trivially;
* eventual openness and identity: for `R` larger than a bound of `Λ_t`, `cluster (μ ω) R 0 t` is open and
  `Λ_t = interior (closure cluster)` (`isOpen_cluster_of_family`, Theorem 2.3(c) as `SatisfiesObstacleCharacterization`).

External inputs are the explicit hypotheses of the frozen Lusin theorem, the disc Green function (nonnegativity and
pole behaviour) and the a.s. local finiteness and AE test-integral measurability of `μ`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls

/-- Point events of the cluster at radius `R > 0`: `{ω | d ∈ cluster (μ ω) R 0 u}` is null measurable. -/
theorem nullMeasurableSet_mem_cluster_threshold {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    {μ : Ω → Measure ℂ} {u R : ℝ} (hu : 0 < u) (hR : 0 < R)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (d : ℂ) : NullMeasurableSet {ω | d ∈ cluster (μ ω) R 0 u} P := by
  by_cases hd : d ∈ ball (0 : ℂ) R
  · by_cases hd0 : d = 0
    · have hset : {ω | d ∈ cluster (μ ω) R 0 u} = univ :=
        Set.eq_univ_of_forall fun ω => Set.mem_sep hd (Or.inl hd0)
      rw [hset]
      exact MeasurableSet.univ.nullMeasurableSet
    · have hset : {ω | d ∈ cluster (μ ω) R 0 u} =
          {ω | -u * greenFunction (ball (0 : ℂ) R) 0 d < leastSupersolution (μ ω) R 0 u d} := by
        ext ω
        exact ⟨fun h => (mem_sep_iff.1 (h : d ∈ cluster (μ ω) R 0 u)).2.resolve_left hd0,
          fun h => Set.mem_sep hd (Or.inr h)⟩
      rw [hset]
      refine nullMeasurableSet_lt_leastSupersolution_rat hF1 hR.le hu hμ
        (fun φ hφ hsupp => hmeas φ hφ ((isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
          (isClosed_tsupport φ) hsupp)) φs hφs hdense (fun x hx hx0 => (hF3 R hR).1 x hx hx0)
        (ball_subset_closedBall hd) _ ?_
      refine Filter.Eventually.of_forall fun ω => ⟨-u * greenFunction (ball (0 : ℂ) R) 0 d, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 d (ball_subset_closedBall hd) hd0
  · have hset : {ω | d ∈ cluster (μ ω) R 0 u} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω h => hd (mem_sep_iff.1 (h : d ∈ cluster (μ ω) R 0 u)).1
    rw [hset]
    exact MeasurableSet.empty.nullMeasurableSet

/-- The `hmeas` input of the entry-time argument: for a compact `C` and `t > 0`, `{ω | C ⊆ Λ_t(ω)}` is null
measurable, for a family of cone harmonic balls `Λ` (almost surely). -/
theorem nullMeasurableSet_subset_family {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hG : FrozenGreenDiscPole) {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hloc : ∀ R : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (R : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    {t : ℝ} (ht : 0 < t) {C : Set ℂ} (hC : IsCompact C) :
    NullMeasurableSet {ω | C ⊆ Λ ω t} P := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  choose φs hφs hdense using fun R : ℕ => exists_dense_nonnegTest_family (R : ℝ)
  refine nullMeasurableSet_inclCompact_eventually hDc hD
    (S := fun (n : ℕ) (ω : Ω) => cluster (μ ω) (n : ℝ) 0 t) (Λ := fun ω => Λ ω t) ?_ ?_ hC
  · intro n d _
    show NullMeasurableSet {ω : Ω | d ∈ cluster (μ ω) ((n : ℕ) : ℝ) 0 t} P
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hset : {ω | d ∈ cluster (μ ω) ((0 : ℕ) : ℝ) 0 t} = ∅ := by
        ext ω
        simp [cluster]
      rw [hset]
      exact MeasurableSet.empty.nullMeasurableSet
    · exact nullMeasurableSet_mem_cluster_threshold hF1 hF3 ht (R := (n : ℝ)) (by exact_mod_cast hn) (hloc n)
        hmeas (φs n) (hφs n) (hdense n) d
  · filter_upwards [hΛ] with ω hω
    obtain ⟨r, hr⟩ := (hω.2.1.isBounded t ht).subset_closedBall (0 : ℂ)
    have hr'pos : (0 : ℝ) < |r| + 1 := by positivity
    have hΛ' : Λ ω t ⊆ ball (0 : ℂ) (|r| + 1) := by
      intro x hx
      have h1 : ‖x‖ ≤ r := mem_closedBall_zero_iff.1 (hr hx)
      rw [mem_ball_zero_iff]
      have := le_abs_self r
      linarith
    refine ⟨⌈|r| + 1⌉₊ + 1, fun n hn => ?_⟩
    have hrn : |r| + 1 < (n : ℝ) := by
      have h1 : (|r| + 1) ≤ (⌈|r| + 1⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈|r| + 1⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    exact ⟨isOpen_cluster_of_family hG hω ht hr'pos hΛ' hrn,
      (hω.2.2 t (|r| + 1) ht hr'pos hΛ' (n : ℝ) hrn).1⟩

end MatedCRT.S5c
