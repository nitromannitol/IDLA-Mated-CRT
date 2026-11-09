import MatedCRT.FirstPass.S1c.Measurability
import MatedCRT.FirstPass.S5c.InclusionCode

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §2): the cluster's inclusion events are null measurable

For the obstacle cluster `cluster μ R 0 u = {x ∈ B_R | x = 0 ∨ -u G_{B_R}(0,x) < v_{B_R;0}(u)(x)}`
(Harmonic-Balls-LQG Defs/Obstacle.lean:69; the leastSupersolution threshold of MatedCRT/FirstPass/S1c/Measurability.lean),
its point events `{ω | d ∈ cluster (μ ω) R 0 u}` are null measurable (`nullMeasurableSet_threshold`, the pole and points
outside `B_R` being trivial). With the cluster open almost surely, the interior-closure inclusion events of
`InclusionCode.lean` are null measurable. In particular the point events of `Λ = interior (closure cluster)`, the G1
form `{ω | d ∈ Λ_ω}` of the blocker of q1's `ConeFamilyAEMeasurableStep`, follow. The a.s. openness of the cluster is an
explicit hypothesis here (it is `isOpen_cluster_of_volumeGrowth` in Harmonic-Balls-LQG under `VolumeGrowth`, to be bridged
to `VolumeGrowthStmt`); no new frozen input is introduced.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls

/-- Point events of the cluster are null measurable: `{ω | d ∈ cluster (μ ω) R 0 u}`. -/
theorem nullMeasurableSet_mem_cluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 < u)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → Measurable fun ω => ∫ x, φ x ∂(μ ω))
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    (d : ℂ) : NullMeasurableSet {ω | d ∈ cluster (μ ω) R 0 u} P := by
  by_cases hd0 : d = 0
  · subst hd0
    have hset : {ω | (0 : ℂ) ∈ cluster (μ ω) R 0 u} = univ := by
      ext ω
      simp [cluster, hR]
    rw [hset]
    exact MeasurableSet.univ.nullMeasurableSet
  · by_cases hdb : d ∈ ball (0 : ℂ) R
    · have hp : d ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hdb
      have hset : {ω | d ∈ cluster (μ ω) R 0 u} =
          {ω | -u * greenFunction (ball (0 : ℂ) R) 0 d < leastSupersolution (μ ω) R 0 u d} := by
        ext ω
        simp only [cluster, Set.mem_ofPred_eq, hd0, false_or, hdb, true_and]
      rw [hset]
      exact nullMeasurableSet_threshold hF1 hR.le hu hμ hmeas φs hφs hdense hG hp hd0
    · have hset : {ω | d ∈ cluster (μ ω) R 0 u} = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h
        exact hdb h.1
      rw [hset]
      exact MeasurableSet.empty.nullMeasurableSet

/-- Null measurability of the inclusion `C ⊆ interior (closure (cluster (μ ω) R 0 u))` for compact `C`, given
a.s. openness of the cluster. -/
theorem nullMeasurableSet_clusterInclusion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 < u)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → Measurable fun ω => ∫ x, φ x ∂(μ ω))
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    (hopen : ∀ᵐ ω ∂P, IsOpen (cluster (μ ω) R 0 u))
    {C : Set ℂ} (hC : IsCompact C) :
    NullMeasurableSet {ω | C ⊆ interior (closure (cluster (μ ω) R 0 u))} P := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  exact nullMeasurableSet_inclCompact hDc hD hopen
    (fun d _ => nullMeasurableSet_mem_cluster hF1 hR hu hμ hmeas φs hφs hdense hG d) hC

/-- The G1 event: `{ω | d ∈ Λ_ω}` for `Λ_ω = interior (closure (cluster (μ ω) R 0 u))` and a point `d`. -/
theorem nullMeasurableSet_mem_interiorClosureCluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 < u)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → Measurable fun ω => ∫ x, φ x ∂(μ ω))
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    (hopen : ∀ᵐ ω ∂P, IsOpen (cluster (μ ω) R 0 u)) (d : ℂ) :
    NullMeasurableSet {ω | d ∈ interior (closure (cluster (μ ω) R 0 u))} P := by
  have h := nullMeasurableSet_clusterInclusion hF1 hR hu hμ hmeas φs hφs hdense hG hopen
    (isCompact_singleton (x := d))
  have hset : {ω | d ∈ interior (closure (cluster (μ ω) R 0 u))} =
      {ω | ({d} : Set ℂ) ⊆ interior (closure (cluster (μ ω) R 0 u))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.singleton_subset_iff]
  rw [hset]
  exact h

end MatedCRT.S5c
