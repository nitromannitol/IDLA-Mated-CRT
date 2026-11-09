import Mathlib

/-!
# FIRST PASS, Lemma 5.3: deterministic geometric lemma (G-5-3 note, Section 3)

Pure measure theory and plane topology, used by `MeanValueSurplusLowerStep`
(`MatedCRT/Proofs/Sec5/MeanValueInequality/SurplusSteps.lean:209`) through the exterior-mass bound (8).
A set `L` with `interior (closure L) = L` (regular open) is recovered by compact sets `U j` whose exterior
mass `μ (U j \ L)` tends to zero, provided `μ` charges every nonempty open disk.
No paper input: the statements are general potential-theoretic and measure-theoretic facts.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- A closed set contains the open disk around one of its points whose radius does not exceed the distance from
that point to the frontier. A disk is preconnected, so it cannot meet both the interior and the complement of a
closed set without meeting its frontier. -/
lemma ball_subset_of_isClosed {U : Set ℂ} (hU : IsClosed U) {z : ℂ} (hz : z ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (hfr : ∀ w ∈ frontier U, δ ≤ dist z w) : ball z δ ⊆ U := by
  have hcov : ball z δ ⊆ interior U ∪ Uᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · left
      by_contra hint
      have hyfr : y ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hyU, hint⟩
      have h1 := hfr y hyfr
      have h2 : dist y z < δ := mem_ball.1 hy
      rw [dist_comm] at h1
      linarith
    · right
      exact hyU
  have hdisj : Disjoint (interior U) Uᶜ :=
    Set.disjoint_left.2 fun y hy hyc => hyc (interior_subset hy)
  rcases IsPreconnected.subset_or_subset isOpen_interior hU.isOpen_compl hdisj hcov
      (convex_ball z δ).isPreconnected with h | h
  · exact h.trans interior_subset
  · exact (h (mem_ball_self hδ) hz).elim

/-- Passing to the limit: if `w n ∈ V n` with `V n` closed, `δ < infDist (w n) (frontier (V n))`, the exterior mass
`μ (V n \ L)` tends to zero and `w n → z`, then the disk `ball z δ` lies in the closure of `L`.
(Proof: a point `y` of `ball z δ` outside `closure L` has a disk `ball y r₁` disjoint from `L` and contained in
`ball (w n) δ ⊆ V n` for large `n`, which has positive mass against a vanishing exterior mass.) -/
lemma ball_subset_closure_of_limit {μ : Measure ℂ} {L : Set ℂ} {V : ℕ → Set ℂ} {δ : ℝ} {w : ℕ → ℂ} {z : ℂ}
    (hfull : ∀ x : ℂ, ∀ r : ℝ, 0 < r → 0 < μ (ball x r)) (hδ : 0 < δ)
    (hVc : ∀ n, IsClosed (V n)) (hwV : ∀ n, w n ∈ V n) (hw : ∀ n, δ < infDist (w n) (frontier (V n)))
    (hmass : Tendsto (fun n => μ (V n \ L)) atTop (𝓝 0)) (hlim : Tendsto w atTop (𝓝 z)) :
    ball z δ ⊆ closure L := by
  intro y hy
  by_contra hyL
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl y hyL
  have hyz : dist y z < δ := mem_ball.1 hy
  obtain ⟨r₁, hr₁, hr₁s, hr₁r⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ (δ - dist y z) / 2 ∧ r₁ ≤ r :=
    ⟨min r ((δ - dist y z) / 2), lt_min hr (by linarith), min_le_right _ _, min_le_left _ _⟩
  have hpos : 0 < μ (ball y r₁) := hfull y r₁ hr₁
  have hev1 : ∀ᶠ n in atTop, μ (V n \ L) < μ (ball y r₁) :=
    hmass.eventually (Iio_mem_nhds hpos)
  have hev2 : ∀ᶠ n in atTop, w n ∈ ball z ((δ - dist y z) / 2) :=
    hlim.eventually (ball_mem_nhds z (by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hn2' : dist (w n) z < (δ - dist y z) / 2 := mem_ball.1 hn2
  have hsub : ball y r₁ ⊆ ball (w n) δ := by
    intro u hu
    rw [mem_ball] at hu ⊢
    have h1 := dist_triangle u y (w n)
    have h2 := dist_triangle y z (w n)
    rw [dist_comm z (w n)] at h2
    linarith
  have hsubV : ball y r₁ ⊆ V n :=
    hsub.trans (ball_subset_of_isClosed (hVc n) (hwV n) hδ fun w' hw' =>
      le_trans (le_of_lt (hw n)) (infDist_le_dist_of_mem hw'))
  have hsubLc : ball y r₁ ⊆ Lᶜ := by
    intro u hu
    have hu' : u ∈ (closure L)ᶜ := ball_subset_ball hr₁r hu |> fun h => hball h
    exact fun hL => hu' (subset_closure hL)
  have hle : μ (ball y r₁) ≤ μ (V n \ L) :=
    measure_mono fun u hu => ⟨hsubV hu, hsubLc hu⟩
  exact absurd hn1 (not_lt.2 hle)

/-- **Deterministic lemma of Lemma 5.3** (G-5-3 note, Section 3, eq. (9)). Let `L` be a bounded regular open set with
nonempty complement, `μ` charge every nonempty open disk, and let compact sets `U j` lie in a fixed compact set `Q`
with exterior mass `μ (U j \ L) → 0`. Then for every `δ > 0`, eventually every `z ∈ U j` whose distance to the frontier
of `U j` exceeds `δ` satisfies `3δ/4 ≤ d(z, Lᶜ)`. -/
theorem deep_points_of_exterior_mass_tendsto_zero
    {μ : Measure ℂ} {L Q : Set ℂ} {U : ℕ → Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hL : interior (closure L) = L) (hLc : Lᶜ.Nonempty) (hQ : IsCompact Q)
    (hfull : ∀ x : ℂ, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hU : ∀ j, IsCompact (U j)) (hUQ : ∀ j, U j ⊆ Q)
    (hmass : Tendsto (fun j => μ (U j \ L)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ z ∈ U j,
      δ < infDist z (frontier (U j)) →
      3 * δ / 4 ≤ infDist z Lᶜ := by
  by_contra hcon
  have hfreq : ∃ᶠ j in atTop, ∃ z ∈ U j, δ < infDist z (frontier (U j)) ∧ infDist z Lᶜ < 3 * δ / 4 :=
    (Filter.not_eventually.1 hcon).mono fun j hj => by push Not at hj; exact hj
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z hzU hzδ hzL using hφP
  obtain ⟨z₀, -, ψ, hψ, hlim⟩ := hQ.tendsto_subseq (x := fun n => z n) (fun n => hUQ _ (hzU n))
  have hψtop : Tendsto (fun n => φ (ψ n)) atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hmass' : Tendsto (fun n => μ (U (φ (ψ n)) \ L)) atTop (𝓝 0) := hmass.comp hψtop
  have hsub := ball_subset_closure_of_limit (μ := μ) (L := L) (V := fun n => U (φ (ψ n)))
    (w := fun n => z (ψ n)) (z := z₀) hfull hδ (fun n => (hU _).isClosed) (fun n => hzU (ψ n))
    (fun n => hzδ (ψ n)) hmass' hlim
  have hballL : ball z₀ δ ⊆ L := by
    have h := interior_maximal hsub isOpen_ball
    rwa [hL] at h
  have hdist : δ ≤ infDist z₀ Lᶜ := (le_infDist (x := z₀) hLc).2 fun y hy => by
    by_contra hlt
    push Not at hlt
    exact hy (hballL (mem_ball.2 (by rw [dist_comm]; exact hlt)))
  have hcont : Tendsto (fun n => infDist (z (ψ n)) Lᶜ) atTop (𝓝 (infDist z₀ Lᶜ)) :=
    ((continuous_infDist_pt Lᶜ).tendsto z₀).comp hlim
  have hle : infDist z₀ Lᶜ ≤ 3 * δ / 4 :=
    le_of_tendsto hcont (Eventually.of_forall fun n => (hzL (ψ n)).le)
  linarith

end MatedCRT.S5c
