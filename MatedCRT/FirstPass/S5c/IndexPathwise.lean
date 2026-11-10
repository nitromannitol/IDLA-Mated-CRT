import MatedCRT.FirstPass.S5c.MarginInf
import MatedCRT.FirstPass.S1c.Cluster

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), step M4a): the countable closure index (deterministic)

Let `C` be the obstacle cluster `cluster μ ρ 0 t` and `Λ = interior (closure C)` (the obstacle characterization,
Defs/Setting.lean, `SatisfiesObstacleCharacterization`). The margin index `marginIndex` of MarginInf.lean tests closed rational
balls inside `Λ`. Here `closureIndex C ρ δ` tests only countably many Gaussian rational points `d` (`ratComplex`,
S1c/Cluster.lean:17) against `closure C`, so that it is a countable Boolean combination of point events of `C`
(measurable in `ω` once the point events are; see IndexExact.lean). Both inclusions needed by the margin hold deterministically:
`closureIndex_subset_marginIndex` and `closureIndex_near`. The index avoids the pole: `ratComplexNZ = ratComplex \ {0}`, because
the rational threshold of the least supersolution is measurable off the pole (`bddBelow_supersolution_values_of_ne_zero`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls

/-- The Gaussian rationals different from `0`: countable, and every nonempty open set of `ℂ` meets it
(`ratComplexNZ_meets_open`). -/
def ratComplexNZ : Set ℂ := ratComplex \ {0}

/-- The closure index: `q` with `‖q‖ < ρ` and a rational radius `r > δ/4` such that every Gaussian rational `d` with
`dist d q < r` lies in the closure of `C`. -/
def closureIndex (C : Set ℂ) (ρ δ : ℝ) : Set ℂ :=
  {q | ‖q‖ < ρ ∧ ∃ r : ℚ, δ / 4 < (r : ℝ) ∧ ∀ d ∈ ratComplex, dist d q < (r : ℝ) → d ∈ closure C}

theorem ratComplexNZ_meets_open {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ p ∈ ratComplexNZ, p ∈ U := by
  have hU' : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  have hne' : (U ∩ {0}ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases h0 : x = 0
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
      have hmem : ((ε / 2 : ℝ) : ℂ) ∈ ball x ε := by
        rw [mem_ball, h0, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (half_pos hε).le]
        linarith
      exact ⟨((ε / 2 : ℝ) : ℂ), hball hmem, Complex.ofReal_ne_zero.2 (half_pos hε).ne'⟩
    · exact ⟨x, hx, h0⟩
  obtain ⟨p, hpR, hpU⟩ := ratComplex_meets_open hU' hne'
  exact ⟨p, ⟨hpR, hpU.2⟩, hpU.1⟩

/-- Every ball is contained in the closure of the Gaussian rationals of the ball. -/
theorem ball_subset_closure_ratComplex_inter {q : ℂ} {r : ℝ} :
    ball q r ⊆ closure (ratComplex ∩ ball q r) := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hpR, hpU⟩ := ratComplex_meets_open (U := ball y ε ∩ ball q r)
    (isOpen_ball.inter isOpen_ball) ⟨y, mem_ball_self hε, hy⟩
  exact ⟨p, ⟨hpR, hpU.2⟩, by rw [dist_comm]; exact hpU.1⟩

/-- A ball all of whose Gaussian rational points lie in the closure of `C` is contained in `interior (closure C)`. -/
theorem ball_subset_interior_closure {C : Set ℂ} {q : ℂ} {r : ℝ}
    (h : ∀ d ∈ ratComplex, dist d q < r → d ∈ closure C) : ball q r ⊆ interior (closure C) := by
  have hsub : ratComplex ∩ ball q r ⊆ closure C := fun d hd => h d hd.1 (mem_ball.1 hd.2)
  have hball : ball q r ⊆ closure C :=
    ball_subset_closure_ratComplex_inter.trans (closure_minimal hsub isClosed_closure)
  exact interior_maximal hball isOpen_ball

/-- **Closure index inside the margin index** (M4a, pathwise): `closureIndex C ρ δ ⊆ marginIndex (interior (closure C)) ρ δ`. -/
theorem closureIndex_subset_marginIndex {C : Set ℂ} {ρ δ : ℝ} :
    closureIndex C ρ δ ⊆ marginIndex (interior (closure C)) ρ δ := by
  rintro q ⟨hqρ, r, hr, h⟩
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hr
  exact ⟨hqρ, s, hs1, (closedBall_subset_ball hs2).trans (ball_subset_interior_closure h)⟩

/-- **Approximation by closure-index points** (M4a, pathwise): if `B(x, δ/2) ⊆ closure C` and `x ∈ B̄_ρ`, then for every
`ε > 0` there is `q ∈ ratComplexNZ` in `closureIndex C ρ δ` with `dist q x < ε`. -/
theorem closureIndex_near {C : Set ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) ρ) (hΛ : ball x (δ / 2) ⊆ closure C) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ ratComplexNZ, q ∈ closureIndex C ρ δ ∧ dist q x < ε := by
  have hmin : 0 < min ε (δ / 8) := lt_min hε (by linarith)
  have hxcl : x ∈ closure (ball (0 : ℂ) ρ) := by
    rw [closure_ball (0 : ℂ) hρ.ne']
    exact hx
  obtain ⟨y, hyρ, hyx⟩ := Metric.mem_closure_iff.1 hxcl (min ε (δ / 8) / 2) (half_pos hmin)
  obtain ⟨q, hqNZ, hqy, hqρ⟩ := ratComplexNZ_meets_open ((isOpen_ball (x := y) (ε := min ε (δ / 8) / 2)).inter
    isOpen_ball) ⟨y, mem_ball_self (half_pos hmin), hyρ⟩
  have hqx : dist q x < min ε (δ / 8) := by
    have h1 : dist q y < min ε (δ / 8) / 2 := mem_ball.1 hqy
    have h2 : dist y x < min ε (δ / 8) / 2 := by rw [dist_comm]; exact hyx
    have h3 := dist_triangle q y x
    linarith
  have hqε : dist q x < ε := lt_of_lt_of_le hqx (min_le_left _ _)
  have hqδ : dist q x < δ / 8 := lt_of_lt_of_le hqx (min_le_right _ _)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show δ / 4 < δ / 2 - dist q x by linarith)
  refine ⟨q, hqNZ, ⟨mem_ball_zero_iff.1 hqρ, r, hr1, ?_⟩, hqε⟩
  intro d _ hdq
  apply hΛ
  rw [mem_ball]
  have := dist_triangle d q x
  linarith

/-- **Pathwise margin for an arbitrary index** (M4a): the argument of `marginInf_pathwise` (MarginInf.lean) with the index
`I` in place of `marginIndex Λ ρ δ`, under the two inclusions `I ⊆ marginIndex Λ ρ δ` and the approximation property. -/
theorem marginInf_pathwise_index {D I : Set ℂ} (hDne : D.Nonempty)
    {Λ : Set ℂ} {A : ℂ → ℝ} {ρ δ β : ℝ} (hΛne : Λᶜ.Nonempty)
    (hA : ContinuousOn A (closedBall (0 : ℂ) ρ)) (hβ : ∀ x ∈ marginCore Λ ρ δ, β ≤ A x)
    (hIΛ : I ⊆ marginIndex Λ ρ δ) (hIS : I ⊆ closedBall (0 : ℂ) ρ)
    (happ : ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x Λᶜ →
      ∀ ε : ℝ, 0 < ε → ∃ q ∈ D, q ∈ I ∧ dist q x < ε) :
    min 1 β ≤ marginInf D I A ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x Λᶜ → marginInf D I A ≤ A x := by
  have hβI : ∀ q ∈ D, q ∈ I → β ≤ A q := fun q _ hq => hβ q (marginIndex_subset_core hΛne (hIΛ hq))
  refine ⟨le_marginInf hDne hβI, fun x hx hxd => ?_⟩
  exact marginInf_le_of_approx (term_ge_min hβI) hIS (hA.continuousWithinAt hx)
    (fun ε hε => happ x hx hxd ε hε)

end MatedCRT.S5c
