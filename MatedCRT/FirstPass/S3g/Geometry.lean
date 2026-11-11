import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Proofs.Infra.LocallyFinite

/-! # Geometry for the boundary-stability bridge of corrected Lemma 3.5

Elementary facts about cells, the vertex map `vertexOf`, the retraction `ballRetraction`, and the discrete
boundary of `interiorCellVertices ε η (ball z r)`. They feed `discreteDirichletProblem_of_corrected`. -/

namespace MatedCRT.FirstPass35Bridge

open MeasureTheory Filter Topology Set Metric

/-- Every point of `ℂ` lies in the cell of the vertex it is assigned to (the `sInf` of `vertexOf`). Uses the
continuity, surjectivity and properness of the curve `η` (`IsAreaParametrized` and `ae_tendsto_cocompact`). -/
theorem mem_cell_vertexOf {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hsurj : Function.Surjective η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (x : ℂ) :
    x ∈ cell ε η (vertexOf ε η x) := by
  set S : Set ℤ := {k : ℤ | x ∈ cell ε η k} with hSdef
  have hne : S.Nonempty := by
    obtain ⟨t, rfl⟩ := hsurj x
    refine ⟨⌈t / ε⌉, t, ⟨?_, ?_⟩, rfl⟩
    · have h2 : ((⌈t / ε⌉ : ℤ) : ℝ) < t / ε + 1 := Int.ceil_lt_add_one _
      have h3 : ((⌈t / ε⌉ : ℤ) - 1 : ℝ) < t / ε := by linarith
      have h4 := (lt_div_iff₀ hε).1 h3
      nlinarith
    · have h1 : t / ε ≤ ((⌈t / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
      have h4 := (div_le_iff₀ hε).1 h1
      nlinarith
  have hbdd : BddBelow S := by
    have hpre : IsCompact (η ⁻¹' {x}) :=
      (isProperMap_iff_tendsto_cocompact.mpr ⟨hη, hp⟩).isCompact_preimage isCompact_singleton
    obtain ⟨T, hT⟩ := hpre.isBounded.subset_closedBall 0
    refine ⟨⌊-T / ε⌋, fun k hk => ?_⟩
    obtain ⟨t, ht, hηt⟩ := hk
    have htT : |t| ≤ T := by
      have h := hT (show t ∈ η ⁻¹' {x} from hηt)
      rwa [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
    have h1 : -T ≤ t := (abs_le.mp htT).1
    have h2 : t ≤ ε * (k : ℝ) := ht.2
    have h3 : -T / ε ≤ (k : ℝ) := by
      rw [div_le_iff₀ hε]
      linarith [mul_comm ε (k : ℝ)]
    have h4 : (⌊-T / ε⌋ : ℝ) ≤ -T / ε := Int.floor_le _
    exact_mod_cast h4.trans h3
  exact Int.csInf_mem hne hbdd

/-- A connected set which misses the sphere and meets the open ball lies in the open ball. -/
theorem subset_ball_of_isPreconnected {z : ℂ} {r : ℝ} {s : Set ℂ} (hs : IsPreconnected s)
    (hsph : ∀ y ∈ s, y ∉ sphere z r) (hmeet : (s ∩ ball z r).Nonempty) : s ⊆ ball z r := by
  have hdisj : Disjoint (ball z r) (closedBall z r)ᶜ := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hy' (ball_subset_closedBall hy)
  refine hs.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl hdisj ?_ hmeet
  intro y hy
  by_cases h : y ∈ closedBall z r
  · left
    have hne : dist y z ≠ r := fun h' => hsph y hy (mem_sphere.2 h')
    exact mem_ball.2 (lt_of_le_of_ne (mem_closedBall.1 h) hne)
  · right
    exact h

/-- The discrete boundary of the interior cells of a ball lies in the cells meeting the sphere: an edge
from an interior vertex `a` to `b ∉ A` gives `H_a ∩ H_b ≠ ∅` (adjacency, `hadj`), the cell `H_a` is connected and
misses the sphere, so it lies in the ball, and then `b` meets the ball, hence meets the sphere. -/
theorem vBoundary_interior_subset_sphere {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {z : ℂ} {r : ℝ} (hη : Continuous η)
    (hr : r ≠ 0) (hadj : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    vBoundary m (interiorCellVertices ε η (ball z r)) ⊆ cellVertices ε η (sphere z r) := by
  rintro b ⟨hbA, a, haA, hab⟩
  obtain ⟨x, hxa, hxb⟩ := hadj a b hab
  have hfr : frontier (ball z r) = sphere z r := frontier_ball z hr
  have hA1 : (cell ε η a ∩ ball z r).Nonempty := haA.1
  have hA2 : ∀ y ∈ cell ε η a, y ∉ sphere z r := by
    intro y hy hys
    apply haA.2
    rw [hfr]
    exact ⟨y, hy, hys⟩
  have hconn : IsPreconnected (cell ε η a) :=
    (isPreconnected_Icc (a := ε * ((a : ℝ) - 1)) (b := ε * (a : ℝ))).image η hη.continuousOn
  have hsub : cell ε η a ⊆ ball z r := subset_ball_of_isPreconnected hconn hA2 hA1
  have hbB : b ∈ cellVertices ε η (ball z r) := ⟨x, hxb, hsub hxa⟩
  by_contra hns
  exact hbA ⟨hbB, by rw [hfr]; exact hns⟩

/-- A point of the closed ball lies in a cell whose vertex is interior or whose cell meets the sphere. -/
theorem vertexOf_mem_interior_or_sphere {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r : ℝ} (hr : r ≠ 0) {x : ℂ}
    (hx : x ∈ closedBall z r) (hxc : x ∈ cell ε η (vertexOf ε η x)) :
    vertexOf ε η x ∈ interiorCellVertices ε η (ball z r) ∨
      vertexOf ε η x ∈ cellVertices ε η (sphere z r) := by
  by_cases hs : (cell ε η (vertexOf ε η x) ∩ sphere z r).Nonempty
  · exact Or.inr hs
  · left
    have hxball : x ∈ ball z r := by
      have hne : dist x z ≠ r := fun h => hs ⟨x, hxc, mem_sphere.2 h⟩
      exact mem_ball.2 (lt_of_le_of_ne (mem_closedBall.1 hx) hne)
    refine ⟨⟨x, hxc, hxball⟩, ?_⟩
    rw [frontier_ball z hr]
    exact hs

/-- The vertex point `η(εb)` lies in its own cell. -/
theorem vertexPoint_mem_cell_self {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (b : ℤ) :
    vertexPoint ε η b ∈ cell ε η b :=
  ⟨ε * (b : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- Distance from `x` to its retraction on the closed ball, as an explicit formula. -/
theorem dist_self_ballRetraction {z : ℂ} {r : ℝ} (x : ℂ) :
    dist x (ballRetraction z r x) = |1 - r / max r (dist x z)| * dist x z := by
  have key : x - ballRetraction z r x = ((1 - r / max r (dist x z) : ℝ) : ℂ) * (x - z) := by
    unfold ballRetraction
    push_cast
    ring
  rw [dist_eq_norm, key, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← dist_eq_norm]

/-- The retraction of a point lies in the closed ball (for `r > 0`). -/
theorem ballRetraction_mem_closedBall {z : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    ballRetraction z r x ∈ closedBall z r := by
  rw [mem_closedBall]
  have key : ballRetraction z r x - z = ((r / max r (dist x z) : ℝ) : ℂ) * (x - z) := by
    unfold ballRetraction
    ring
  have hc : 0 ≤ r / max r (dist x z) := div_nonneg hr.le (le_trans hr.le (le_max_left _ _))
  rw [dist_eq_norm, key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, ← dist_eq_norm]
  have hmax : 0 < max r (dist x z) := lt_of_lt_of_le hr (le_max_left _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hmax]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le

/-- The retraction is the nearest point of the closed ball: `dist x (π x) ≤ dist x w` for `w` in the ball. -/
theorem dist_le_dist_ballRetraction {z w : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) (hw : w ∈ closedBall z r) :
    dist x (ballRetraction z r x) ≤ dist x w := by
  have hw' : dist w z ≤ r := mem_closedBall.1 hw
  rw [dist_self_ballRetraction]
  rcases le_total (dist x z) r with h | h
  · rw [max_eq_left h, div_self hr.ne', sub_self, abs_zero, zero_mul]
    exact dist_nonneg
  · have hd : 0 < dist x z := lt_of_lt_of_le hr h
    rw [max_eq_right h, abs_of_nonneg (sub_nonneg.2 ((div_le_one hd).2 h)), sub_mul,
      div_mul_cancel₀ _ hd.ne', one_mul]
    linarith [dist_triangle x w z]

end MatedCRT.FirstPass35Bridge
