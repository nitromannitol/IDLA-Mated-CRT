import MatedCRT.FirstPass.S1c.Equiv
import MatedCRT.FirstPass.S1c.Cluster

/-!
# Membership in the obstacle cluster as a countable moment event (Lemma 1)

Deterministic part of the containment event of `FixedTimeRadiusStep`. For `p ≠ 0` in the closed disc, membership of
`p` in the Armitage-Gardiner cluster `Λ_{B_R;0}(u)` (`HarmonicBalls.cluster`) is the strict inequality
`-u G_{B_R}(0,p) < v_{B_R;0}(u)(p)` between the disc Green obstacle and the least supersolution. The infimum defining
`v` is a supremum of thresholds: `c < sInf S` iff some rational `q > c` lies below no `w(p)`, `w` a supersolution.
Combined with `mem_image_iff_exists_supersolution`, the threshold is a countable union of complements of analytic
moment sets. The Green nonnegativity needed for nonemptiness is an explicit hypothesis (`FrozenDiskGreenNonnegCont`).
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

/-- Membership in the cluster away from the pole: `p ∈ Λ_{B_R;0}(u)` iff `p ∈ B_R` and `-uG(0,p) < v(u)(p)`. -/
theorem mem_cluster_iff_of_ne {μ : Measure ℂ} {R u : ℝ} {p : ℂ} (hp : p ≠ 0) :
    p ∈ cluster μ R 0 u ↔
      p ∈ ball (0 : ℂ) R ∧ -u * greenFunction (ball (0 : ℂ) R) 0 p < leastSupersolution μ R 0 u p := by
  simp [cluster, hp]

/-- The zero function is a supersolution (Armitage-Gardiner's least supersolution is bounded above by `0`):
`Δ0 = 0 ≤ μ` on the ball, and `-uG(0,·) ≤ 0` on the closed disc off the pole. -/
theorem zero_mem_supersolutions (μ : Measure ℂ) {R u : ℝ} (hu : 0 < u)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x) :
    (0 : ℂ → ℝ) ∈ supersolutions μ R 0 u := by
  refine ⟨continuousOn_const, ⟨fun x _ => ⟨univ, univ_mem, integrableOn_zero⟩, ?_⟩, ?_⟩
  · intro φ _ hφ0 _
    simp only [Pi.zero_apply, zero_mul, integral_zero]
    exact integral_nonneg hφ0
  · intro x hx hx0
    simp only [Pi.zero_apply]
    by_cases hxb : x ∈ ball (0 : ℂ) R
    · rw [neg_mul]
      linarith [mul_nonneg hu.le (hG x hxb hx0)]
    · have hzero : greenFunction (ball (0 : ℂ) R) 0 x = 0 := by
        simp [greenFunction, hxb]
      rw [hzero, mul_zero]

/-- Threshold characterization of the least supersolution at a point off the pole: `-uG(0,p) < v(u)(p)` iff some
rational `q > -uG(0,p)` is below no value `w(p)` of a supersolution `w`. -/
theorem neg_mul_green_lt_leastSupersolution_iff {μ : Measure ℂ} {R u : ℝ} (hu : 0 < u)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R) (hp0 : p ≠ 0) :
    -u * greenFunction (ball (0 : ℂ) R) 0 p < leastSupersolution μ R 0 u p ↔
      ∃ q : ℚ, -u * greenFunction (ball (0 : ℂ) R) 0 p < (q : ℝ) ∧
        ¬ ∃ w ∈ supersolutions μ R 0 u, w p < (q : ℝ) := by
  set c := -u * greenFunction (ball (0 : ℂ) R) 0 p with hc
  set S : Set ℝ := (fun w : ℂ → ℝ => w p) '' supersolutions μ R 0 u with hS
  have hne : S.Nonempty := ⟨(0 : ℂ → ℝ) p, ⟨0, zero_mem_supersolutions μ hu hG, rfl⟩⟩
  have hbdd : BddBelow S := by
    refine ⟨c, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨-, -, hob⟩ := hw
    exact hob p hp hp0
  have hlss : leastSupersolution μ R 0 u p = sInf S := rfl
  rw [hlss]
  constructor
  · intro h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    refine ⟨q, hq1, ?_⟩
    rintro ⟨w, hw, hwq⟩
    have h1 : sInf S ≤ w p := csInf_le hbdd ⟨w, hw, rfl⟩
    linarith
  · rintro ⟨q, hq1, hno⟩
    have hle : (q : ℝ) ≤ sInf S := by
      refine le_csInf hne ?_
      rintro y ⟨w, hw, rfl⟩
      show (q : ℝ) ≤ w p
      by_contra hlt
      exact hno ⟨w, hw, not_le.1 hlt⟩
    linarith

/-- The threshold event in moment form: for a locally finite `μ` with `μ(B̄_R) < ∞`, `-uG(0,p) < v(u)(p)` iff some
rational `q > -uG(0,p)` has its moment vector `(∫ φs k dμ)_k` outside the analytic set of
`supersolutionPairs` at `(p, q)`. -/
theorem threshold_iff_moments {μ : Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hμ : μ (closedBall (0 : ℂ) R) < ⊤)
    (hu : 0 < u) (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R) (hp0 : p ≠ 0) :
    -u * greenFunction (ball (0 : ℂ) R) 0 p < leastSupersolution μ R 0 u p ↔
      ∃ q : ℚ, -u * greenFunction (ball (0 : ℂ) R) 0 p < (q : ℝ) ∧
        (fun k => ∫ x, φs k x ∂μ) ∉
          Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ) := by
  rw [neg_mul_green_lt_leastSupersolution_iff hu hG hp hp0]
  refine exists_congr fun q => and_congr Iff.rfl (not_congr ?_)
  exact mem_image_iff_exists_supersolution hR μ hμ φs hφs hdense u (q : ℝ) ⟨p, hp⟩
    (fun k => ∫ x, φs k x ∂μ) (fun k => rfl)

end MatedCRT
