import MatedCRT.FirstPass.S1c.Analytic

/-!
# Supersolutions with prescribed moments (Lemma 1 analytic layer)

For a locally finite `ν` with `ν(B̄_R) < ∞` and the moment vector `m k = ∫ φs k dν`, a supersolution
`w ∈ HarmonicBalls.supersolutions ν R 0 u` with `w(z₀) < q` exists if and only if `m` lies in the projection of the
supersolution pairs (`supersolutionPairs`). This is the identification used to write the sublevel sets of the least
supersolution as analytic sets (Lemma 1). Classical; no paper-specific input.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

variable {R : ℝ}

/-- A nonnegative test function on `B_R` is integrable against a measure finite on `B̄_R`. -/
theorem integrable_nonnegTest {ν : Measure ℂ} (hν : ν (closedBall (0 : ℂ) R) < ⊤) {φ : ℂ → ℝ}
    (hφ : φ ∈ nonnegTest R) : Integrable φ ν :=
  integrable_of_continuous_of_support hν (contDiff_two_of_isTestFunction hφ.1).continuous
    fun _ hx => eq_zero_of_not_mem_tsupport_fn hφ.1.2.2 (fun h => hx (ball_subset_closedBall h))

/-- The moment description of the supersolution sublevel sets: `m ∈ Prod.fst '' supersolutionPairs` iff some
supersolution of `ν` has `w(z₀) < q`, when `m` is the vector of moments `∫ φs k dν`. -/
theorem mem_image_iff_exists_supersolution (hR : 0 ≤ R) (ν : Measure ℂ) (hν : ν (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (u q : ℝ) (z0 : closedBall (0 : ℂ) R) (m : ℕ → ℝ) (hm : ∀ k, m k = ∫ x, φs k x ∂ν) :
    (∃ w ∈ supersolutions ν R 0 u, w z0 < q) ↔
      m ∈ Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) z0 q := by
  constructor
  · rintro ⟨w, ⟨hwc, ⟨-, hwL⟩, hwob⟩, hwq⟩
    refine ⟨(m, ⟨(closedBall (0 : ℂ) R).domRestrict w, hwc.domRestrict⟩), ⟨?_, ?_, ?_⟩, rfl⟩
    · intro k
      have key : momentCM hR φs k ⟨(closedBall (0 : ℂ) R).domRestrict w, hwc.domRestrict⟩ =
          ∫ x, w x * Laplacian.laplacian (φs k) x :=
        (integral_mul_laplacian_eq_extend hR w hwc (hφs k).1).symm
      refine le_trans (le_of_eq key) ?_
      show ∫ x, w x * Laplacian.laplacian (φs k) x ≤ m k
      rw [hm k]
      exact hwL (φs k) (hφs k).1 (hφs k).2 (integrable_nonnegTest hν (hφs k))
    · intro z hz
      exact hwob z.1 z.2 hz
    · exact hwq
  · rintro ⟨p, ⟨h1, h2, h3⟩, hpm⟩
    refine ⟨extendCM R hR p.2, ⟨(continuous_extendCM hR p.2).continuousOn, ?_, ?_⟩, ?_⟩
    · refine laplacianLE_extend_of_countable hR ν hν φs hφs hdense p.2 (fun k => ?_)
      have hk := h1 k
      unfold momentCM at hk
      rw [hpm, hm k] at hk
      exact hk
    · intro z hz hne
      rw [extendCM_apply hR p.2 hz]
      exact h2 ⟨z, hz⟩ hne
    · rw [extendCM_apply hR p.2 z0.2]
      exact h3

end MatedCRT
