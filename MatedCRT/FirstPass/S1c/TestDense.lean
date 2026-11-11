import HarmonicBalls.Defs.Laplacian
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import MatedCRT.FirstPass.S1c.TestLocal

/-!
# A countable dense family of nonnegative test functions (Lemma 1 analytic layer)

For the radius `R`, the nonnegative test functions of `HarmonicBalls.LaplacianLE` on the ball `B_R` are approximated,
in the sup norm of the function and of its Laplacian on the closed ball, by a countable family of such test functions.
The proof is classical: the restrictions of `(φ, Δφ)` to `B̄_R` form a subset of the separable metric space
`C(B̄_R) × C(B̄_R)`, and a subset of a separable metric space has a countable dense sequence in itself.
No paper-specific input.
-/

namespace MatedCRT

open Set Metric TopologicalSpace HarmonicBalls

/-- Nonnegative test functions on the ball `B_R` (`IsTestFunction` with `0 ≤ φ`): the class over which the
supersolution inequality `LaplacianLE` is tested. -/
def nonnegTest (R : ℝ) : Set (ℂ → ℝ) :=
  {φ | IsTestFunction (ball (0 : ℂ) R) φ ∧ 0 ≤ φ}

/-- A test function is `C²`. -/
theorem contDiff_two_of_isTestFunction {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTestFunction U φ) :
    ContDiff ℝ 2 φ :=
  h.1.of_le (by norm_cast)

/-- Restriction of a continuous function on `ℂ` to the closed ball, as a continuous map on the compact ball. -/
def restrictCM (R : ℝ) (f : ℂ → ℝ) (hf : Continuous f) : C(closedBall (0 : ℂ) R, ℝ) :=
  ⟨fun x => f x, hf.comp continuous_subtype_val⟩

/-- The embedding of a nonnegative test function into `C(B̄_R) × C(B̄_R)`: its restriction to the closed ball together
with the restriction of its Laplacian. -/
noncomputable def testEmbed (R : ℝ) (φ : nonnegTest R) :
    C(closedBall (0 : ℂ) R, ℝ) × C(closedBall (0 : ℂ) R, ℝ) :=
  (restrictCM R φ.1 (contDiff_two_of_isTestFunction φ.2.1).continuous,
    restrictCM R (Laplacian.laplacian φ.1)
      (continuous_laplacian_of_contDiff (contDiff_two_of_isTestFunction φ.2.1)))

/-- Zero is a nonnegative test function on every ball. -/
theorem zero_mem_nonnegTest (R : ℝ) : (0 : ℂ → ℝ) ∈ nonnegTest R :=
  ⟨⟨contDiff_const, HasCompactSupport.zero, by simp⟩, le_rfl⟩

/-- A countable family of nonnegative test functions on `B_R`, dense for the sup norm of `φ` and of `Δφ` on the
closed ball `B̄_R`: every nonnegative test function on `B_R` is approximated within `ε` on `B̄_R` by some member. -/
theorem exists_dense_nonnegTest_family (R : ℝ) :
    ∃ φs : ℕ → ℂ → ℝ, (∀ k, φs k ∈ nonnegTest R) ∧
      ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε := by
  classical
  have : Nonempty ↥(range (testEmbed R)) := ⟨⟨testEmbed R ⟨0, zero_mem_nonnegTest R⟩, ⟨_, rfl⟩⟩⟩
  obtain ⟨u, hu⟩ := exists_dense_seq ↥(range (testEmbed R))
  have hex : ∀ k, ∃ φ : nonnegTest R, testEmbed R φ = (u k : C(closedBall (0 : ℂ) R, ℝ) × C(closedBall (0 : ℂ) R, ℝ)) :=
    fun k => (u k).2
  choose ψ hψ using hex
  refine ⟨fun k => (ψ k : ℂ → ℝ), fun k => (ψ k).2, ?_⟩
  intro φ hφ ε hε
  have hmem : testEmbed R ⟨φ, hφ⟩ ∈ range (testEmbed R) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hu ⟨_, hmem⟩ ε hε
  have hd : dist (testEmbed R ⟨φ, hφ⟩) (testEmbed R (ψ k)) < ε := by
    rw [hψ k]
    exact hk
  rw [Prod.dist_eq] at hd
  have hd1 : dist (testEmbed R ⟨φ, hφ⟩).1 (testEmbed R (ψ k)).1 < ε :=
    lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist (testEmbed R ⟨φ, hφ⟩).2 (testEmbed R (ψ k)).2 < ε :=
    lt_of_le_of_lt (le_max_right _ _) hd
  refine ⟨k, fun x hx => ⟨?_, ?_⟩⟩
  · have h := ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : closedBall (0 : ℂ) R)
      (f := (testEmbed R ⟨φ, hφ⟩).1) (g := (testEmbed R (ψ k)).1)
    rw [Real.dist_eq] at h
    exact lt_of_le_of_lt h hd1
  · have h := ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : closedBall (0 : ℂ) R)
      (f := (testEmbed R ⟨φ, hφ⟩).2) (g := (testEmbed R (ψ k)).2)
    rw [Real.dist_eq] at h
    exact lt_of_le_of_lt h hd2

end MatedCRT
