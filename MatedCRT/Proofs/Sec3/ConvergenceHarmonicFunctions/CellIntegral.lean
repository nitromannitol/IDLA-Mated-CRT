import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PointwiseCell
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PoleLocation
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Lemma 3.6: the comparison after integrating over the walk

For a fixed environment with small cells, the expected boundary values at the discrete
exit vertex and at the retracted interpolated exit differ by at most
`C (2η + d)^χ + 2K E[U_k(exitWindowBad)(X̂)]`, the expectation of a bounded Lipschitz
functional of the interpolated walk, to which Theorem 2.11 applies.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The discrete exit position is measurable. -/
theorem measurable_vExitPosition (A : Set ℤ) : Measurable (vExitPosition A) := by
  have hk : Measurable fun x : ℕ → ℤ => (vExitTime A x).toNat :=
    (measurable_of_countable ENat.toNat).comp (measurable_vExitTime A)
  refine measurable_to_countable' fun y => ?_
  have hset : vExitPosition A ⁻¹' {y} =
      ⋃ n : ℕ, (fun x : ℕ → ℤ => (vExitTime A x).toNat) ⁻¹' {n} ∩
        (fun x : ℕ → ℤ => x n) ⁻¹' {y} := by
    ext x
    simp only [vExitPosition, mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨_, rfl, hx⟩
    · rintro ⟨n, hn, hx⟩
      rw [hn]
      exact hx
  rw [hset]
  exact MeasurableSet.iUnion fun n =>
    (hk (measurableSet_singleton n)).inter ((measurable_pi_apply n) (measurableSet_singleton y))

/-- The simple random walk moves along edges almost surely. -/
theorem srwLaw_ae_step (m : ℤ → ℤ → ℕ) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
  refine ae_all_iff.2 fun n => ?_
  have h := WalkSteps.srwLaw_nonadjacent_null m n a
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx
  by_contra hc
  exact hx hc

/-- **The integrated comparison** for a fixed environment. -/
theorem abs_discreteExit_sub_interpolatedExit_le {ε mε d s η' : ℝ} {h : ℝ≥0} (hε : 0 < ε)
    (hm : 0 < mε) (hmh : (1 / mε : ℝ).toNNReal ≤ h) {μ : Measure ℂ} {η : ℝ → ℂ}
    (hηa : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {m : ℤ → ℤ → ℕ} (hadj : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hds : d ≤ s) (hη' : 0 ≤ η')
    (hyd : dist y z + d < r) {ψ : ℂ → ℝ} {C χ : ℝ≥0}
    (hhol : HolderOnWith C χ ψ (closedBall z (r + s))) {K : ℝ}
    (hK : ∀ a ∈ closedBall z (r + s), |ψ a| ≤ K)
    (hdiam : ∀ k ∈ cellVertices ε η (ball z r), ∀ a ∈ cell ε η k, ∀ b ∈ cell ε η k,
      dist a b ≤ d) (k : ℕ) :
    |(∫ x, ψ (vertexPoint ε η (vExitPosition (interiorCellVertices ε η (ball z r)) x))
        ∂(srwLaw m (vertexOf ε η y))) -
      ∫ x, ψ (ballRetraction z r (pathExitPosition (ball z r) (interpolatedWalk ε η mε x)))
        ∂(srwLaw m (vertexOf ε η y))| ≤
      C * (2 * η' + d) ^ (χ : ℝ) + 2 * K * ∫ x, pathUpperEnvelope (exitWindowBad z r d h η') k
        (interpolatedWalk ε η mε x) ∂(srwLaw m (vertexOf ε η y)) := by
  set B : ℝ := C * (2 * η' + d) ^ (χ : ℝ) with hB
  have hs0 : 0 ≤ s := hd.trans hds
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK z (mem_closedBall_self (by linarith)))
  have hyball : y ∈ ball z r := mem_ball.2 (by linarith)
  have hycell := Tightness.mem_cell_vertexOf hηa.1 hp hηa.2.2.1 hε y
  have hx0 : vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) :=
    vertexOf_mem_interiorCellVertices_ball hηa hp hε hyd (hdiam _ ⟨y, hycell, hyball⟩)
  set fD : (ℕ → ℤ) → ℝ := fun x =>
    ψ (vertexPoint ε η (vExitPosition (interiorCellVertices ε η (ball z r)) x)) with hfD
  set fI : (ℕ → ℤ) → ℝ := fun x =>
    ψ (ballRetraction z r (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))) with hfI
  set fU : (ℕ → ℤ) → ℝ := fun x =>
    pathUpperEnvelope (exitWindowBad z r d h η') k (interpolatedWalk ε η mε x) with hfU
  have hpw : ∀ᵐ x ∂srwLaw m (vertexOf ε η y), |fD x - fI x| ≤ B + 2 * K * fU x := by
    filter_upwards [srwLaw_ae_start m (vertexOf ε η y), srwLaw_ae_step m (vertexOf ε η y)]
      with x hx0' hstep
    have h1 := abs_exitValue_sub_le (x := x) hε.le hm hmh hηa.1 hr hd hds hη' hhol hK
      (hx0' ▸ hx0) (fun n => (hstep n).imp id fun hne => hadj _ _ hne) hdiam
    have h2 := le_pathUpperEnvelope (abs_exitWindowBad_le_one z r d h η') (Nat.cast_nonneg k)
      (interpolatedWalk ε η mε x)
    have h3 : 0 ≤ 2 * K := by positivity
    calc |fD x - fI x| ≤ B + 2 * K * exitWindowBad z r d h η' (interpolatedWalk ε η mε x) := h1
      _ ≤ B + 2 * K * fU x := by gcongr
  have hfIb : ∀ x, |fI x| ≤ K := fun x =>
    hK _ (closedBall_subset_closedBall (by linarith) (ballRetraction_mem z hr _))
  have hfImeas : Measurable fI :=
    measurable_exitPosition_interpolatedWalk ε mε η (U := ball z r)
      (φ := fun e => ψ (ballRetraction z r e))
  have hfDmeas : Measurable fD :=
    (measurable_of_countable fun j : ℤ => ψ (vertexPoint ε η j)).comp
      (measurable_vExitPosition _)
  have hBL := isBoundedLipschitzPathFunctional_pathUpperEnvelope
    (abs_exitWindowBad_le_one z r d h η') (Nat.cast_nonneg (α := ℝ) k)
  have hfUmeas : Measurable fU := (continuous_pathFunctional_interpolatedWalk hBL ε mε η).measurable
  have hfUb : ∀ x, |fU x| ≤ 1 := fun x => hBL.1 _
  have hfUint : Integrable fU (srwLaw m (vertexOf ε η y)) :=
    Integrable.of_bound hfUmeas.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfUb x)
  have hfIint : Integrable fI (srwLaw m (vertexOf ε η y)) :=
    Integrable.of_bound hfImeas.aestronglyMeasurable K
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfIb x)
  have hfDint : Integrable fD (srwLaw m (vertexOf ε η y)) := by
    refine Integrable.of_bound hfDmeas.aestronglyMeasurable (K + B + 2 * K) ?_
    filter_upwards [hpw] with x hx
    rw [Real.norm_eq_abs]
    have h1 := hfIb x
    have h2 := hfUb x
    have h3 := abs_sub_abs_le_abs_sub (fD x) (fI x)
    have h4 : 2 * K * fU x ≤ 2 * K := by
      have := (abs_le.mp h2).2
      nlinarith
    linarith
  change |(∫ x, fD x ∂_) - ∫ x, fI x ∂_| ≤ B + 2 * K * ∫ x, fU x ∂_
  rw [← integral_sub hfDint hfIint]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |fD x - fI x| ∂srwLaw m (vertexOf ε η y)
      ≤ ∫ x, (B + 2 * K * fU x) ∂srwLaw m (vertexOf ε η y) :=
        integral_mono_ae (hfDint.sub hfIint).abs
          ((integrable_const B).add (hfUint.const_mul _)) hpw
    _ = B + 2 * K * ∫ x, fU x ∂srwLaw m (vertexOf ε η y) := by
        rw [integral_add (integrable_const B) (hfUint.const_mul _), integral_const,
          integral_const_mul, probReal_univ, one_smul]

end MatedCRT
