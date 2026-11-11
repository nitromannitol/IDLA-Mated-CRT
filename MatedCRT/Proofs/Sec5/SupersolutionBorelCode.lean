import MatedCRT.Proofs.Sec5.ConeOriginNullMeasurableProof
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.BallExtension
import MatedCRT.LPStaging.Analysis.LaplacianCalculus

/-!
# The Borel supersolution relation

Target: the relation inside `ConeOriginNullMeasurableStep` (the cone-origin
obstacle code). For a countable family `φs : ℕ → ℂ → ℝ` of nonnegative smooth tests supported in `ball 0 R` and a
sequence `ps : ℕ → ℂ` dense in the punctured closed disk, the relation

* `∫ w̃ Δφ_j ≤ J_{φ_j}(c)` for all `j`, where `J_φ = massLimit γ φ` is the checked mass code,
* `w(p_k) ≥ -t G_R(0,p_k)` for all `k`, the Green-obstacle inequalities at the dense points,

is a measurable subset `supersolutionRelation γ t hR φs ps` of `PosCircleFns × BallFns R`.

Conventions.
* `w̃ = extendClosedBall 0 R hR w` is the project's radial-retraction extension of a trace `w ∈ C(closedBall 0 R, ℝ)`
  (`BallExtension.lean`, `closedBallRetraction`). Values of `w̃` off the closed disk never enter a test integral: a test
  has `tsupport φ ⊆ ball 0 R`, so `Δφ` vanishes off the disk. The extension is continuous, hence integrable against
  `Δφ`, and it agrees with `w` on the closed disk (`extendClosedBall_of_mem`).
* Diagonal convention: the Green constraint is imposed off the pole only (`y = 0` is unconstrained), as in
  `HarmonicBalls.supersolutions`, where the obstacle is imposed for `x ≠ z`.
* Terminology: Armitage-Gardiner (potential theory of the disk; Green function of a ball, greatest harmonic minorant),
  Duplantier-Sheffield and Berestycki-Powell (LQG measure as a limit of dyadic approximations, `massLimit`).

Proved here.
* `lipschitz_ballTestIntegral`: `w ↦ ∫ w̃ Δφ` is Lipschitz for the sup norm on `C(closedBall 0 R, ℝ)`, with constant
  `∫ |Δφ|`.
* `measurableSet_supersolutionRelation`: the relation is a Borel (in particular measurable) subset.
* `forall_pointGreen_iff_of_dense`: countably many Green-obstacle inequalities at a dense punctured-disk sequence are
  equivalent to all punctured-disk inequalities (both sides continuous on the punctured closed disk).
* `mem_supersolutionRelation_iff`: the section formula for the relation.
* `mem_superTraces_iff`: the traces of supersolutions are the traces `w` with `LaplacianLE w̃ μ (ball 0 R)` and the
  Green constraint, with no residual.
* `mem_supersolutionRelation_iff_of_residuals`: the section of the relation is the set of traces of supersolutions,
  conditional on the two residuals below and on the mass identity `massLimit = ∫ dμ` for the family.

Residuals (exact Props, not proved here):
* `CountableC2DenseStmt R φs`: the countable family is `C²`-dense among nonnegative tests in `ball 0 R`.
* `LaplacianLESectionStmt μ hR φs`: for a measure `μ` with `μ (ball 0 R) < ∞` and a `C²`-dense nonnegative family, the countable mass
  inequalities hold for a trace `w` iff `LaplacianLE w̃ μ (ball 0 R)` (the final LaplacianLE section identification).
-/

open HarmonicBalls

namespace MatedCRT

namespace ConeOriginNull

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff
open MatedCRT.CircleProcessSpace Real

/-! ### 0. The closed disk is compact -/

instance closedBall_zero_compactSpace (R : ℝ) : CompactSpace (closedBall (0 : ℂ) R) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)

/-! ### 1. The Laplacian of a smooth compactly supported test -/

/-- The Laplacian of a `C^∞` function on `ℂ` is continuous (Mathlib's `Laplacian.laplacian` is the sum of the second
derivatives along an orthonormal basis, `InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane`). -/
theorem continuous_laplacian_of_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (Laplacian.laplacian φ) :=
  LatticeProb.LaplacianCalculus.continuous_laplacian_of_contDiff (hφ.of_le (by norm_num))

/-- The Laplacian of a compactly supported `C^∞` function has compact support. -/
theorem hasCompactSupport_laplacian_of_hasCompactSupport {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) := by
  have h : HasCompactSupport (iteratedFDeriv ℝ 2 φ) := hc.iteratedFDeriv 2
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  exact (h.comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ => A ![1, 1])
      (by simp)).add
    (h.comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ => A ![Complex.I, Complex.I])
      (by simp))

/-- The Laplacian vanishes off the topological support of the function. -/
theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport φ) :
    Laplacian.laplacian φ z = 0 := by
  have h0 : iteratedFDeriv ℝ 2 φ z = 0 :=
    Function.notMem_support.1 fun h => hz (support_iteratedFDeriv_subset 2 h)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [h0]

/-! ### 2. The test integral of a trace on the closed disk -/

/-- `∫ w̃ Δφ` for a trace `w ∈ C(closedBall 0 R, ℝ)` and a test `φ`. The extension `w̃` is the radial
retraction extension `extendClosedBall 0 R hR w` (`BallExtension.lean`). -/
noncomputable def ballTestIntegral {R : ℝ} (hR : 0 < R) (φ : ℂ → ℝ) (w : BallFns R) : ℝ :=
  ∫ z, extendClosedBall 0 R hR w z * Laplacian.laplacian φ z

/-- Support and integrability: `w̃` is continuous and `Δφ` is continuous with compact support, so the integrand is
integrable. -/
theorem integrable_extend_mul_laplacian {R : ℝ} (hR : 0 < R) (w : BallFns R) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => extendClosedBall 0 R hR w z * Laplacian.laplacian φ z) :=
  Continuous.integrable_of_hasCompactSupport
    ((continuous_extendClosedBall hR w).mul (continuous_laplacian_of_contDiff hφ))
    (hasCompactSupport_laplacian_of_hasCompactSupport hc).mul_left

/-- **Lipschitz estimate.** For the sup norm on `C(closedBall 0 R, ℝ)`,
`|∫ w̃ Δφ - ∫ w̃' Δφ| ≤ (∫ |Δφ|) ‖w - w'‖`. -/
theorem dist_ballTestIntegral_le {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (w w' : BallFns R) :
    dist (ballTestIntegral hR φ w) (ballTestIntegral hR φ w') ≤
      (∫ z, ‖Laplacian.laplacian φ z‖) * dist w w' := by
  have hN : Integrable (fun z => ‖Laplacian.laplacian φ z‖) :=
    Continuous.integrable_of_hasCompactSupport (continuous_laplacian_of_contDiff hφ).norm
      (hasCompactSupport_laplacian_of_hasCompactSupport hc).norm
  unfold ballTestIntegral
  rw [Real.dist_eq, ← Real.norm_eq_abs, ← integral_sub (integrable_extend_mul_laplacian hR w hφ hc)
    (integrable_extend_mul_laplacian hR w' hφ hc)]
  refine (norm_integral_le_of_norm_le (hN.const_mul (dist w w')) (ae_of_all _ fun z => ?_)).trans_eq ?_
  · have hpt : ‖extendClosedBall 0 R hR w z - extendClosedBall 0 R hR w' z‖ ≤ dist w w' := by
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist
        (⟨closedBallRetraction 0 R z, closedBallRetraction_mem hR z⟩ : closedBall (0 : ℂ) R)
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hpt (norm_nonneg _)
  · rw [integral_const_mul, mul_comm (dist w w')]

theorem lipschitz_ballTestIntegral {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    LipschitzWith (Real.toNNReal (∫ z, ‖Laplacian.laplacian φ z‖)) (ballTestIntegral hR φ) :=
  LipschitzWith.of_dist_le' (dist_ballTestIntegral_le hR hφ hc)

theorem continuous_ballTestIntegral {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : Continuous (ballTestIntegral hR φ) :=
  (lipschitz_ballTestIntegral hR hφ hc).continuous

/-- The test integral is Borel on `PosCircleFns × BallFns R` (it depends on the trace only, and is continuous). -/
theorem measurable_ballTestIntegral_snd {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    Measurable fun p : PosCircleFns × BallFns R => ballTestIntegral hR φ p.2 :=
  ((continuous_ballTestIntegral hR hφ hc).comp continuous_snd).measurable

/-! ### 3. The Borel relation -/

/-- The mass inequality `∫ w̃ Δφ ≤ J_φ(c)` for one test `φ`, as a subset of `PosCircleFns × BallFns R`. Here
`J_φ = massLimit γ φ` is the checked mass code (`ConeOriginNullMeasurableProof.lean`). -/
def massTestSet (γ : ℝ) {R : ℝ} (hR : 0 < R) (φ : ℂ → ℝ) : Set (PosCircleFns × BallFns R) :=
  {p | ballTestIntegral hR φ p.2 ≤ massLimit γ φ p.1}

/-- Each mass inequality is a Borel set: both sides are Borel functions on the product (`massLimit` is measurable, the
test integral is continuous in the trace). -/
theorem measurableSet_massTestSet (γ : ℝ) {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : MeasurableSet (massTestSet γ hR φ) :=
  measurableSet_le (measurable_ballTestIntegral_snd hR hφ hc)
    ((measurable_massLimit γ φ hφ.continuous).comp measurable_fst)

/-- The Green-obstacle inequality at `y`, imposed off the pole: `y = 0` is unconstrained. This is the diagonal
convention of `HarmonicBalls.supersolutions` (the obstacle is imposed for `x ≠ z`); the junk value
`greenFunction _ 0 0 = 0` of the Green function never enters. -/
def pointGreenSet (t : ℝ) {R : ℝ} (hR : 0 < R) (y : ℂ) : Set (PosCircleFns × BallFns R) :=
  {p | y = 0 ∨ -t * greenFunction (ball 0 R) 0 y ≤ extendClosedBall 0 R hR p.2 y}

theorem measurableSet_pointGreenSet (t : ℝ) {R : ℝ} (hR : 0 < R) (y : ℂ) :
    MeasurableSet (pointGreenSet t hR y) := by
  have hev : Measurable fun p : PosCircleFns × BallFns R => extendClosedBall 0 R hR p.2 y :=
    ((continuous_eval_const
      (⟨closedBallRetraction 0 R y, closedBallRetraction_mem hR y⟩ : closedBall (0 : ℂ) R)).comp
      continuous_snd).measurable
  unfold pointGreenSet
  rw [ofPred_or]
  exact (MeasurableSet.const _).union (measurableSet_le measurable_const hev)

/-- **The Borel supersolution relation.** For a countable family of tests `φs` and a sequence `ps`
dense in the punctured closed disk: the mass inequalities for all `j` and the Green-obstacle inequalities at all
`ps k`. -/
def supersolutionRelation (γ t : ℝ) {R : ℝ} (hR : 0 < R) (φs : ℕ → ℂ → ℝ) (ps : ℕ → ℂ) :
    Set (PosCircleFns × BallFns R) :=
  (⋂ j, massTestSet γ hR (φs j)) ∩ ⋂ k, pointGreenSet t hR (ps k)

/-- **The relation is Borel.** Countable intersections of Borel sets. -/
theorem measurableSet_supersolutionRelation (γ t : ℝ) {R : ℝ} (hR : 0 < R) {φs : ℕ → ℂ → ℝ}
    (hφs : ∀ j, IsTestFunction (ball 0 R) (φs j)) (ps : ℕ → ℂ) :
    MeasurableSet (supersolutionRelation γ t hR φs ps) :=
  (MeasurableSet.iInter fun j => measurableSet_massTestSet γ hR (hφs j).1 (hφs j).2.1).inter
    (MeasurableSet.iInter fun k => measurableSet_pointGreenSet t hR (ps k))

/-! ### 4. Continuity of the centred Green function off the pole -/

/-- Off the pole the centred Green function is `(2π)⁻¹ max(log(R/|y|), 0)`: it is `(2π)⁻¹ log(R/|y|)` in the ball
(`greenFunction_zero_eq`) and `0` outside, where `log(R/|y|) ≤ 0`. -/
theorem greenFunction_zero_eq_max {R : ℝ} (hR : 0 < R) {y : ℂ} (hy0 : y ≠ 0) :
    greenFunction (ball 0 R) 0 y = (2 * π)⁻¹ * max (Real.log (R / ‖y‖)) 0 := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  by_cases hy : y ∈ ball (0 : ℂ) R
  · rw [greenFunction_zero_eq hR hy hy0]
    have hlog : 0 ≤ Real.log (R / ‖y‖) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hn, one_mul]
      exact (mem_ball_zero_iff.1 hy).le
    rw [max_eq_left hlog]
  · have hG : greenFunction (ball (0 : ℂ) R) 0 y = 0 := by
      unfold greenFunction
      simp [hy]
    have hR' : R ≤ ‖y‖ := not_lt.1 fun h => hy (mem_ball_zero_iff.2 h)
    have hlog : Real.log (R / ‖y‖) ≤ 0 := by
      apply Real.log_nonpos (div_nonneg hR.le hn.le)
      rw [div_le_one hn]
      exact hR'
    rw [hG, max_eq_right hlog, mul_zero]

/-- The centred Green function is continuous at every point off the pole. -/
theorem continuousAt_greenFunction_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ≠ 0) :
    ContinuousAt (fun y : ℂ => greenFunction (ball 0 R) 0 y) x := by
  have hEq : (fun y : ℂ => (2 * π)⁻¹ * max (Real.log (R / ‖y‖)) 0) =ᶠ[𝓝 x]
      (fun y : ℂ => greenFunction (ball 0 R) 0 y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (greenFunction_zero_eq_max hR hy).symm
  refine ContinuousAt.congr ?_ hEq
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hlogc : ContinuousAt (fun y : ℂ => Real.log (R / ‖y‖)) x :=
    ContinuousAt.log (continuousAt_const.div continuous_norm.continuousAt hn) (div_ne_zero hR.ne' hn)
  have hmax : ContinuousAt (fun y : ℂ => max (Real.log (R / ‖y‖)) 0) x :=
    ((continuous_id.max continuous_const).continuousAt).comp hlogc
  exact continuousAt_const.mul hmax

/-- The Green-obstacle function `y ↦ -t G_R(0,y)` is continuous off the pole. -/
theorem continuousAt_neg_mul_greenFunction (t : ℝ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ≠ 0) :
    ContinuousAt (fun y : ℂ => -t * greenFunction (ball 0 R) 0 y) x :=
  (continuousAt_greenFunction_zero hR hx).const_mul (-t)

/-! ### 5. Dense Green-obstacle inequalities -/

/-- **Dense obstacle equivalence.** The Green-obstacle inequalities at a dense punctured-disk sequence
are equivalent to all of them: the trace `w̃` and `-t G_R(0,·)` are continuous on the punctured closed disk, so the
inequality, which holds on a dense set, holds on its closure. -/
theorem forall_pointGreen_iff_of_dense (t : ℝ) {R : ℝ} (hR : 0 < R) {ps : ℕ → ℂ}
    (hps : ∀ k, ps k ∈ closedBall (0 : ℂ) R \ {0})
    (hdense : ∀ x ∈ closedBall (0 : ℂ) R \ {0}, x ∈ closure (range ps)) (w : BallFns R) :
    (∀ k, -t * greenFunction (ball 0 R) 0 (ps k) ≤ extendClosedBall 0 R hR w (ps k)) ↔
      ∀ x ∈ closedBall (0 : ℂ) R, x ≠ 0 → -t * greenFunction (ball 0 R) 0 x ≤ extendClosedBall 0 R hR w x := by
  refine ⟨fun h x hx hx0 => ?_, fun h k => h (ps k) (hps k).1 (fun h0 => (hps k).2 h0)⟩
  exact ContinuousWithinAt.closure_le (hdense x ⟨hx, hx0⟩)
    (continuousAt_neg_mul_greenFunction t hR hx0).continuousWithinAt
    (continuous_extendClosedBall hR w).continuousWithinAt
    (by rintro _ ⟨k, rfl⟩; exact h k)

/-- **Section formula for the relation.** At a circle process `c` and a trace `w`, the pair lies in the
relation iff the mass inequalities against `J_φ(c)` hold for all `j` and the Green-obstacle inequalities hold on all of
the punctured closed disk. -/
theorem mem_supersolutionRelation_iff (γ t : ℝ) {R : ℝ} (hR : 0 < R) {φs : ℕ → ℂ → ℝ} {ps : ℕ → ℂ}
    (hps : ∀ k, ps k ∈ closedBall (0 : ℂ) R \ {0})
    (hdense : ∀ x ∈ closedBall (0 : ℂ) R \ {0}, x ∈ closure (range ps)) (c : PosCircleFns) (w : BallFns R) :
    (c, w) ∈ supersolutionRelation γ t hR φs ps ↔
      (∀ j, ballTestIntegral hR (φs j) w ≤ massLimit γ (φs j) c) ∧
        ∀ x ∈ closedBall (0 : ℂ) R, x ≠ 0 → -t * greenFunction (ball 0 R) 0 x ≤ extendClosedBall 0 R hR w x := by
  simp only [supersolutionRelation, mem_inter_iff, mem_iInter, massTestSet, pointGreenSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hM, hK⟩
    exact ⟨hM, (forall_pointGreen_iff_of_dense t hR hps hdense w).1
      fun k => (hK k).resolve_left fun h0 => (hps k).2 h0⟩
  · rintro ⟨hM, hG⟩
    exact ⟨hM, fun k => Or.inr ((forall_pointGreen_iff_of_dense t hR hps hdense w).2 hG k)⟩

/-! ### 6. Traces of supersolutions -/

/-- **Traces of supersolutions.** `w` is the trace of a supersolution of the obstacle problem `(μ, R, t)` iff its
radial-retraction extension satisfies `LaplacianLE` on `ball 0 R` and the Green constraint off the pole holds on the
closed disk. The extension `w̃` is itself the witness for `⇐`. Conversely, a supersolution `u` with trace `w` has
`LaplacianLE w̃`, because `u = w̃` on the closed disk and `Δφ` vanishes off the disk for every test `φ` supported in
`ball 0 R`, so the two integrands agree everywhere. -/
theorem mem_superTraces_iff {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) (w : BallFns R) :
    w ∈ superTraces μ R t ↔ LaplacianLE (extendClosedBall 0 R hR w) μ (ball 0 R) ∧
      ∀ x ∈ closedBall (0 : ℂ) R, x ≠ 0 → -t * greenFunction (ball 0 R) 0 x ≤ extendClosedBall 0 R hR w x := by
  constructor
  · rintro ⟨u, ⟨-, hLE, hobs⟩, hu⟩
    have hagree : ∀ z ∈ closedBall (0 : ℂ) R, u z = extendClosedBall 0 R hR w z := fun z hz => by
      rw [extendClosedBall_of_mem hR w hz]
      exact hu ⟨z, hz⟩
    refine ⟨⟨(continuous_extendClosedBall hR w).continuousOn.locallyIntegrableOn measurableSet_ball,
        fun φ hφ hφ0 hint => ?_⟩,
      fun x hx hx0 => ?_⟩
    · have hEq : (fun z => extendClosedBall 0 R hR w z * Laplacian.laplacian φ z) =
          fun z => u z * Laplacian.laplacian φ z := by
        funext z
        by_cases hz : z ∈ closedBall (0 : ℂ) R
        · rw [hagree z hz]
        · have hz' : z ∉ tsupport φ := fun h => hz (ball_subset_closedBall (hφ.2.2 h))
          simp [laplacian_eq_zero_of_notMem_tsupport hz']
      rw [hEq]
      exact hLE.2 φ hφ hφ0 hint
    · have h := hobs x hx hx0
      rwa [hagree x hx] at h
  · rintro ⟨hLE, hG⟩
    exact ⟨extendClosedBall 0 R hR w, ⟨(continuous_extendClosedBall hR w).continuousOn, hLE,
      fun x hx hx0 => hG x hx hx0⟩, fun x => extendClosedBall_of_mem hR w x.2⟩

/-! ### 7. Residuals (exact types; not proved in this file) -/

/-- **Residual A: countable `C²` approximation.** Every nonnegative test `φ` supported in `ball 0 R`
is approximated, together with its Laplacian, uniformly by members of the family `φs`. This is the density of the
countable family in the `C²` topology on nonnegative tests; it is the input that passes from the countable
inequalities to all tests, given `μ (ball 0 R) < ∞` (residual B). -/
def CountableC2DenseStmt (R : ℝ) (φs : ℕ → ℂ → ℝ) : Prop :=
  ∀ φ : ℂ → ℝ, IsTestFunction (ball 0 R) φ → (∀ z, 0 ≤ φ z) → ∀ ε : ℝ, 0 < ε →
    ∃ j : ℕ, (∀ z, |φs j z - φ z| ≤ ε) ∧
      ∀ z, |Laplacian.laplacian (φs j) z - Laplacian.laplacian φ z| ≤ ε

/-- **Residual A′: existence of a countable `C²`-dense family.** For every radius `R > 0` some countable
family of nonnegative tests in `ball 0 R` is `C²`-dense (`CountableC2DenseStmt`). `CodeSectionStmt` needs this, for each
radius, to choose the family in the relation; it is stated here and not proved. -/
def CountableC2FamilyStmt : Prop :=
  ∀ R : ℝ, 0 < R → ∃ φs : ℕ → ℂ → ℝ,
    (∀ j, IsTestFunction (ball 0 R) (φs j) ∧ ∀ z, 0 ≤ φs j z) ∧ CountableC2DenseStmt R φs

/-- **Residual B: final LaplacianLE section identification.** Let `μ` be a measure with
`μ (ball 0 R) < ∞`, and let `φs` be a `C²`-dense family of nonnegative tests in `ball 0 R`. Then for every trace `w`,
the countable mass inequalities `∫ w̃ Δφ_j ≤ ∫ φ_j dμ` hold iff `Δ w̃ ≤ μ` in `ball 0 R` (`LaplacianLE`). -/
def LaplacianLESectionStmt (μ : Measure ℂ) {R : ℝ} (hR : 0 < R) (φs : ℕ → ℂ → ℝ) : Prop :=
  μ (ball 0 R) < ⊤ → (∀ j, IsTestFunction (ball 0 R) (φs j) ∧ ∀ z, 0 ≤ φs j z) → CountableC2DenseStmt R φs →
    ∀ w : BallFns R, (∀ j, ballTestIntegral hR (φs j) w ≤ ∫ z, φs j z ∂μ) ↔
      LaplacianLE (extendClosedBall 0 R hR w) μ (ball 0 R)

/-- **Section of the relation, conditional on the residuals.** Given the mass identity `massLimit γ φ_j c = ∫ φ_j dμ`
for the family (the exact integral identity of `massLimit_eq_integral` on an LQG event), the section of the Borel
relation at `c` is exactly the set of traces of supersolutions of `(μ, R, t)`. -/
theorem mem_supersolutionRelation_iff_of_residuals (γ t : ℝ) {R : ℝ} (hR : 0 < R) {φs : ℕ → ℂ → ℝ}
    {ps : ℕ → ℂ} (hps : ∀ k, ps k ∈ closedBall (0 : ℂ) R \ {0})
    (hdense : ∀ x ∈ closedBall (0 : ℂ) R \ {0}, x ∈ closure (range ps))
    {μ : Measure ℂ} (hμ : μ (ball 0 R) < ⊤)
    (hfam : ∀ j, IsTestFunction (ball 0 R) (φs j) ∧ ∀ z, 0 ≤ φs j z)
    (hC2 : CountableC2DenseStmt R φs) (hLE : LaplacianLESectionStmt μ hR φs)
    (c : PosCircleFns) (hmass : ∀ j, massLimit γ (φs j) c = ∫ z, φs j z ∂μ) (w : BallFns R) :
    (c, w) ∈ supersolutionRelation γ t hR φs ps ↔ w ∈ superTraces μ R t := by
  rw [mem_supersolutionRelation_iff γ t hR hps hdense c w, mem_superTraces_iff hR w]
  have hM := hLE hμ hfam hC2 w
  simp only [hmass]
  exact and_congr hM Iff.rfl

end ConeOriginNull

end MatedCRT
