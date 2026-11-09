import MatedCRT.Defs.DirichletGFF
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Covariance of the Gaussian Dirichlet projection of the pairing observations (steps3:603-613)

Task `z1-steps3-dirichlet-projection-covariance`. A bounded covariance component for the producer
`LocalDirichletCoordinatewiseStep` (`InsertionLocalCircleRecovery.lean:114-123`). It is not that producer.

The objects are an isonormal Gaussian process `X` on a real inner product space `E` (the energy space of the whole-plane
field) and the orthogonal projection `K.starProjection` onto a closed subspace `K` (the Dirichlet subspace `H_0^1(D)`).
No field is constructed here: `X` is an arbitrary isonormal process.

* `IsIsonormalProcess P X`: a centered, jointly Gaussian family `X u` with covariance the inner product `⟪u, v⟫`
  (isonormal Gaussian process, Nualart's name for a Gaussian Hilbert space).
* `IsIsonormalProcess.gaussian_projection`, `.covariance_projection`, `.covariance_projection_residual`: the projected
  family `X (K.starProjection u)` is a centered Gaussian family with covariance `⟪K.starProjection u, K.starProjection v⟫`,
  and it is uncorrelated with the residual `u - K.starProjection u` (the orthogonality of steps3:605-606).
* `dirichletPairing_projection_gaussian_covariance`: for test functions `φ, ψ` admissible on `D`, the observations
  `X (K.starProjection (rep φ))` form a centered Gaussian family with covariance `dirichletGFFCovariance D (pairing φ)
  (pairing ψ)`, the kernel `2π G_D` of `Defs/DirichletGFF.lean`. The covariance is derived from the orthogonal projection,
  not assumed.

Two named deterministic inputs are used, and no others:

* `DirichletRieszIdentity D ev rep K`: the representative `rep φ` of a test function satisfies `⟪rep φ, f⟫ = 2π ∫ φ · ev f`
  for `f ∈ K`, with the energy normalization `⟪·,·⟫ = 2π ∫∇·∇·`. This is the weak form of `-Δ(rep φ) = φ`; its proof by
  integration by parts is not written here.
* `DirichletProjectionGreenRealization D ev rep K` (projection-realization premise): the orthogonal projection of `rep ψ`
  onto `K` has Dirichlet function `x ↦ ∫ G_D(x,y) ψ(y) dy` almost everywhere on `D`. It identifies the projection onto
  `H_0^1(D)` with the Green operator. steps3:605-608 asserts that orthogonality gives covariance `2πG_D` but does not
  write this identification; it is not proved here.

Neither premise is a Gaussian-law premise: the covariance of the projected observations is derived from them.
Still open (recorded in `reports/z1.md`): the realization of `X` from the whole-plane GFF on the same probability space,
a function-valued version of the projected field, the circle observables, the harmonicity of the remainder, and the
coordinatewise circle identity.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls

namespace MatedCRT

/-- An isonormal Gaussian process on the real inner product space `E` (Nualart's name for a Gaussian Hilbert space):
a family `X u` of real random variables indexed by `E`, jointly Gaussian and centered, whose covariance is the inner
product `⟪u, v⟫`. -/
structure IsIsonormalProcess {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) (X : E → Ω → ℝ) : Prop where
  /-- Finite families are jointly Gaussian. -/
  gaussian : IsGaussianProcess X P
  /-- Each `X u` is centered. -/
  centered : ∀ u, ∫ ω, X u ω ∂P = 0
  /-- The covariance is the inner product. -/
  covariance : ∀ u v, cov[X u, X v; P] = inner ℝ u v

/-- The projected family `u ↦ X (K.starProjection u)` is jointly Gaussian: `X` composed with the orthogonal projection. -/
theorem IsIsonormalProcess.gaussian_projection {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : Measure Ω} {X : E → Ω → ℝ} (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hX : IsIsonormalProcess P X) :
    IsGaussianProcess (fun u ω => X (K.starProjection u) ω) P :=
  hX.gaussian.comp_right (fun u => K.starProjection u)

/-- The covariance of the projected observations is the inner product of the projections. -/
theorem IsIsonormalProcess.covariance_projection {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : Measure Ω} {X : E → Ω → ℝ} (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hX : IsIsonormalProcess P X) (u v : E) :
    cov[fun ω => X (K.starProjection u) ω, fun ω => X (K.starProjection v) ω; P] =
      inner ℝ (K.starProjection u) (K.starProjection v) :=
  hX.covariance _ _

/-- The projected observation is uncorrelated with the residual `u - K.starProjection u`: the orthogonality of the
projection (steps3:605-606). -/
theorem IsIsonormalProcess.covariance_projection_residual {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : Measure Ω} {X : E → Ω → ℝ} (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hX : IsIsonormalProcess P X) (u : E) :
    cov[fun ω => X (K.starProjection u) ω, fun ω => X (u - K.starProjection u) ω; P] = 0 := by
  refine (hX.covariance (K.starProjection u) (u - K.starProjection u)).trans ?_
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero u (K.starProjection u) (K.starProjection_apply_mem u)

/-- Self-adjointness and idempotence of the orthogonal projection: `⟪Pu, Pv⟫ = ⟪u, Pv⟫`. -/
theorem inner_starProjection_starProjection_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (u v : E) :
    inner ℝ (K.starProjection u) (K.starProjection v) = inner ℝ u (K.starProjection v) := by
  rw [K.inner_starProjection_left_eq_right u (K.starProjection v),
    K.starProjection_eq_self_iff.2 (K.starProjection_apply_mem v)]

/-- **Riesz identity** (named deterministic premise). `rep φ ∈ E` is the representative of a test function `φ`
admissible on `D`, `ev f : ℂ → ℝ` is the Dirichlet function of `f ∈ E`, and `⟪·,·⟫` is the energy inner product
normalized as `2π ∫ ∇f·∇g`. The identity `⟪rep φ, f⟫ = 2π ∫ φ · ev f` for `f ∈ K` is the weak form of `-Δ(rep φ) = φ`. -/
def DirichletRieszIdentity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (D : Set ℂ)
    (ev : E → ℂ → ℝ) (rep : (ℂ → ℝ) → E) (K : Submodule ℝ E) : Prop :=
  ∀ φ : ℂ → ℝ, IsTestFunction D φ → ∀ f ∈ K, inner ℝ (rep φ) f = 2 * Real.pi * ∫ x, φ x * ev f x

/-- **Projection-realization premise** (named deterministic input). For each test function `ψ` admissible on `D`, the
orthogonal projection of `rep ψ` onto the Dirichlet subspace `K` has Dirichlet function `x ↦ ∫ G_D(x,y) ψ(y) dy`
almost everywhere on `D`, where `G_D = HarmonicBalls.greenFunction D`. -/
def DirichletProjectionGreenRealization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (D : Set ℂ)
    (ev : E → ℂ → ℝ) (rep : (ℂ → ℝ) → E) (K : Submodule ℝ E) [K.HasOrthogonalProjection] : Prop :=
  ∀ ψ : ℂ → ℝ, IsTestFunction D ψ → ∀ᵐ x ∂(volume : Measure ℂ), x ∈ D →
    ev (K.starProjection (rep ψ)) x = ∫ y, HarmonicBalls.greenFunction D x y * ψ y

/-- **Covariance of the projected pairing observations.** Let `X` be isonormal on `E`, let `K` be a Dirichlet subspace
with orthogonal projection `K.starProjection`, and assume the Riesz identity and the projection-realization premise for
`(D, ev, rep, K)`. Then the observations `φ ↦ X (K.starProjection (rep φ))`, over the test functions admissible on `D`,
form a centered Gaussian family whose covariance is `dirichletGFFCovariance D (pairing φ) (pairing ψ)`, that is
`2π ∫∫ φ(x) G_D(x,y) ψ(y)`. -/
theorem dirichletPairing_projection_gaussian_covariance {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : Measure Ω} {X : E → Ω → ℝ} {D : Set ℂ} {ev : E → ℂ → ℝ} {rep : (ℂ → ℝ) → E}
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (hX : IsIsonormalProcess P X)
    (hR1 : DirichletRieszIdentity D ev rep K) (hR2 : DirichletProjectionGreenRealization D ev rep K) :
    IsGaussianProcess (fun φ : {φ : ℂ → ℝ // IsTestFunction D φ} => fun ω => X (K.starProjection (rep φ.1)) ω) P ∧
      (∀ φ : ℂ → ℝ, IsTestFunction D φ → ∫ ω, X (K.starProjection (rep φ)) ω ∂P = 0) ∧
      ∀ φ ψ : ℂ → ℝ, IsTestFunction D φ → IsTestFunction D ψ →
        cov[fun ω => X (K.starProjection (rep φ)) ω, fun ω => X (K.starProjection (rep ψ)) ω; P] =
          dirichletGFFCovariance D (.pairing φ) (.pairing ψ) := by
  refine ⟨hX.gaussian.comp_right (fun φ : {φ : ℂ → ℝ // IsTestFunction D φ} => K.starProjection (rep φ.1)),
    fun φ _ => hX.centered _, ?_⟩
  intro φ ψ hφ hψ
  refine (hX.covariance (K.starProjection (rep φ)) (K.starProjection (rep ψ))).trans ?_
  rw [inner_starProjection_starProjection_right K, hR1 φ hφ (K.starProjection (rep ψ))
    (K.starProjection_apply_mem _)]
  have hint : ∫ x, φ x * ev (K.starProjection (rep ψ)) x =
      ∫ x, φ x * ∫ y, HarmonicBalls.greenFunction D x y * ψ y := by
    refine integral_congr_ae ?_
    filter_upwards [hR2 ψ hψ] with x hx
    by_cases hxD : x ∈ D
    · rw [hx hxD]
    · have hφx : φ x = 0 := by
        by_contra hne
        exact hxD (hφ.2.2 (subset_tsupport φ (Function.mem_support.2 hne)))
      rw [hφx, zero_mul, zero_mul]
  rw [hint]
  have hinner : ∀ x : ℂ, ∫ y, ψ y * (2 * Real.pi * HarmonicBalls.greenFunction D x y) =
      2 * Real.pi * ∫ y, HarmonicBalls.greenFunction D x y * ψ y := by
    intro x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  show 2 * Real.pi * ∫ x, φ x * ∫ y, HarmonicBalls.greenFunction D x y * ψ y =
    ∫ x, φ x * ∫ y, ψ y * (2 * Real.pi * HarmonicBalls.greenFunction D x y)
  simp_rw [hinner]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end MatedCRT
