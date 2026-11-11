import MatedCRT.Audit.LocalDirichletProjectionComponents

/-!
# Harmonic remainder of one Dirichlet projection realization

The harmonic-remainder component of clause (g) of
`DirichletProjectionRealization`, for one whole-plane GFF `(hC, hcirc)` and one disk `D = ball c ρ`.

Proved here, from the realization carriers (`IsWholePlaneGFF`, the Dirichlet subspaces `K D`, the observables `repO`,
the isonormal process `X`):

* `representedRemainder`: the represented difference `z ↦ hcirc o (δ z) z − X(P_D rep(circle (δ z) z)) o`, read at the
  radius `δ z = (ρ − |z − c|)/2`, which is admissible for every `z ∈ D`. It is a continuous modification of the
  remainder: one radius per point replaces the countable family of circles of .
* `identity_representedRemainder`, `representedRemainder_eq_ae`: the circle identity of (g) on every admissible circle,
  and agreement with the given remainder `H` at each point, almost surely.
* `ae_continuousOn_representedRemainder`: almost surely the represented remainder is continuous on `D`.
* `harmonicRemainder_of_annihilation`: if the represented remainder annihilates planar Laplacians of tests supported in
  `D` (`RemainderAnnihilationStep`), then it is almost surely harmonic on `D`, by the
  named Step `WeylLemmaContinuousStmt` (source status in its docstring).
* `isHarmonicOnDisk_add_const`, `ae_isHarmonicOnDisk_add_const`: harmonicity survives adding a random constant, so the
  unit-circle random-constant normalization preserves it. No independence of normalized pieces is used.

Named premises (see docs/campaign/COUNTED.md): `RemainderAnnihilationStep` and `WeylLemmaContinuousStmt`, a
named Step retained as an explicit hypothesis (docstrings give the exact types and source status), the a.s. continuity of
the field and of the projected circle averages (predecessor realization fields), and the circle identity for some
remainder `H`. Nothing here closes Proposition 4.2.
-/

open MeasureTheory Filter Topology Set HarmonicBalls
open scoped ContDiff

namespace MatedCRT

noncomputable section

/-- Planar Laplacian `∂ₓ² + ∂ᵧ²` of `φ : ℂ → ℝ`: the sum of the second derivatives along the directions `1` and `i`. -/
def planarLaplacianC (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  iteratedFDeriv ℝ 2 φ z ![(1 : ℂ), 1] + iteratedFDeriv ℝ 2 φ z ![Complex.I, Complex.I]

/-- Smooth test functions with compact support in `D`. -/
def IsSmoothTestFunctionIn (D : Set ℂ) (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- `u` annihilates planar Laplacians of test functions supported in `D`: `∫ u Δφ = 0` for every smooth test function
`φ` with compact support in `D`. This is the distributional form of `Δ u = 0` on `D` (Armitage–Gardiner). For `u`
continuous on `D` the integrand is continuous and vanishes outside the compact set `tsupport φ ⊆ D`, so the integral is
the genuine one. -/
def LaplacianAnnihilatesOn (D : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : ℂ → ℝ, IsSmoothTestFunctionIn D φ → ∫ z, u z * planarLaplacianC φ z = 0

/-- **Named Step: Weyl's lemma in continuous form, with the mean-value characterization.** For an open set `D`,
a function `u` continuous on `D` that annihilates planar Laplacians of test functions supported in `D` is harmonic on `D`
in the sense of `IsHarmonicOnDisk` (continuity and the circle mean-value property on every closed ball contained in `D`).
This Prop is retained as an explicit hypothesis (`hWeyl`) of the conditional components that use it. It is a hypothesis of this file, not a literature result (see docs/campaign/COUNTED.md).

Source status (see `docs/campaign/MATH-OPEN-20261109.md`):
* Weyl1940 locator: H. Weyl, "The method of orthogonal projection in potential theory", Duke Math. J. 7 (1940), Lemma 2,
  p. 415, as cited by the Wikipedia article "Weyl's lemma (Laplace equation)". The printed text has not been checked.
  The campaign doc records Project Euclid full-page and download attempts that did not expose it; a bibliographic search
  confirmed only the journal record (volume 7, pp. 411–444). The lemma number and the page: see docs/campaign/MATH-OPEN-20261109.md. The DOI recorded
  in the campaign doc, `10.1215/S0012-7094-40-00725-6`, is only a pointer to the source (see docs/campaign/MATH-OPEN-20261109.md).
* Armitage–Gardiner attribution (*Classical Potential Theory*): no theorem number is given; see docs/campaign/MATH-OPEN-20261109.md.
* The conclusion bundles two facts, which are not established as one cited lemma: (i) Weyl's lemma proper, that a function
  annihilating planar Laplacians of test functions supported in `D` is (almost everywhere) a harmonic function on `D`;
  (ii) the mean-value characterization of harmonic functions that `IsHarmonicOnDisk` packages into the conclusion
  (`InsertionCoordinate.lean`, `IsHarmonicOnDisk`), namely the circle mean-value property on closed balls in `D`.
  This file writes neither a bridge from (i) to (ii) nor a printed locator for that bridge.

Accepting the conditional components that use this Prop does not require moving it into `MatedCRT/External`; source
admission is a separate decision. -/
def WeylLemmaContinuousStmt : Prop :=
  ∀ (D : Set ℂ) (u : ℂ → ℝ), IsOpen D → ContinuousOn u D → LaplacianAnnihilatesOn D u → IsHarmonicOnDisk D u

/-- The radius `δ z = (ρ − |z − c|)/2`: for `z ∈ ball c ρ` it is positive and `closedBall z (δ z) ⊆ ball c ρ`. -/
def boundaryRadius (c : ℂ) (ρ : ℝ) (z : ℂ) : ℝ := (ρ - dist z c) / 2

lemma continuous_boundaryRadius (c : ℂ) (ρ : ℝ) : Continuous (boundaryRadius c ρ) := by
  unfold boundaryRadius
  exact (continuous_const.sub (continuous_id.dist continuous_const)).div_const 2

lemma boundaryRadius_admissible {c z : ℂ} {ρ : ℝ} (hz : z ∈ Metric.ball c ρ) :
    0 < boundaryRadius c ρ z ∧ Metric.closedBall z (boundaryRadius c ρ z) ⊆ Metric.ball c ρ := by
  have hd : dist z c < ρ := Metric.mem_ball.mp hz
  refine ⟨?_, fun w hw => ?_⟩
  · unfold boundaryRadius
    linarith
  · have hw' : dist w z ≤ (ρ - dist z c) / 2 := Metric.mem_closedBall.mp hw
    have htri : dist w c ≤ dist w z + dist z c := dist_triangle w z c
    rw [Metric.mem_ball]
    linarith

/-- The represented difference of a field `f` and a projection `g`, read at the radius `δ z`:
`z ↦ f (δ z) z − g (δ z) z`. -/
def representedDifference (c : ℂ) (ρ : ℝ) (f g : ℝ → ℂ → ℝ) : ℂ → ℝ :=
  fun z => f (boundaryRadius c ρ z) z - g (boundaryRadius c ρ z) z

/-- Continuity of `z ↦ G (δ z, z)` on `ball c ρ` from continuity of `G` on the admissible circles. -/
lemma continuousOn_representedDifference (c : ℂ) (ρ : ℝ) (G : ℝ × ℂ → ℝ)
    (hG : ContinuousOn G {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ Metric.ball c ρ}) :
    ContinuousOn (fun z => G (boundaryRadius c ρ z, z)) (Metric.ball c ρ) := by
  have hmap : ContinuousOn (fun z : ℂ => (boundaryRadius c ρ z, z)) (Metric.ball c ρ) :=
    ((continuous_boundaryRadius c ρ).prodMk continuous_id).continuousOn
  exact hG.comp hmap (fun z hz => boundaryRadius_admissible hz)

/-- The Dirichlet projection of the observable of the circle `circle r z`, as a random variable for the outcome `o`:
`X(P_D rep(circle r z)) o`, with `P_D` the orthogonal projection onto the Dirichlet subspace `K D`. -/
def projCircleFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    (K : Set ℂ → Submodule ℝ E) [∀ D : Set ℂ, (K D).HasOrthogonalProjection]
    (repO : GFFObservable → E) (X : E → Ω → ℝ) (D : Set ℂ) (o : Ω) : ℝ → ℂ → ℝ :=
  fun r z => X ((K D).starProjection (repO (.circle r z))) o

/-- The represented remainder of one Dirichlet projection realization on `ball c ρ`, for the outcome `o`: the field on
circles minus its projection, read at the radius `δ z`. -/
def representedRemainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    (K : Set ℂ → Submodule ℝ E) [∀ D : Set ℂ, (K D).HasOrthogonalProjection]
    (repO : GFFObservable → E) (X : E → Ω → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (ρ : ℝ) (o : Ω) : ℂ → ℝ :=
  representedDifference c ρ (hcirc o) (projCircleFun K repO X (Metric.ball c ρ) o)

/-- **Named step.** The represented remainder annihilates planar Laplacians of test functions supported
in `ball c ρ`, almost surely. The paper asserts this ("the remainder annihilates Δφ for tests supported in D, so is
harmonic") without a written argument. The expected source is the orthogonality of the harmonic part to the zero-boundary
Dirichlet subspace (the Riesz identity), which is not part of this file. It is stated pathwise, for almost every `o` and all
tests at once; passing from a per-test almost sure statement to this form is not part of this file. -/
def RemainderAnnihilationStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (K : Set ℂ → Submodule ℝ E) [∀ D : Set ℂ, (K D).HasOrthogonalProjection]
    (repO : GFFObservable → E) (X : E → Ω → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (ρ : ℝ) : Prop :=
  ∀ᵐ o ∂P, LaplacianAnnihilatesOn (Metric.ball c ρ) (representedRemainder K repO X hcirc c ρ o)

/-- The circle identity of clause (g) holds for the represented remainder on every admissible circle, almost surely.
Both the circle `(r, z)` and the circle `(δ z, z)` satisfy the identity for the given remainder `H`, so the two
represented values agree. -/
lemma identity_representedRemainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (K : Set ℂ → Submodule ℝ E)
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] (repO : GFFObservable → E) (X : E → Ω → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (ρ : ℝ) (H : Ω → ℂ → ℝ)
    (hident : ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → ∀ᵐ o ∂P,
      hcirc o r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) o + H o z)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hsub : Metric.closedBall z r ⊆ Metric.ball c ρ) :
    ∀ᵐ o ∂P, hcirc o r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) o +
      representedRemainder K repO X hcirc c ρ o z := by
  have hz : z ∈ Metric.ball c ρ := hsub (Metric.mem_closedBall_self hr.le)
  obtain ⟨hδ, hδsub⟩ := boundaryRadius_admissible hz
  filter_upwards [hident r z hr hsub, hident _ z hδ hδsub] with o e1 e2
  simp only [representedRemainder, representedDifference, projCircleFun]
  linarith

/-- The represented remainder agrees almost surely with the given remainder `H` at each point of `ball c ρ`. -/
lemma representedRemainder_eq_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (K : Set ℂ → Submodule ℝ E)
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] (repO : GFFObservable → E) (X : E → Ω → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (ρ : ℝ) (H : Ω → ℂ → ℝ)
    (hident : ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → ∀ᵐ o ∂P,
      hcirc o r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) o + H o z)
    {z : ℂ} (hz : z ∈ Metric.ball c ρ) :
    ∀ᵐ o ∂P, representedRemainder K repO X hcirc c ρ o z = H o z := by
  obtain ⟨hδ, hδsub⟩ := boundaryRadius_admissible hz
  filter_upwards [hident _ z hδ hδsub] with o e2
  simp only [representedRemainder, representedDifference, projCircleFun]
  linarith

/-- Almost surely the represented remainder is continuous on `ball c ρ`, from the a.s. continuity of the field on
circles (`IsWholePlaneGFF`) and of the projected circle averages on admissible circles (the realization's continuity
clause). This is the continuity extension of , here at one radius per point. -/
lemma ae_continuousOn_representedRemainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (K : Set ℂ → Submodule ℝ E)
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] (repO : GFFObservable → E) (X : E → Ω → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (ρ : ℝ)
    (hcircCont : ∀ᵐ o ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc o p.1 p.2) (Ioi 0 ×ˢ univ))
    (hRcont : ∀ᵐ o ∂P, ContinuousOn (fun p : ℝ × ℂ => projCircleFun K repO X (Metric.ball c ρ) o p.1 p.2)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ Metric.ball c ρ}) :
    ∀ᵐ o ∂P, ContinuousOn (representedRemainder K repO X hcirc c ρ o) (Metric.ball c ρ) := by
  filter_upwards [hcircCont, hRcont] with o h1 h2
  have hG : ContinuousOn (fun p : ℝ × ℂ => hcirc o p.1 p.2 - projCircleFun K repO X (Metric.ball c ρ) o p.1 p.2)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ Metric.ball c ρ} :=
    (h1.mono fun p hp => ⟨hp.1, Set.mem_univ _⟩).sub h2
  exact continuousOn_representedDifference c ρ _ hG

/-- Harmonicity on `D` from the named Step `WeylLemmaContinuousStmt`: a continuous function annihilating
Laplacians of tests in `D` is harmonic on `D` (applied to the open set `D`; source status in its docstring). -/
lemma isHarmonicOnDisk_of_laplacian_annihilation (hWeyl : WeylLemmaContinuousStmt) {c : ℂ} {ρ : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (Metric.ball c ρ)) (hann : LaplacianAnnihilatesOn (Metric.ball c ρ) u) :
    IsHarmonicOnDisk (Metric.ball c ρ) u :=
  hWeyl (Metric.ball c ρ) u Metric.isOpen_ball hu hann

/-- Harmonicity on `D` survives adding a constant: continuity is preserved, and the circle averages of `H + k` are those
of `H` plus `k` (the unit-circle random-constant normalization). -/
lemma isHarmonicOnDisk_add_const {D : Set ℂ} {H : ℂ → ℝ} (hH : IsHarmonicOnDisk D H) (k : ℝ) :
    IsHarmonicOnDisk D (fun z => H z + k) := by
  obtain ⟨hcont, hmvp⟩ := hH
  refine ⟨hcont.add continuousOn_const, fun z r hr hsub => ?_⟩
  have hI : IntervalIntegrable (fun θ : ℝ => H (circleMap z r θ)) MeasureTheory.volume 0 (2 * Real.pi) := by
    refine ContinuousOn.intervalIntegrable (hcont.comp (continuous_circleMap z r).continuousOn ?_)
    exact fun θ _ => hsub (circleMap_mem_closedBall z hr.le θ)
  have hJ : ∫ θ in (0 : ℝ)..2 * Real.pi, (H (circleMap z r θ) + k)
      = (∫ θ in (0 : ℝ)..2 * Real.pi, H (circleMap z r θ)) + ∫ _ in (0 : ℝ)..2 * Real.pi, k :=
    intervalIntegral.integral_add hI intervalIntegrable_const
  have hmz := hmvp z r hr hsub
  have h2 : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
  simp only [Real.circleAverage, smul_eq_mul] at hmz ⊢
  rw [hJ, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  linear_combination hmz + (-k) * h2

/-- The almost sure form of `isHarmonicOnDisk_add_const`, for a random constant `k o` (no independence is used). -/
lemma ae_isHarmonicOnDisk_add_const {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D : Set ℂ} {H : Ω → ℂ → ℝ}
    (hH : ∀ᵐ o ∂P, IsHarmonicOnDisk D (H o)) (k : Ω → ℝ) :
    ∀ᵐ o ∂P, IsHarmonicOnDisk D (fun z => H o z + k o) :=
  hH.mono fun o h => isHarmonicOnDisk_add_const h (k o)

/-- **Harmonic remainder component of clause (g) of `DirichletProjectionRealization`.** Given the realization carriers, the
a.s. continuity of the field on circles and of the projected circle averages, the circle identity for a remainder `H` on
every admissible circle, the annihilation `RemainderAnnihilationStep`, and the named Step
`WeylLemmaContinuousStmt`: the represented remainder is a.s. harmonic on `ball c ρ`, satisfies the circle identity on
every admissible circle, and agrees a.s. with `H` at each point of `ball c ρ`. -/
theorem harmonicRemainder_of_annihilation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (K : Set ℂ → Submodule ℝ E) [∀ D : Set ℂ, (K D).HasOrthogonalProjection]
    (repO : GFFObservable → E) (X : E → Ω → ℝ) (c : ℂ) (ρ : ℝ) (H : Ω → ℂ → ℝ)
    (hWeyl : WeylLemmaContinuousStmt)
    (hRcont : ∀ᵐ o ∂P, ContinuousOn (fun p : ℝ × ℂ => projCircleFun K repO X (Metric.ball c ρ) o p.1 p.2)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ Metric.ball c ρ})
    (hident : ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → ∀ᵐ o ∂P,
      hcirc o r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) o + H o z)
    (hAnn : RemainderAnnihilationStep P K repO X hcirc c ρ) :
    (∀ᵐ o ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (representedRemainder K repO X hcirc c ρ o)) ∧
    (∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → ∀ᵐ o ∂P,
      hcirc o r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) o +
        representedRemainder K repO X hcirc c ρ o z) ∧
    (∀ z ∈ Metric.ball c ρ, ∀ᵐ o ∂P, representedRemainder K repO X hcirc c ρ o z = H o z) := by
  have hcont := ae_continuousOn_representedRemainder K repO X hcirc c ρ hGFF.ae_continuousOn_circle hRcont
  have hAnn' : ∀ᵐ o ∂P, LaplacianAnnihilatesOn (Metric.ball c ρ) (representedRemainder K repO X hcirc c ρ o) := hAnn
  refine ⟨?_, fun r z hr hsub => identity_representedRemainder K repO X hcirc c ρ H hident hr hsub,
    fun z hz => representedRemainder_eq_ae K repO X hcirc c ρ H hident hz⟩
  filter_upwards [hcont, hAnn'] with o h1 h2
  exact isHarmonicOnDisk_of_laplacian_annihilation hWeyl h1 h2

end

end MatedCRT
