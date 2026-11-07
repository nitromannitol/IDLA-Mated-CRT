import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ModulusApproximation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitValue

/-! # Discrete harmonicity of projected exit expectations -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Expected projected boundary value for a walk started at a vertex. -/
noncomputable def projectedExitVertexValue (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (a : ℤ) : ℝ :=
  ∫ x, ψ (ballRetraction z r (vertexPoint ε η
    (vExitPosition (interiorCellVertices ε η (ball z r)) x))) ∂srwLaw m a

/-- The projected extension is the exit expectation at the selected vertex. -/
theorem projectedDiscreteHarmonicExtension_eq_vertexValue {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (ε : ℝ) (ω : Ω) (x : ℂ) :
    projectedDiscreteHarmonicExtension S r z ψ ε ω x =
      projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ
        (vertexOf ε (S.η ω) x) := rfl

/-- The exit expectation inherits a uniform bound from the boundary data. -/
theorem abs_projectedExitVertexValue_le (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {K : ℝ}
    (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K) (a : ℤ) :
    |projectedExitVertexValue m ε η r z ψ a| ≤ K := by
  have h := abs_integral_sub_le_of_uniform_bound (srwLaw m a)
    (f := fun x => ψ (ballRetraction z r (vertexPoint ε η
      (vExitPosition (interiorCellVertices ε η (ball z r)) x))))
    (g := fun _ => 0) (K := K) (L := 0) (δ := K)
    ((measurable_of_countable fun b : ℤ => ψ (ballRetraction z r
      (vertexPoint ε η b))).comp (measurable_vExitPosition _)) measurable_const
    (fun x => hψ _ (ballRetraction_mem z hr _)) (by simp)
    (fun x => by simpa using hψ _ (ballRetraction_mem z hr _))
  simpa [projectedExitVertexValue] using h

/-- The projected exit expectation is discrete harmonic whenever the walk
exits the interior vertex set almost surely. -/
theorem matedLaplacian_projectedExitVertexValue (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (ε : ℝ) (η : ℝ → ℂ) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (ψ : ℂ → ℝ) {K : ℝ} (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K)
    (hA : ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z r)) x ≠ ⊤)
    {a : ℤ} (ha : a ∈ interiorCellVertices ε η (ball z r)) (hdeg : mdeg m a ≠ 0) :
    matedLaplacian m (projectedExitVertexValue m ε η r z ψ) a = 0 := by
  have h := mLaplacian_integral_exitValue hlf hA ha hdeg
    (g := fun b => ψ (ballRetraction z r (vertexPoint ε η b)))
    (fun b => hψ _ (ballRetraction_mem z hr _))
  exact h

/-- At vertices outside the interior, the exit expectation is the boundary value. -/
theorem projectedExitVertexValue_of_not_mem (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) {a : ℤ}
    (ha : a ∉ interiorCellVertices ε η (ball z r)) :
    projectedExitVertexValue m ε η r z ψ a =
      ψ (ballRetraction z r (vertexPoint ε η a)) := by
  unfold projectedExitVertexValue
  have heq : ∀ᵐ x ∂srwLaw m a,
      vExitPosition (interiorCellVertices ε η (ball z r)) x = a := by
    filter_upwards [srwLaw_ae_start m a] with x hx
    unfold vExitPosition
    rw [vExitTime_eq_zero_of_not_mem (by rw [hx]; exact ha)]
    simpa using hx
  calc
    _ = ∫ _x, ψ (ballRetraction z r (vertexPoint ε η a)) ∂srwLaw m a :=
      integral_congr_ae (heq.mono fun _ hx => by rw [hx])
    _ = _ := by simp

/-- Hölder control of the retracted data transfers to boundary-cell values. -/
theorem projectedExitVertexValue_boundary_holder (m : ℤ → ℤ → ℕ) (ε : ℝ)
    (η : ℝ → ℂ) (r R : ℝ) (z : ℂ) (ψ : ℂ → ℝ) {C χ : ℝ≥0}
    (hψ : HolderOnWith C χ (fun x => ψ (ballRetraction z r x)) (closedBall z R))
    {a b : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball z r)))
    (hb : b ∈ cellVertices ε η (frontier (ball z r)))
    (haR : vertexPoint ε η a ∈ closedBall z R)
    (hbR : vertexPoint ε η b ∈ closedBall z R) :
    edist (projectedExitVertexValue m ε η r z ψ a)
      (projectedExitVertexValue m ε η r z ψ b) ≤
      (C : ℝ≥0∞) * edist (vertexPoint ε η a) (vertexPoint ε η b) ^ (χ : ℝ) := by
  have ha' : a ∉ interiorCellVertices ε η (ball z r) := fun h => h.2 ha
  have hb' : b ∉ interiorCellVertices ε η (ball z r) := fun h => h.2 hb
  rw [projectedExitVertexValue_of_not_mem m ε η r z ψ ha',
    projectedExitVertexValue_of_not_mem m ε η r z ψ hb']
  exact hψ.edist_le haR hbR

/-- The boundary Hölder estimate in the real-distance form used by Lemma 3.2. -/
theorem projectedExitVertexValue_boundary_holder_real (m : ℤ → ℤ → ℕ) (ε : ℝ)
    (η : ℝ → ℂ) (r R : ℝ) (z : ℂ) (ψ : ℂ → ℝ) {C χ : ℝ≥0}
    (hψ : HolderOnWith C χ (fun x => ψ (ballRetraction z r x)) (closedBall z R))
    {a b : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball z r)))
    (hb : b ∈ cellVertices ε η (frontier (ball z r)))
    (haR : vertexPoint ε η a ∈ closedBall z R)
    (hbR : vertexPoint ε η b ∈ closedBall z R) :
    |projectedExitVertexValue m ε η r z ψ a -
      projectedExitVertexValue m ε η r z ψ b| ≤
      (C : ℝ) * dist (vertexPoint ε η a) (vertexPoint ε η b) ^ (χ : ℝ) := by
  have h := projectedExitVertexValue_boundary_holder m ε η r R z ψ hψ ha hb haR hbR
  rw [edist_dist, edist_dist,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg χ),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (by simpa [Real.dist_eq] using h)

/-- Boundary-cell values satisfy the mesh-scale Hölder hypothesis of Lemma 3.2. -/
theorem projectedExitVertexValue_boundary_holder_mesh (m : ℤ → ℤ → ℕ) (ε : ℝ)
    (η : ℝ → ℂ) (r R : ℝ) (z : ℂ) (ψ : ℂ → ℝ) {C χ : ℝ≥0}
    (hψ : HolderOnWith C χ (fun x => ψ (ballRetraction z r x)) (closedBall z R))
    {a b : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball z r)))
    (hb : b ∈ cellVertices ε η (frontier (ball z r)))
    (haR : vertexPoint ε η a ∈ closedBall z R)
    (hbR : vertexPoint ε η b ∈ closedBall z R) :
    |projectedExitVertexValue m ε η r z ψ a -
      projectedExitVertexValue m ε η r z ψ b| ≤
      (C : ℝ) * max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ (χ : ℝ) := by
  have h := projectedExitVertexValue_boundary_holder_real m ε η r R z ψ hψ ha hb haR hbR
  rw [dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (le_max_right _ _) χ.coe_nonneg) C.coe_nonneg)

end MatedCRT
