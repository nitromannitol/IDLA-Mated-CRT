import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryProof
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate

/-! Scaled Hölder boundary data for projected Dirichlet solutions. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped NNReal

/-- Projected Hölder data satisfy the prepared boundary condition when the
marked boundary-cell points stay in a fixed bounded disk and the median has
the stated upper scaling bound. -/
theorem preparedHolderBoundary_of_projected_data
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {z : ℂ} {r R A : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hA : 0 < A)
    (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (ω : Ω) (φ : ℂ → ℝ)
    (hφ : IsHolderContinuousOn φ (closedBall z r))
    (hsimply : SimplyConnectedSpace (ball z r))
    (hE : ∀ n, 0 < E ω n)
    (hm : ∀ n, S.mε (E ω n) ≤ A / E ω n)
    (hrep : ∀ n b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
      vertexPoint (E ω n) (S.η ω) b ∈ closedBall z R)
    (hharm : ∀ n a, a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r) →
      matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0)
    (hbd : ∀ n b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
      u ω n b = S.mε (E ω n) * φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) b))) :
    PreparedHolderBoundary S (ball z r) E u ω := by
  obtain ⟨C, χ, hχ, hχ1, hhol⟩ := holder_ballRetraction hr hR z hφ
  refine ⟨hsimply, hharm, χ, A * ((C : ℝ) + 1), hχ, hχ1, by positivity, ?_⟩
  intro n a ha b hb
  have hdist := hhol.dist_le (hrep n a ha) (hrep n b hb)
  have hpow : dist (vertexPoint (E ω n) (S.η ω) a)
      (vertexPoint (E ω n) (S.η ω) b) ^ (χ : ℝ) ≤
      max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a -
        vertexPoint (E ω n) (S.η ω) b‖ ^ (χ : ℝ) := by
    apply Real.rpow_le_rpow dist_nonneg
    · simp [dist_eq_norm]
    · exact χ.coe_nonneg
  have hmod : |φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) a)) -
      φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) b))| ≤
      (C : ℝ) * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a -
        vertexPoint (E ω n) (S.η ω) b‖ ^ (χ : ℝ) := by
    rw [← Real.dist_eq]
    exact hdist.trans (mul_le_mul_of_nonneg_left hpow C.coe_nonneg)
  have hmed : 0 ≤ S.mε (E ω n) := medianOf_nonneg _
  have hpow0 : 0 ≤ max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a -
        vertexPoint (E ω n) (S.η ω) b‖ ^ (χ : ℝ) := Real.rpow_nonneg (le_trans (hE n).le (le_max_left _ _)) _
  rw [hbd n a ha, hbd n b hb, ← mul_sub, abs_mul, abs_of_nonneg hmed]
  calc
    _ ≤ (A / E ω n) * ((C : ℝ) * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a -
        vertexPoint (E ω n) (S.η ω) b‖ ^ (χ : ℝ)) :=
      mul_le_mul (hm n) hmod (abs_nonneg _) (div_nonneg hA.le (hE n).le)
    _ ≤ (A * ((C : ℝ) + 1) / E ω n) * max (E ω n)
        ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ (χ : ℝ) := by
      have : A / E ω n * (C : ℝ) ≤ A * ((C : ℝ) + 1) / E ω n := by
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right (hE n)).2
        nlinarith [C.coe_nonneg]
      nlinarith

/-- On the common prepared event, projected harmonic data satisfy the vertex
boundary modulus. All bounds are pathwise and may depend on the environment. -/
theorem ae_projected_harmonic_boundary_vertex_modulus
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r)) :
    ∀ᵐ ω ∂S.P, ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ)
      (C : Ω → ℝ) (φ : ℂ → ℝ) (R A : ℝ),
      (∀ n, E ω n ∈ range e) → Tendsto (E ω) atTop (𝓝 0) →
      (∀ n, 0 < E ω n) → 0 < C ω →
      (∀ n a, a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r) →
        |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) →
      (∀ n a, a ∈ cellVertices (E ω n) (S.η ω) (ball z r) →
        |u ω n a| ≤ C ω / E ω n) →
      IsHolderContinuousOn φ (closedBall z r) → 0 ≤ R → 0 < A →
      (∀ n, S.mε (E ω n) ≤ A / E ω n) →
      (∀ n b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
        vertexPoint (E ω n) (S.η ω) b ∈ closedBall z R) →
      (∀ n a, a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r) →
        matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) →
      (∀ n b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
        u ω n b = S.mε (E ω n) * φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) b))) →
      IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) (closure (ball z r)) := by
  filter_upwards [preparedBoundaryVertexModuliStep_of_holder hH γ hγ hγ2 ρ hρ hρ1 Ω S hS e he] with ω hω
  intro E u C φ R A hEr hE0 hE hC hlap hsize hφ hR hA hm hrep hharm hbd
  apply hω (fun _ => ball z r) (fun _ => ⟨hD, isOpen_ball, isConnected_ball hr⟩)
    E (fun _ => u) (fun _ => C) hEr hE0 ?_ 0
  · exact preparedHolderBoundary_of_projected_data S hr hR hA E u ω φ hφ hsimply
      hE hm hrep hharm hbd
  · intro j
    exact ⟨hC, hlap, hsize⟩

end MatedCRT

#print axioms MatedCRT.preparedHolderBoundary_of_projected_data

#print axioms MatedCRT.ae_projected_harmonic_boundary_vertex_modulus
