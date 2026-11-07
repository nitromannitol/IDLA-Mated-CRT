import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedSpatialModulus

/-! Prepared boundary moduli with eventual pathwise hypotheses. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- A finite initial segment does not affect vertex asymptotic equicontinuity. -/
theorem vertex_asymptotic_equicontinuity_of_shift
    {ε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ} {K : Set ℂ} (N : ℕ)
    (h : IsVertexAsymptoticallyEquicontinuous (fun n => ε (n + N)) η
      (fun n => u (n + N)) K) : IsVertexAsymptoticallyEquicontinuous ε η u K := by
  intro k hk
  obtain ⟨δ, hδ, hev⟩ := h k hk
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨δ, hδ, eventually_atTop.2 ⟨M + N, ?_⟩⟩
  intro n hn
  have hsub : M ≤ n - N := by omega
  have hsum : n - N + N = n := by omega
  simpa only [hsum] using hM (n - N) hsub

/-- On the common prepared event, the boundary vertex modulus remains valid
when the pathwise estimates and projected boundary conditions hold eventually. -/
theorem ae_eventual_projected_harmonic_boundary_vertex_modulus
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
      IsHolderContinuousOn φ (closedBall z r) → 0 ≤ R → 0 < A →
      (∀ᶠ n in atTop,
        (∀ a, a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r) →
          |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) ∧
        (∀ a, a ∈ cellVertices (E ω n) (S.η ω) (ball z r) →
          |u ω n a| ≤ C ω / E ω n) ∧
        S.mε (E ω n) ≤ A / E ω n ∧
        (∀ b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
          vertexPoint (E ω n) (S.η ω) b ∈ closedBall z R) ∧
        (∀ a, a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r) →
          matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
        (∀ b, b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)) →
          u ω n b = S.mε (E ω n) * φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) b)))) →
      IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) (closure (ball z r)) := by
  filter_upwards [ae_projected_harmonic_boundary_vertex_modulus hH hγ hγ2 hρ hρ1 S hS e he
    hr hD hsimply] with ω hω
  intro E u C φ R A hEr hE0 hE hC hφ hR hA hevent
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  apply vertex_asymptotic_equicontinuity_of_shift N
  apply hω (fun ω n => E ω (n + N)) (fun ω n => u ω (n + N)) C φ R A
    (fun n => hEr (n + N)) (hE0.comp (tendsto_add_atTop_nat N))
    (fun n => hE (n + N)) hC
  · exact fun n => (hN (n + N) (by omega)).1
  · exact fun n => (hN (n + N) (by omega)).2.1
  · exact hφ
  · exact hR
  · exact hA
  · exact fun n => (hN (n + N) (by omega)).2.2.1
  · exact fun n => (hN (n + N) (by omega)).2.2.2.1
  · exact fun n => (hN (n + N) (by omega)).2.2.2.2.1
  · exact fun n => (hN (n + N) (by omega)).2.2.2.2.2

/-- Projected harmonic functions with eventual size and boundary conditions
have a common-event spatial modulus on the closed disk. -/
theorem ae_eventual_projected_harmonic_spatial_modulus
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r)) :
    ∀ᵐ ω ∂S.P, ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ)
      (C : Ω → ℝ) (φ : ℂ → ℝ),
      (∀ n, E ω n ∈ range e) → Tendsto (E ω) atTop (𝓝 0) →
      (∀ n, 0 < E ω n) → 0 < C ω → IsHolderContinuousOn φ (closedBall z r) →
      (∀ᶠ n in atTop,
        (∀ a ∈ cellVertices (E ω n) (S.η ω) (ball z r), |u ω n a| ≤ C ω / E ω n) ∧
        (∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (ball z r),
          matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
        (∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier (ball z r)),
          u ω n b = S.mε (E ω n) * φ (ballRetraction z r (vertexPoint (E ω n) (S.η ω) b)))) →
      Tightness.IsAsymptoticallyEquicontinuousOn
        (fun n => rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u ω n)) (closedBall z r) := by
  obtain ⟨A, hA, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscaleε⟩ := hscale Ω S hS
  filter_upwards [ae_eventual_projected_harmonic_boundary_vertex_modulus hH hγ hγ2 hρ hρ1
    S hS e he hr hD hsimply, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hω hη hp
  intro E u C φ hEr hE0 hE hC hφ hdata
  have hbounded : Bornology.IsBounded (frontier (ball z r)) := by
    rw [frontier_ball z hr.ne']
    exact isBounded_sphere
  obtain ⟨ε₁, hε₁, hsmall⟩ := Tightness.exists_cell_near_vertexPoint hη.1 hp hbounded
    (show (0 : ℝ) < 1 by norm_num)
  have hrep : ∀ ε, 0 < ε → ε < ε₁ →
      ∀ b ∈ cellVertices ε (S.η ω) (frontier (ball z r)),
        vertexPoint ε (S.η ω) b ∈ closedBall z (r + 1) := by
    intro ε hε hεsmall b hb
    obtain ⟨q, hqcell, hqfront⟩ := hb
    have hnear := hsmall ε hε hεsmall b ⟨q, hqcell, hqfront⟩ q hqcell
    have hq : dist q z = r := by simpa only [frontier_ball z hr.ne', mem_sphere] using hqfront
    apply mem_closedBall.mpr
    have htri := dist_triangle (vertexPoint ε (S.η ω) b) q z
    have hnear' : dist q (vertexPoint ε (S.η ω) b) < 1 := by
      simpa only [dist_eq_norm] using hnear
    rw [dist_comm (vertexPoint ε (S.η ω) b) q, hq] at htri
    linarith
  have hvertex : IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω)
      (closure (ball z r)) := by
    apply hω E u C φ (r + 1) A hEr hE0 hE hC hφ (by linarith) (by linarith)
    filter_upwards [hdata, hE0.eventually (gt_mem_nhds hε₀),
      hE0.eventually (gt_mem_nhds hε₁)] with n hn hn₀ hn₁
    refine ⟨?_, hn.1, ?_, hrep (E ω n) (hE n) hn₁, hn.2.1, hn.2.2⟩
    · intro a ha
      rw [hn.2.1 a ha, abs_zero]
      exact hC.le
    · simpa [div_eq_mul_inv] using (hscaleε (E ω n) (hE n) hn₀).2
  exact projected_spatial_modulus_of_vertex_modulus hm hγ hγ2 S hS ω hr (E ω) (u ω)
    hη.1 hp hη.2.2.1 hE hE0 hvertex

end MatedCRT

#print axioms MatedCRT.vertex_asymptotic_equicontinuity_of_shift
#print axioms MatedCRT.ae_eventual_projected_harmonic_boundary_vertex_modulus
#print axioms MatedCRT.ae_eventual_projected_harmonic_spatial_modulus
