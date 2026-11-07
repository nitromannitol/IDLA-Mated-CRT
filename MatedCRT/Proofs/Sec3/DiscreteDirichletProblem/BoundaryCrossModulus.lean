import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryModulusReduction
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedBoundaryProbability
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.BoundaryGeometry

/-! From circle convergence and closed-disk moduli to a boundary layer. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped ENNReal

/-- Circle convergence, a discrete probability modulus and a continuum
probability modulus imply the boundary-layer estimate. -/
theorem boundary_layer_of_circle_convergence_and_boundary_modulus
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℝ → Ω → ℂ → ℝ) (v : Ω → ℂ → ℝ)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hcircle : TendstoUniformlyOnInProbability P u v (sphere z r))
    (hu : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ, 0 < d ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r,
        dist x y < d ∧ t < |u ε ω x - u ε ω y|} ≤ e)
    (hv : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ, 0 < d ∧
      P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
        dist x y < d ∧ t < |v ω x - v ω y|} ≤ e) :
    ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |u ε ω x - v ω x|} ≤ e := by
  intro δ hδ e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he4 : 0 < e / 2 / 2 := ENNReal.half_pos he2.ne'
  obtain ⟨du, hdu, hu⟩ := hu (δ / 3) (by positivity) (e / 2 / 2) he4
  obtain ⟨dv, hdv, hv⟩ := hv (δ / 3) (by positivity) (e / 2 / 2) he4
  let r' := max (r / 2) (r - min du dv / 2)
  have hr'0 : 0 < r' := (by linarith : 0 < r / 2).trans_le (le_max_left _ _)
  have hr'r : r' < r := max_lt (by linarith) (by have := lt_min hdu hdv; linarith)
  refine ⟨r', hr'0, hr'r, ?_⟩
  have hc := ENNReal.tendsto_nhds_zero.1 (hcircle (δ / 3) (by positivity)) (e / 2) he2
  filter_upwards [hu, hc] with ε hu hc
  calc
    _ ≤ P ({ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r,
        dist x y < du ∧ δ / 3 < |u ε ω x - u ε ω y|} ∪
      {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
        dist x y < dv ∧ δ / 3 < |v ω x - v ω y|}) +
        P {ω | ∃ y ∈ sphere z r, δ / 3 < |u ε ω y - v ω y|} := by
      calc
        _ ≤ P (({ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r,
            dist x y < du ∧ δ / 3 < |u ε ω x - u ε ω y|} ∪
          {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
            dist x y < dv ∧ δ / 3 < |v ω x - v ω y|}) ∪
          {ω | ∃ y ∈ sphere z r, δ / 3 < |u ε ω y - v ω y|}) := by
          apply measure_mono
          rintro ω ⟨x, hx, herr⟩
          have hxr : r' < dist x z := lt_of_not_ge hx.2
          have hxle : dist x z ≤ r := mem_closedBall.mp hx.1
          have hclose : r - dist x z < min du dv := by
            have hh := le_max_right (r / 2) (r - min du dv / 2)
            have hp := lt_min hdu hdv
            linarith
          have hy : ∃ y ∈ sphere z r, dist x y < min du dv := by
            by_cases hxs : x ∈ sphere z r
            · exact ⟨x, hxs, by simpa using lt_min hdu hdv⟩
            · have hxball : x - z ∈ ball (0 : ℂ) r := by
                rw [mem_ball, dist_zero_right, ← dist_eq_norm]
                have hne : dist x z ≠ r := fun he => hxs (mem_sphere.mpr he)
                exact lt_of_le_of_ne hxle hne
              obtain ⟨w, hw, hwd⟩ := exists_sphere_radial_distance hr (x - z) hxball
              refine ⟨w + z, ?_, ?_⟩
              · simpa [mem_sphere, dist_eq_norm] using hw
              · have heq : dist x (w + z) = dist (x - z) w := by
                  simp only [dist_eq_norm]
                  congr 1
                  ring
                rw [heq, hwd, ← dist_eq_norm]
                exact hclose
          obtain ⟨y, hys, hxy⟩ := hy
          have hyc := sphere_subset_closedBall hys
          have ht1 := abs_sub_le (u ε ω x) (u ε ω y) (v ω y)
          have ht2 := abs_sub_le (u ε ω x) (v ω y) (v ω x)
          by_cases h1 : δ / 3 < |u ε ω x - u ε ω y|
          · exact Or.inl (Or.inl ⟨x, hx.1, y, hys, hxy.trans_le (min_le_left _ _), h1⟩)
          · by_cases h2 : δ / 3 < |v ω x - v ω y|
            · exact Or.inl (Or.inr ⟨x, hx.1, y, hyc, hxy.trans_le (min_le_right _ _), h2⟩)
            · right
              refine ⟨y, hys, ?_⟩
              rw [abs_sub_comm (v ω y) (v ω x)] at ht2
              linarith [le_of_not_gt h1, le_of_not_gt h2]
        _ ≤ _ := measure_union_le _ _
    _ ≤ (e / 2 / 2 + e / 2 / 2) + e / 2 := add_le_add (le_trans (measure_union_le _ _) (add_le_add hu hv)) hc
    _ = e := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- For projected Dirichlet data, the boundary-layer estimate reduces to
equicontinuity between the disk and its boundary in probability. -/
theorem projectedDirichlet_boundary_of_boundary_modulus
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ) (hdata : ProjectedDirichletData S r z ψ φ F)
    (hmod : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ, 0 < d ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r,
        dist x y < d ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
          rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e) :
    ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
          dirichletLimit S r z ψ (fun y => φ (ballRetraction z r y)) ω x|} ≤ e := by
  have hbd := dirichletLimit_projected_ae_properties 𝒮 h27 hγ hγ2 hρ1 S hS hr hball
    ψ φ hdata.1 hdata.2.1 hdata.2.2.1
  have hcircle : TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω))
      (dirichletLimit S r z ψ (fun y => φ (ballRetraction z r y))) (sphere z r) := by
    intro t ht
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    have hc := ENNReal.tendsto_nhds_zero.1
      (projectedDirichlet_boundary_values_in_probability 𝒮 hm hγ hγ2 S hS hr ψ φ F hdata t ht) e he
    filter_upwards [hc] with ε hc
    calc
      _ ≤ S.P {ω | ∃ x ∈ sphere z r,
          t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - φ x|} := by
        apply measure_mono_ae
        filter_upwards [hbd] with ω hω
        rintro ⟨x, hx, hbig⟩
        exact ⟨x, hx, by simpa [hω.2.2.1 x hx] using hbig⟩
      _ ≤ e := hc
  apply boundary_layer_of_circle_convergence_and_boundary_modulus S.P _ _ hr hcircle hmod
  intro t ht e he
  exact projectedDirichletLimit_closedBall_modulus_of_volumeGrowth 𝒮 h27 hγ hγ2 hρ1
    S hS hr hball ψ φ hdata.1 hdata.2.1 hdata.2.2.1 ht he

/-- Boundary equicontinuity needed in Step 3 of Lemma 3.5,
corrected paper lines 1575–1605. -/
def ProjectedDirichletBoundaryModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ), ProjectedDirichletData S r z ψ φ F →
  ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ, 0 < d ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r,
      dist x y < d ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e

/-- A closed-disk modulus also controls pairs with one point on the boundary. -/
theorem projectedDirichletBoundaryModulusStep_of_closed_modulus
    (𝒮 : SpaceFillingSLEModel) (hmod : ProjectedDirichletClosedModulusStep 𝒮) :
    ProjectedDirichletBoundaryModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ F hdata t ht e he
  obtain ⟨d, hd, h⟩ := hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ F hdata t ht e he
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with ε hε
  exact (measure_mono (by
    rintro ω ⟨x, hx, y, hy, hxy, hbig⟩
    exact ⟨x, hx, y, sphere_subset_closedBall hy, hxy, hbig⟩)).trans hε

/-- Boundary equicontinuity supplies the projected boundary-layer step. -/
theorem projectedDirichletBoundaryStep_of_boundary_modulus
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (hmod : ProjectedDirichletBoundaryModulusStep 𝒮) : ProjectedDirichletBoundaryStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ F hdata
  exact projectedDirichlet_boundary_of_boundary_modulus 𝒮 h27 hm hγ hγ2 hρ1 S hS hr hball ψ φ F hdata
    (hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ F hdata)

end MatedCRT

#print axioms MatedCRT.boundary_layer_of_circle_convergence_and_boundary_modulus
#print axioms MatedCRT.projectedDirichletBoundaryStep_of_boundary_modulus

#print axioms MatedCRT.projectedDirichletBoundaryModulusStep_of_closed_modulus
