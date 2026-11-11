import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedExitBoundary
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedExitBarrier

/-! Boundary decay from a continuous zero-boundary limit. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

/-- Uniform convergence to a continuous zero-boundary function gives
uniform boundary decay along the same sequence. -/
theorem boundary_decay_of_uniform_limit {z : ℂ} {r : ℝ} (hr : 0 < r)
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    (hg : ContinuousOn g (closedBall z r)) (hz : ∀ x ∈ sphere z r, g x = 0)
    (hconv : TendstoUniformlyOn f g atTop (closedBall z r)) :
    ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ → f n x ≤ k := by
  intro k hk
  obtain ⟨r', hr'0, hr'r, hsmall⟩ :=
    exists_boundary_layer_of_continuousOn hr hg hz (show 0 < k / 2 by positivity)
  refine ⟨(r - r') / 2, by linarith, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (k / 2) (by positivity)] with n hn
  intro x hx y hy hxy
  have hdist : dist x y ≤ (r - r') / 2 := by simpa [dist_eq_norm] using hxy
  have hyr : dist y z = r := mem_sphere.mp hy
  have htri := dist_triangle y x z
  have hxlayer : x ∈ closedBall z r \ closedBall z r' := by
    refine ⟨hx, ?_⟩
    rw [mem_closedBall, dist_comm y x] at *
    linarith
  have hs := hsmall x hxlayer
  have hd := hn x hx
  rw [Real.dist_eq] at hd
  rw [abs_sub_comm] at hd
  have hle := le_abs_self (f n x - g x)
  have hge := le_abs_self (g x)
  linarith

/-- A pointwise upper bound by functions with a continuous zero-boundary
uniform limit also yields boundary decay. -/
theorem boundary_decay_of_uniform_majorant {z : ℂ} {r : ℝ} (hr : 0 < r)
    (q f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    (hdom : ∀ᶠ n in atTop, ∀ x ∈ closedBall z r, q n x ≤ f n x)
    (hg : ContinuousOn g (closedBall z r)) (hz : ∀ x ∈ sphere z r, g x = 0)
    (hconv : TendstoUniformlyOn f g atTop (closedBall z r)) :
    ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ → q n x ≤ k := by
  intro k hk
  obtain ⟨δ, hδ, hbound⟩ := boundary_decay_of_uniform_limit hr f g hg hz hconv k hk
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hdom, hbound] with n hn hb x hx y hy hxy
  exact (hn x hx).trans (hb x hx y hy hxy)

/-- A uniformly convergent majorant with zero boundary values gives the
prepared exit-time barrier. This is an explicit sufficient hypothesis. -/
theorem preparedExitTimeBoundaryDecayStep_of_uniform_majorant
    (𝒮 : SpaceFillingSLEModel)
    (hlimit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
      ∃ (F : ℝ → Ω → ℂ → ℝ) (g : Ω → ℂ → ℝ),
        (∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ∀ x ∈ closedBall z r,
          rescale (S.mε ε) ε (S.η ω)
            (fun a => (expectedExitTime (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball z r)) a).toReal) x ≤ F ε ω x) ∧
        (∀ᵐ ω ∂S.P, ContinuousOn (g ω) (closedBall z r) ∧
          ∀ x ∈ sphere z r, g ω x = 0) ∧
        TendstoUniformlyOnInProbability S.P F g (closedBall z r)) :
    PreparedExitTimeBoundaryDecayStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hD e he ψ hψ
  obtain ⟨F, g, hdom, hg, hconv⟩ := hlimit γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hD
  have he0 : Tendsto e atTop (𝓝 0) := (isPolySummableScales_of_lt_half_pow he).tendsto_zero
  obtain ⟨φ, hφ, hφae⟩ := exists_ae_uniform_subsequence_random S.P (closedBall z r)
    F g hconv (e ∘ ψ) (fun n => (he _).1) (he0.comp hψ.tendsto_atTop)
  have hdomae : ∀ᵐ ω ∂S.P, ∀ n, ∀ x ∈ closedBall z r,
      rescale (S.mε (e (ψ (φ n)))) (e (ψ (φ n))) (S.η ω)
        (fun a => (expectedExitTime (S.mult (e (ψ (φ n))) ω)
          (interiorCellVertices (e (ψ (φ n))) (S.η ω) (ball z r)) a).toReal) x ≤
        F (e (ψ (φ n))) ω x := ae_all_iff.mpr fun n => hdom _ (he _).1
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hg, hφae, hdomae] with ω hgω hconvω hdomω
  simpa only [Function.comp_def, rescale] using
    boundary_decay_of_uniform_majorant hr _ _ (g ω) (Filter.Eventually.of_forall hdomω)
      hgω.1 hgω.2 hconvω

/-- Full-disk convergence of the ordinary normalized exit time to a
continuous zero-boundary limit implies the prepared boundary barrier.
This hypothesis is retained explicitly and is not derived from Lemma 3.5. -/
theorem preparedExitTimeBoundaryDecayStep_of_uniform_limit
    (𝒮 : SpaceFillingSLEModel)
    (hlimit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
      ∃ g : Ω → ℂ → ℝ,
        (∀ᵐ ω ∂S.P, ContinuousOn (g ω) (closedBall z r) ∧
          ∀ x ∈ sphere z r, g ω x = 0) ∧
        TendstoUniformlyOnInProbability S.P
          (fun ε ω => rescale (S.mε ε) ε (S.η ω)
            (fun a => (expectedExitTime (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball z r)) a).toReal)) g (closedBall z r)) :
    PreparedExitTimeBoundaryDecayStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hD e he ψ hψ
  obtain ⟨g, hg, hconv⟩ := hlimit γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hD
  have he0 : Tendsto e atTop (𝓝 0) := (isPolySummableScales_of_lt_half_pow he).tendsto_zero
  obtain ⟨φ, hφ, hφae⟩ := exists_ae_uniform_subsequence_random S.P (closedBall z r)
    (fun ε ω => rescale (S.mε ε) ε (S.η ω)
      (fun a => (expectedExitTime (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) (ball z r)) a).toReal)) g hconv
    (e ∘ ψ) (fun n => (he _).1) (he0.comp hψ.tendsto_atTop)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hg, hφae] with ω hgω hconvω
  simpa only [Function.comp_def, rescale] using
    boundary_decay_of_uniform_limit hr _ (g ω) hgω.1 hgω.2 hconvω

end MatedCRT

#print axioms MatedCRT.boundary_decay_of_uniform_limit
#print axioms MatedCRT.boundary_decay_of_uniform_majorant
#print axioms MatedCRT.preparedExitTimeBoundaryDecayStep_of_uniform_majorant
#print axioms MatedCRT.preparedExitTimeBoundaryDecayStep_of_uniform_limit
