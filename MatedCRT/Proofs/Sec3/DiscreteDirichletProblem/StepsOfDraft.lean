import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.Limit
import HarmonicBalls.Steps.Sec11.SubharmonicMaximum
import HarmonicBalls.Proofs.Sec5.BoundaryRightContinuity
import HarmonicBalls.Steps.Sec3.Basic
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds

/-!
# The interior and boundary steps of Lemma 3.5 from its Draft statement

The Draft Lemma 3.5 (`DiscreteDirichletProblemStmt`) gives a limit `f̄` of the rescaled discrete solutions, uniformly on
`cl(B_r(z))` in probability, which is continuous on `cl(B_r(z))`, has Laplacian `c₀ ψ μ_h` in `B_r(z)` and boundary
values `φ`. The continuum solution `dirichletLimit` has the same three properties (`dirichletLimitStep_of_volumeGrowth`),
and a continuous function on a closed disk is determined by its distributional Laplacian in the disk and its boundary
values (`eqOn_closedBall_of_hasLaplacian`: the difference is subharmonic together with its negative, so the maximum
principle applies). Hence `f̄ = dirichletLimit` almost surely, and the steps `DirichletInteriorStep` and
`DirichletBoundaryStep` follow from the Draft Lemma 3.5 and the volume growth (Lemma 2.7).

## Main statements

* `eqOn_closedBall_of_hasLaplacian`
* `tendstoUniformlyOnInProbability_dirichletLimit_of_draft`
* `dirichletInteriorStep_of_draft`, `dirichletBoundaryStep_of_draft`
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Laplacian
open scoped ENNReal

/-- **Uniqueness for the Dirichlet problem on a disk.** Two functions continuous on `cl(B_r(z))` with the same
distributional Laplacian `μpos - μneg` in `B_r(z)` and the same values on `∂B_r(z)` agree on `cl(B_r(z))`. -/
theorem eqOn_closedBall_of_hasLaplacian {f g : ℂ → ℝ} {μpos μneg : Measure ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall z r)) (hg : ContinuousOn g (closedBall z r))
    (hLf : _root_.HarmonicBalls.HasLaplacian f μpos μneg (ball z r))
    (hLg : _root_.HarmonicBalls.HasLaplacian g μpos μneg (ball z r))
    (hb : ∀ x ∈ sphere z r, f x = g x) : EqOn f g (closedBall z r) := by
  have key : ∀ {u v : ℂ → ℝ}, ContinuousOn u (closedBall z r) → ContinuousOn v (closedBall z r) →
      _root_.HarmonicBalls.HasLaplacian u μpos μneg (ball z r) →
      _root_.HarmonicBalls.HasLaplacian v μpos μneg (ball z r) →
      (∀ x ∈ sphere z r, u x = v x) → ∀ x ∈ closedBall z r, u x - v x ≤ 0 := by
    intro u v hu hv hLu hLv hbd
    have hsub : _root_.HarmonicBalls.IsSubharmonicOn (ball z r) (fun x => u x - v x) := by
      refine isSubharmonicOn_of_laplacianGE_zero isOpen_ball ((hu.sub hv).mono ball_subset_closedBall)
        ⟨hLu.1.sub hLv.1, fun φ hφ _ => ⟨integrable_zero_measure, ?_⟩⟩
      have i1 := integrable_mul_laplacian_of_test hLu.1 hφ
      have i2 := integrable_mul_laplacian_of_test hLv.1 hφ
      have e1 := (hLu.2 φ hφ).2.2
      have e2 := (hLv.2 φ hφ).2.2
      have h0 : ∫ x, (u x - v x) * Δ φ x = 0 := by
        simp_rw [sub_mul]
        rw [integral_sub i1 i2, e1, e2, sub_self]
      rw [h0, integral_zero_measure]
    obtain ⟨y, hy, hmax⟩ := hsub.exists_maximum_on_sphere hr (hu.sub hv)
    intro x hx
    have h := hmax x hx
    rw [hbd y hy, sub_self] at h
    exact h
  intro x hx
  have h1 := key hf hg hLf hLg hb x hx
  have h2 := key hg hf hLg hLf (fun y hy => (hb y hy).symm) x hx
  linarith

/-- **The rescaled discrete solutions converge to `dirichletLimit`** uniformly on `cl(B_r(z))` in probability, from the
Draft Lemma 3.5 and the volume growth (Lemma 2.7). -/
theorem tendstoUniformlyOnInProbability_dirichletLimit_of_draft {𝒮 : SpaceFillingSLEModel}
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h27 : VolumeGrowthStmt) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) → IsHolderContinuousOn ψ (ball z r) →
      (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
    ∀ F : ℝ → Ω → ℤ → ℝ,
      (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
        (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
          matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
        ∀ b ∈ cellVertices ε (S.η ω) (sphere z r), F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) →
      TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω))
        (dirichletLimit S r z ψ φ) (closedBall z r) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
  obtain ⟨fbar, hfbar, hconv⟩ := h35 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF
  have hlim := dirichletLimitStep_of_volumeGrowth 𝒮 h27 _root_.HarmonicBalls.greenPotentialHolderStmt_holds.{0}
    γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ
  have hae : ∀ᵐ ω ∂S.P, EqOn (fbar ω) (dirichletLimit S r z ψ φ ω) (closedBall z r) := by
    filter_upwards [hfbar, hlim] with ω h1 h2
    exact eqOn_closedBall_of_hasLaplacian hr h1.1 h2.1 h1.2.1 h2.2.1
      (fun x hx => (h1.2.2.1 x hx).trans (h2.2.2.1 x hx).symm)
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv δ hδ) (fun _ => zero_le)
    (fun ε => measure_mono_ae ?_)
  filter_upwards [hae] with ω hω hmem
  obtain ⟨x, hx, hxδ⟩ := hmem
  exact ⟨x, hx, by rw [hω hx]; exact hxδ⟩

/-- **Lemma 3.5, interior step**, from the Draft Lemma 3.5 and the volume growth (Lemma 2.7). -/
theorem dirichletInteriorStep_of_draft {𝒮 : SpaceFillingSLEModel} (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h27 : VolumeGrowthStmt) : DirichletInteriorStep 𝒮 := by
  intro _ _ _ _ _ _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF r' _ _ δ hδ
  have h := tendstoUniformlyOnInProbability_dirichletLimit_of_draft h35 h27 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
    ψ φ hψb hψh hφ F hF δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun ε => measure_mono ?_)
  rintro ω ⟨x, hx, hxδ⟩
  exact ⟨x, closedBall_subset_closedBall (by linarith) hx, hxδ⟩

/-- **Lemma 3.5, boundary step**, from the Draft Lemma 3.5 and the volume growth (Lemma 2.7). -/
theorem dirichletBoundaryStep_of_draft {𝒮 : SpaceFillingSLEModel} (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h27 : VolumeGrowthStmt) : DirichletBoundaryStep 𝒮 := by
  intro _ _ _ _ _ _ _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF δ hδ e he
  have h := tendstoUniformlyOnInProbability_dirichletLimit_of_draft h35 h27 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
    ψ φ hψb hψh hφ F hF δ hδ
  refine ⟨r / 2, half_pos hr, half_lt_self hr, ?_⟩
  filter_upwards [(tendsto_order.1 h).2 e he] with ε hε
  refine le_trans (measure_mono ?_) hε.le
  rintro ω ⟨x, hx, hxδ⟩
  exact ⟨x, hx.1, hxδ⟩

end MatedCRT
