import MatedCRT.Proofs.Sec4.SubsequentialConvergence.BoundaryGeometry

/-! Extension of Hölder estimates to the closed Euclidean ball. -/

namespace MatedCRT

open Metric Set Filter Topology MeasureTheory
open scoped NNReal

/-- A Hölder function on an open ball retains its estimate on the closed
ball whenever it is continuous there. -/
theorem holderOn_closedBall_of_continuousOn {ρ : ℝ} (hρ : 0 < ρ) {g : ℂ → ℝ}
    (hc : ContinuousOn g (closedBall 0 ρ))
    (ho : IsHolderContinuousOn g (ball 0 ρ)) :
    IsHolderContinuousOn g (closedBall 0 ρ) := by
  obtain ⟨C, χ, hχ, hχ1, hf⟩ := ho
  refine ⟨C, χ, hχ, hχ1, holderOnWith_of_dist_le ?_⟩
  intro x hx y hy
  have hcl : closedBall (0 : ℂ) ρ ⊆ closure (ball 0 ρ) :=
    subset_of_eq (closure_ball 0 hρ.ne').symm
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hcl hx)
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hcl hy)
  have hu' : Tendsto u atTop (𝓝[closedBall (0 : ℂ) ρ] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hux, Eventually.of_forall fun n => ball_subset_closedBall (hu n)⟩
  have hv' : Tendsto v atTop (𝓝[closedBall (0 : ℂ) ρ] y) :=
    tendsto_nhdsWithin_iff.2 ⟨hvy, Eventually.of_forall fun n => ball_subset_closedBall (hv n)⟩
  have hgu : Tendsto (fun n => g (u n)) atTop (𝓝 (g x)) := (hc x hx).tendsto.comp hu'
  have hgv : Tendsto (fun n => g (v n)) atTop (𝓝 (g y)) := (hc y hy).tendsto.comp hv'
  have hd : ∀ n, dist (g (u n)) (g (v n)) ≤ C * dist (u n) (v n) ^ (χ : ℝ) :=
    fun n => hf.dist_le (hu n) (hv n)
  have hR : Tendsto (fun n => C * dist (u n) (v n) ^ (χ : ℝ)) atTop
      (𝓝 (C * dist x y ^ (χ : ℝ))) :=
    ((hux.dist hvy).rpow_const (Or.inr (NNReal.coe_nonneg χ))).const_mul (C : ℝ)
  exact le_of_tendsto_of_tendsto (hgu.dist hgv) hR (Eventually.of_forall hd)

/-- For a fixed positive time, all local limits along further subsequences
have Hölder continuous zero extensions and converge uniformly on the closed ball. -/
theorem odometer_prepared_holder_uniform_fixed_time
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        IsHolderContinuousOn ((ball 0 ρ).indicator w) (closedBall 0 ρ) ∧
        TendstoUniformlyOn
          (fun n => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ n))) ω)
          ((ball 0 ρ).indicator w) atTop (closedBall 0 ρ) := by
  obtain ⟨φ, hφ, hi⟩ := odometer_prepared_pair_and_boundary_moduli
    𝒮 hm h47 h44 h218 hH h37 h217 h27 hγ hγ2 hρ hρ1 S hS t ht e he he0
  obtain ⟨θ, hθ, hc⟩ := odometer_prepared_continuous_uniform_boundary_holder
    𝒮 h37 h217 h27 hγ hγ2 hρ hρ1 S hS (e ∘ φ) (fun n => he _)
    (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hi, hc] with ω hi hc
  obtain ⟨ξ, A, C₁, q, Cm, R₁, C, B, χ, hξ, hA, hC₁, hq, hCm, hR₁, hC, hχ, hχ1, hi⟩ := hi
  obtain ⟨B', χ', hχ', hχ1', hc⟩ := hc
  intro ψ hψ w hw
  obtain ⟨hint, hdecay⟩ := hi (θ ∘ ψ) (hθ.comp hψ) w hw
  obtain ⟨hcontinuous, huniform, _⟩ := hc t ht ψ hψ w hw
  have hχreal : 0 < (χ : ℝ) := by exact_mod_cast hχ
  have hholder := holderOn_ball_of_interior_and_boundary_moduli hρ hR₁ hξ hA hC₁ hq hCm hC
    (NNReal.coe_nonneg B) hχreal hint hdecay
  obtain ⟨K, α, hα, hα1, hk⟩ := hholder
  have hext : IsHolderContinuousOn ((ball 0 ρ).indicator w) (ball 0 ρ) := by
    refine ⟨K, α, hα, hα1, holderOnWith_of_dist_le ?_⟩
    intro x hx y hy
    simpa only [indicator_of_mem hx, indicator_of_mem hy] using hk.dist_le hx hy
  exact ⟨holderOn_closedBall_of_continuousOn hρ hcontinuous hext, huniform⟩

end MatedCRT
