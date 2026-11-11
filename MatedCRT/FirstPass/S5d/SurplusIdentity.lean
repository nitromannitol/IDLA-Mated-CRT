import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian
import MatedCRT.Proofs.Sec5.LLowerBound.ApplyKernel
import MatedCRT.Proofs.Sec5.StoppedPoleFiniteComparison
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas

/-!
# The surplus identity on the discrete cluster

The surplus `v_ε = u^ε_t = w̃^ε_t + (t/ε) g^ε_{B_ρ}(0,·)` (`stoppedOdometer`, Defs/Sandpile.lean:93; referee §5.2)
satisfies `Δ v_ε = 1/deg - (t/(ε deg 0)) 1_{a=0}` on the discrete cluster `Λ̃^ε_t`, given the Laplacian identity
`Δ w̃^ε_t = 1/deg` on `Λ̃^ε_t` (paper Lemma 4.4 corrected, `DiscreteLaplacianBoundCorrectedStmt`, Draft/Section4.lean:162,
a.s.). This is the input `hv` of `surplus_sub_le_greenComb` (S5d/StoppedComparison.lean). The Green part uses
`mLaplacian_stoppedOdometer` (Sec7), reversibility `greenKernel_symm_pole`, and `mLaplacian_greenFn`.
-/

namespace MatedCRT

open Set

/-- **Surplus identity on the cluster**: if `Δ w̃ = 1/deg` at `a` (Lemma 4.4), then `Δ v_ε(a) = 1/deg(a) - (t/ε)
1_{a=0}/deg(0)` for `a` in the discrete cluster. -/
theorem mLaplacian_stoppedOdometer_on_cluster {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (ht : 0 < t) (hB : (ballInterior ε η ρ).Finite)
    (hcl : ∀ a ∈ matedDiscreteCluster m ε η ρ t,
      mLaplacian m (matedLeastSupersolution m ε η ρ t) a = (mdeg m a : ℝ)⁻¹)
    {a : ℤ} (ha : a ∈ matedDiscreteCluster m ε η ρ t) :
    mLaplacian m (stoppedOdometer m ε η ρ t) a
      = (mdeg m a : ℝ)⁻¹ - t / ε * (if a = 0 then (mdeg m 0 : ℝ)⁻¹ else 0) := by
  have haB : a ∈ ballInterior ε η ρ := matedDiscreteCluster_subset_ballInterior hε ht ha
  have hw : mLaplacian m (matedLeastSupersolution m ε η ρ t) a = (mdeg m a : ℝ)⁻¹ := hcl a ha
  have hfun : greenKernel m (ballInterior ε η ρ) 0 = fun b => (mdeg m 0 : ℝ)⁻¹ * greenFn m (ballInterior ε η ρ) b 0 := by
    funext b
    rw [greenKernel_symm_pole hsymm hlf hcons hB 0 b]
    unfold greenKernel
    ring
  have hG : mLaplacian m (greenKernel m (ballInterior ε η ρ) 0) a
      = (mdeg m 0 : ℝ)⁻¹ * -(if a = 0 then 1 else 0) := by
    have h := Tightness.mLaplacian_const_mul hlf ((mdeg m 0 : ℝ)⁻¹) (fun b => greenFn m (ballInterior ε η ρ) b 0) a
    rw [hfun, h, WalkPotential.mLaplacian_greenFn hlf hcons hB 0 a haB]
  rw [Sec7.mLaplacian_stoppedOdometer hε ht hlf a, hw, hG]
  split_ifs <;> ring

end MatedCRT
