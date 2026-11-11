import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S6r.Constants
import MatedCRT.FirstPass.S4S6c.HVolCutoff68

/-!
# Almost-sure cutoff premise of the pointwise `hVolC` and `hVolY`

The premise `hcut` of `hVolC_pw` and `hVolY_pw` (HVolFullPw68.lean) is, at one environment `ω`, the existence of a
radius `t > 0` below which the LQG volume `S.μ ω` satisfies the coefficient-one lower bound
`δ^β ≤ μ(B_δ(z))` for all `0 < δ < t` and all `z ∈ B_{1-δ}`. This file states that premise almost surely under
`S.P`, in the form the pointwise premise of `ShellPtPrem` takes under `∀ᵐ ω ∂S.P`, and proves it from the inputs
already in the swap: the cone field of `S.IsValid` (`IsConeField`) and the volume-growth input `VolumeGrowthStmt`
(Lemma 2.7, Draft/Section2.lean), through `Lemma68Cutoff.volume_lower_cutoff_ae` (HVolCutoff68.lean).

The cutoff is random: it depends on `ω` and is never claimed for every `ω`.
-/

namespace MatedCRT
namespace Lemma68HVolCutoffAe

open MeasureTheory Set Filter Metric

/-- **Almost-sure cutoff premise (Lemma 2.7 with Borel–Cantelli).** Let `S` be a mated-CRT environment
with `S.IsValid 𝒮 γ`, so that `S.μ ω` is the `γ`-LQG measure of the quantum cone `(S.hC, S.hcirc)`, and let
`β > (2+γ)²/2`. Given the volume-growth input `hVG : VolumeGrowthStmt`, almost surely under `S.P` there is `t > 0`
with `δ^β ≤ S.μ ω (B_δ(z))` for all `0 < δ < t` and all `z ∈ B_{1-δ}`. -/
theorem cutoff_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) (hVG : VolumeGrowthStmt) (hγ0 : 0 < γ) (hγ2 : γ < 2) {β : ℝ}
    (hβ : (2 + γ) ^ 2 / 2 < β) :
    ∀ᵐ ω ∂S.P, ∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ β) ≤ S.μ ω (ball z δ) :=
  Lemma68Cutoff.volume_lower_cutoff_ae hγ0 hγ2 hβ hVG Ω S.P S.hC S.hcirc S.μ
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩

/-- **The same premise at the volume exponent `K.βm`** of `hVolC_pw` and `hVolY_pw` (`K.hβ : (2+γ)²/2 < K.βm`). -/
theorem cutoff_ae_K {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) (hVG : VolumeGrowthStmt) (K : Lemma68Window.Constants68 γ ρ) :
    ∀ᵐ ω ∂S.P, ∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ K.βm) ≤ S.μ ω (ball z δ) :=
  cutoff_ae S hS hVG K.hγ0 K.hγ2 K.hβ

end Lemma68HVolCutoffAe
end MatedCRT

#print axioms MatedCRT.Lemma68HVolCutoffAe.cutoff_ae
#print axioms MatedCRT.Lemma68HVolCutoffAe.cutoff_ae_K
