import MatedCRT.FirstPass.Derived.UniformStartGoodSandwich
import MatedCRT.FirstPass.Derived.UniformStartGoodAssembly
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.ExitNull68

/-!
# Almost sure exit of the interpolated walk from a ball

For a valid environment `S` with `0 < γ < 2`, every `ε > 0`, and every `R`, `ρ`, almost surely in the environment
the interpolated embedded walk exits `ball 0 R` almost surely, from every vertex of the mated-CRT map `𝒢^ε`
(`finExit`, the hypothesis `hfin` of `exists_eps_uniformStart_bound`).

The deterministic input is that the set of vertices whose embedded position lies in a ball is finite
(`η` is continuous and proper, `cellVertices_finite_of_isCompact`), and that a nearest-neighbour walk on `ℤ` with
locally finite edge multiplicity and `m k (k+1) ≠ 0` leaves every finite set almost surely
(`ExitNull68.exit_null_of_finite`).  The interpolated walk at integer time `n` is the embedded walk at step `n`,
so leaving the finite set of vertices inside the ball forces the path to leave the ball.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

namespace UniformStartGood

variable {Ω : Type} [MeasurableSpace Ω]

/-- At an integer time `n` the interpolated walk is the embedded walk at step `n`. -/
theorem interpolatedWalk_natCast (ε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) (n : ℕ) :
    interpolatedWalk ε η 1 x (n : ℝ≥0) = vertexPoint ε η (x n) := by
  unfold interpolatedWalk
  simp

/-- **Deterministic exit.** If `η` is continuous and proper, `m` is locally finite and `m k (k+1) ≠ 0`, then
from every start the interpolated walk leaves `ball 0 R` almost surely. -/
theorem ae_pathExitTime_interpolatedWalk_ne_top {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hc : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) (R : ℝ) (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw m x), pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε η 1 ξ) ≠ ⊤ := by
  set A : Set ℤ := {k | vertexPoint ε η k ∈ ball (0 : ℂ) R} with hA
  have hAfin : A.Finite := by
    refine (cellVertices_finite_of_isCompact hc hp hε (isCompact_closedBall (0 : ℂ) R)).subset ?_
    intro k hk
    refine ⟨η (ε * k), ⟨⟨ε * k, ⟨?_, le_rfl⟩, rfl⟩, ?_⟩⟩
    · nlinarith
    · exact ball_subset_closedBall hk
  have h := ExitNull68.exit_null_of_finite hlf hsucc hAfin x
  rw [← compl_mem_ae_iff] at h
  filter_upwards [h] with ξ hξ
  have hex : ∃ n, ξ n ∉ A := by
    by_contra hno
    exact hξ (show vExitTime A ξ = ⊤ by simp [vExitTime, hno])
  obtain ⟨n, hn⟩ := hex
  have hle : pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε η 1 ξ) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
    refine sInf_le ⟨(n : ℝ≥0), rfl, ?_⟩
    rw [interpolatedWalk_natCast]
    exact hn
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle

/-- **Almost sure exit for a valid environment.** For `0 < γ < 2` and a valid `S`, for every `ε > 0` and every
`R`, `ρ`, almost every environment lies in `finExit`. -/
theorem ae_mem_finExit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) (R ρ : ℝ) :
    ∀ᵐ ω ∂S.P, ω ∈ finExit S ε R ρ := by
  filter_upwards [Uniform68Env.ae_envInputs hγ hγ2 hS] with ω ⟨hc, hp, hadj⟩
  obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hc hp hadj
  intro x _
  exact ae_pathExitTime_interpolatedWalk_ne_top hε hc hp hlf hsucc R x

/-- **Uniform-start bound without the exit hypothesis.** For `0 < γ < 2`, the hypothesis `hfin` of
`exists_eps_uniformStart_bound` holds, so only the reverse Fatou statement `hL4` and the almost-sure eventual
uniform-start statement `hpkg` at tolerance `κ / 2` remain. -/
theorem exists_eps_uniformStart_bound_of_gamma {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ}
    (hL4 : ∀ M : ℝ → Set Ω, (∀ ε : ℝ, 0 < ε → MeasurableSet (M ε)) →
      (∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
        ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ M (e n)) →
      ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P (M ε)ᶜ ≤ ENNReal.ofReal θ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpkg : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ (κ / 2))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.P (goodG S ε R ρ κ)ᶜ ≤ ENNReal.ofReal θ :=
  exists_eps_uniformStart_bound hS hL4 (fun _ hε => ae_mem_finExit hγ hγ2 hS hε R ρ) hκ hpkg hθ

end UniformStartGood

end MatedCRT
