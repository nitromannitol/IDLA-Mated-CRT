import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CompactnessFromClipping
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeClipping
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMeasurable

/-! Random compactness from eventual bounds on normalized exit times. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- When the graph and cell sets are measurable for the chosen meshes,
eventual almost-sure bounds can be enforced everywhere by clipping. -/
theorem exit_compactness_of_eventual_bounds
    (𝒮 : SpaceFillingSLEModel) (h31 : DiscretePotentialTightnessStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hconn : IsConnected D)
    (hDtop : IsOpen D ∨ IsClosed D)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ D)
    (ε : ℕ → ℝ) (I : Ω → ℕ → ℕ)
    (hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hEpos : ∀ ω n, 0 < ε (I ω n))
    (hElim : ∀ ω, Tendsto (fun n => ε (I ω n)) atTop (𝓝 0))
    (hM : ∀ n j k, Measurable[S.envSigma] fun ω => S.mult (ε (I ω n)) ω j k)
    (hV : ∀ n, Measurable[S.envSigma] fun ω => cellVertices (ε (I ω n)) (S.η ω) D)
    (hW : ∀ n, Measurable[S.envSigma] fun ω => interiorCellVertices (ε (I ω n)) (S.η ω) D)
    (C : Ω → ℝ) (hCm : Measurable[S.envSigma] C) (hCpos : ∀ ω, 0 < C ω)
    (hbound : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε (I ω n)) (S.η ω) D,
        |matedLaplacian (S.mult (ε (I ω n)) ω)
          (normExitTime (S.mult (ε (I ω n)) ω)
            (interiorCellVertices (ε (I ω n)) (S.η ω) D)) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε (I ω n)) (S.η ω) D,
        |normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C ω / ε (I ω n))) :
    ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
      ContinuousOn u K ∧ TendstoUniformlyOn
        (fun k => rescale (S.mε (ε (I ω (φ k)))) (ε (I ω (φ k))) (S.η ω)
          (normExitTime (S.mult (ε (I ω (φ k))) ω)
            (interiorCellVertices (ε (I ω (φ k))) (S.η ω) D))) u atTop K := by
  let E : Ω → ℕ → ℝ := fun ω n => ε (I ω n)
  have hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n := by
    intro n
    exact (measurable_of_countable ε).comp (hI n)
  obtain ⟨u, hum, hue⟩ := hS.exists_envSigma_measurable_selected_normExitTime ε D hDtop I hI
  let M : ℕ → Ω → ℤ → ℤ → ℕ := fun n ω => S.mult (E ω n) ω
  let V : ℕ → Ω → Set ℤ := fun n ω => cellVertices (E ω n) (S.η ω) D
  let W : ℕ → Ω → Set ℤ := fun n ω => interiorCellVertices (E ω n) (S.η ω) D
  have hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ W n ω, |matedLaplacian (M n ω) (u ω n) a| ≤ C ω) ∧
      (∀ a ∈ V n ω, |u ω n a| ≤ C ω / E ω n) := by
    filter_upwards [hbound, hue] with ω hb hu
    filter_upwards [hb] with n hn
    have heq : u ω n = normExitTime (M n ω) (W n ω) := funext (hu n)
    simpa [heq, M, V, W, E] using hn
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      (∀ ω a, a ∈ W n ω → |matedLaplacian (M n ω) (v ω) a| ≤ C ω) ∧
      (∀ ω a, a ∈ V n ω → |v ω a| ≤ C ω / E ω n) ∧
      ∀ ω, (∀ a ∈ W n ω, |matedLaplacian (M n ω) (u ω n) a| ≤ C ω) →
        (∀ a ∈ V n ω, |u ω n a| ≤ C ω / E ω n) → v ω = u ω n := by
    intro n
    let : MeasurableSpace Ω := S.envSigma
    exact GreenEnvironment.exists_measurable_clipped_bounded_laplacian
      (M n) (hM n) (V n) (W n) (hV n) (hW n) (fun ω => u ω n) (hum n)
      C (fun ω => E ω n) hCm (hEm n) (fun ω => (hCpos ω).le) (fun ω => hEpos ω n)
  choose v hvm hlap hsize hv using hclip
  let v' : Ω → ℕ → ℤ → ℝ := fun ω n => v n ω
  have heq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      v' ω n = normExitTime (S.mult (E ω n) ω)
        (interiorCellVertices (E ω n) (S.η ω) D) := by
    filter_upwards [hgood, hue] with ω hg hu
    filter_upwards [hg] with n hn
    exact (hv n ω hn.1 hn.2).trans (funext (hu n))
  exact exit_compactness_of_admissible_approximations 𝒮 h31 hγ hγ2 hρ hρ1
    S hS D hD hconn K hK hKD E v' C hEm hEpos hElim hvm hCm hCpos
    (fun ω n a => hlap n ω a) (fun ω n a => hsize n ω a) heq

end MatedCRT
