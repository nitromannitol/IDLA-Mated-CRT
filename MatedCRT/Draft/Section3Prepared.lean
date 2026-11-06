import MatedCRT.Draft.Section3

/-! Lemma 3.1 with the deterministic preparation and boundary scaling of
corrections [C10] and [C11], corrected paper lines 976–1014. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The pathwise bounds in Lemma 3.1 for a countable family of domains and data. -/
def PreparedTightnessBounds {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : ℕ → Set ℂ) (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (C : ℕ → Ω → ℝ) (ω : Ω) : Prop :=
  ∀ j, 0 < C j ω ∧
    (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (D j),
      |matedLaplacian (S.mult (E ω n) ω) (u j ω n) a| ≤ C j ω) ∧
    (∀ n, ∀ a ∈ cellVertices (E ω n) (S.η ω) (D j), |u j ω n a| ≤ C j ω / E ω n)

/-- The scaled boundary hypothesis (3.1) for one member of the family. -/
def PreparedHolderBoundary {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (ω : Ω) : Prop :=
  SimplyConnectedSpace D ∧
  (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
    matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
  ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n,
    ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D),
    ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
      |u ω n a - u ω n b| ≤ C' / E ω n *
        max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ

/-- The common subsequence converges locally in each domain, and uniformly on
its closure when the scaled harmonic boundary condition holds. -/
def PreparedTightnessLimit {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ)
    (Φ : Ω → ℕ → ℕ) (ω : Ω) : Prop :=
  ∃ v : ℂ → ℝ, ContinuousOn v D ∧
    (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
      TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k))
        (S.η ω) (u ω (Φ ω k))) v atTop O) ∧
    (PreparedHolderBoundary S D E u ω →
      TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k))
        (S.η ω) (u ω (Φ ω k))) v atTop (closure D))

/-- Lemma 3.1 [C10, C11]. Each deterministic input has a deterministic
thinning and one almost-sure event for all countable collections of domains
and admissible measurable data on any measurable sequence in the thinning. -/
def DiscretePotentialTightnessPreparedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ A) ∧
    ∀ (D : ℕ → Set ℂ), (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
    ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
      (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
      (∀ ω n, E ω n ∈ range (e ∘ φ)) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
      (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      (∀ j, Measurable[S.envSigma] (C j)) →
      ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
        ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω →
          StrictMono (Φ ω) ∧ ∀ j, PreparedTightnessLimit S (D j) E (u j) Φ ω

end MatedCRT
