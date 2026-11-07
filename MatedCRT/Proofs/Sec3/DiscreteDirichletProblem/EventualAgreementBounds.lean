import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.LocalVersionModulus
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EventualLocalBounds

/-! # Transfer of discrete bounds under eventual local agreement -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- On a disk, eventual agreement on cells meeting the disk transfers both
the Laplacian bound and the size bound to the measurable representative. -/
theorem MatedCRTEnv.IsValid.ae_eventual_bounds_of_local_agreement
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (F v : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ)
    (hEq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), v ω n a = F ω n a)
    (hb : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (ε n) ω) (F ω n) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), |F ω n a| ≤ C ω / ε n)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (ε n) ω) (v ω n) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), |v ω n a| ≤ C ω / ε n) := by
  filter_upwards [hEq, hb, hS.isAreaParametrized,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω heq hbound hη hadj
  filter_upwards [heq, hbound] with n hn hbn
  constructor
  · intro a ha
    rw [matedLaplacian_eq_of_eqOn_cellVertices hη.1 hr (hadj (ε n) (hε n)) hn ha]
    exact hbn.1 a ha
  · intro a ha
    rw [hn a ha]
    exact hbn.2 a ha

/-- Prepared compactness for bounded discrete fields follows from a measurable
representative whose local agreement holds eventually. -/
theorem MatedCRTEnv.IsValid.prepared_compactness_of_local_agreement
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (F v : Ω → ℕ → ℤ → ℝ) (hvm : ∀ n a, Measurable[S.envSigma] fun ω => v ω n a)
    (C : Ω → ℝ) (hCm : Measurable[S.envSigma] C) (hC : ∀ ω, 0 < C ω)
    (hEq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), v ω n a = F ω n a)
    (hb : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (ε n) ω) (F ω n) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), |F ω n a| ≤ C ω / ε n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ (I : Ω → ℕ → ℕ), (∀ n, Measurable[S.envSigma] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∃ Φ : Ω → ℕ → ℕ,
      (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ u : ℂ → ℝ, ContinuousOn u (ball z r) ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ ball z r →
          TendstoUniformlyOn (fun k =>
            rescale (S.mε (ε (φ (I ω (Φ ω k))))) (ε (φ (I ω (Φ ω k))))
              (S.η ω) (F ω (φ (I ω (Φ ω k))))) u atTop O := by
  obtain ⟨φ, hφ, hcompact⟩ :=
    GreenEnvironment.prepared_compactness_of_eventual_random_bounds_ae
      𝒮 h31 hγ hγ2 hρ hρ1 S hS (ball z r) hD isOpen_ball (isConnected_ball hr)
      ε hε hε0 v hvm C hCm hC
      (hS.ae_eventual_bounds_of_local_agreement hγ hγ2 hr ε hε F v C hEq hb)
  have hres : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      EqOn (rescale (S.mε (ε n)) (ε n) (S.η ω) (v ω n))
        (rescale (S.mε (ε n)) (ε n) (S.η ω) (F ω n)) (ball z r) := by
    filter_upwards [hEq, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω heq hη hp
    filter_upwards [heq] with n hn x hx
    have hcell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 (hε n) x
    have ha : vertexOf (ε n) (S.η ω) x ∈ cellVertices (ε n) (S.η ω) (ball z r) :=
      ⟨x, hcell, hx⟩
    simp only [rescale, hn _ ha]
  refine ⟨φ, hφ, ?_⟩
  intro I hIm hI
  obtain ⟨Φ, hΦm, hΦ⟩ := hcompact I hIm hI
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hres] with ω hω heq
  obtain ⟨hmono, u, hu, hconv⟩ := hω
  refine ⟨hmono, u, hu, ?_⟩
  intro O hO hOD
  have hIω : Tendsto (I ω) atTop atTop := tendsto_atTop_mono (hI ω) tendsto_id
  have hidx : Tendsto (fun k => φ (I ω (Φ ω k))) atTop atTop :=
    hφ.tendsto_atTop.comp (hIω.comp hmono.tendsto_atTop)
  apply (hconv O hO hOD).congr
  filter_upwards [hidx.eventually heq] with k hk x hx
  exact hk (hOD (subset_closure hx))

end MatedCRT
