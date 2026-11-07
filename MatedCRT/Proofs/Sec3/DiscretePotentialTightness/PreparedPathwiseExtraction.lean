import MatedCRT.Draft.Section3Prepared

/-! Pathwise extraction for every subsequence on the common prepared event. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Prepared tightness supplies local compactness simultaneously for all
subsequences of a fixed measurable sequence with eventual pathwise bounds. -/
theorem preparedTightness_pathwise_local (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ C / e n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ v : ℂ → ℝ,
        ContinuousOn v D ∧ ∀ K : Set ℂ, IsCompact K → closure K ⊆ D →
          TendstoUniformlyOn (fun n => rescale (S.mε (e (φ (ψ (θ n)))))
            (e (φ (ψ (θ n)))) (S.η ω) (u ω (φ (ψ (θ n))))) v atTop K := by
  obtain ⟨φ, hφ, A, hA, hprep⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hA, hbound] with ω hω ⟨C, hC, hb⟩
  intro ψ hψ
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hb' : ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e (φ (ψ n))) (S.η ω) D,
        |matedLaplacian (S.mult (e (φ (ψ n))) ω) (u ω (φ (ψ n))) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e (φ (ψ n))) (S.η ω) D,
        |u ω (φ (ψ n)) a| ≤ C / e (φ (ψ n))) :=
    hφψ.tendsto_atTop.eventually hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb'
  let E : Ω → ℕ → ℝ := fun _ n => e (φ (ψ (n + N)))
  let U : ℕ → Ω → ℕ → ℤ → ℝ := fun _ ω n => u ω (φ (ψ (n + N)))
  have hadd : StrictMono (fun n : ℕ => n + N) := fun _ _ h => Nat.add_lt_add_right h N
  have hshift : StrictMono (fun n : ℕ => ψ (n + N)) := hψ.comp hadd
  obtain ⟨Φ, _, hΦ⟩ := hprep (fun _ => D) (fun _ => ⟨hD, hDo, hDc⟩)
    E U (fun _ _ => C) (fun _ => measurable_const)
    (fun _ n => ⟨ψ (n + N), rfl⟩)
    (fun _ => he0.comp (hφ.tendsto_atTop.comp hshift.tendsto_atTop))
    (fun _ n a => hu _ a) (fun _ => measurable_const)
  have hbounds : PreparedTightnessBounds S (fun _ => D) E U (fun _ _ => C) ω := by
    intro j
    refine ⟨hC, ?_, ?_⟩
    · intro n a ha
      exact (hN (n + N) (Nat.le_add_left N n)).1 a ha
    · intro n a ha
      exact (hN (n + N) (Nat.le_add_left N n)).2 a ha
  obtain ⟨hmono, hlim⟩ := hΦ ω hω hbounds
  obtain ⟨v, hv, hlocal, _⟩ := hlim 0
  refine ⟨fun n => Φ ω n + N, ?_, v, hv, ?_⟩
  · exact hadd.comp hmono
  · intro K hK hKD
    exact hlocal K hK hKD

/-- The pathwise extraction remains valid for data admitting almost-sure
environment-measurable versions at each mesh and vertex. -/
theorem preparedTightness_pathwise_local_ae (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ)
    (hu : ∀ n a, ∃ v : Ω → ℝ, Measurable[S.envSigma] v ∧
      ∀ᵐ ω ∂S.P, v ω = u ω n a)
    (hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ C / e n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ v : ℂ → ℝ,
        ContinuousOn v D ∧ ∀ K : Set ℂ, IsCompact K → closure K ⊆ D →
          TendstoUniformlyOn (fun n => rescale (S.mε (e (φ (ψ (θ n)))))
            (e (φ (ψ (θ n)))) (S.η ω) (u ω (φ (ψ (θ n))))) v atTop K := by
  classical
  choose v hvm hva using hu
  have hall : ∀ᵐ ω ∂S.P, ∀ n, (fun a => v n a ω) = u ω n := by
    filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun a => hva n a))] with ω hω
    intro n
    funext a
    exact hω n a
  have hb : ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        |matedLaplacian (S.mult (e n) ω) (fun a => v n a ω) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |v n a ω| ≤ C / e n) := by
    filter_upwards [hall, hbound] with ω hω hboundω
    have heval : ∀ n a, v n a ω = u ω n a := fun n a => congrFun (hω n) a
    simpa only [hω, heval] using hboundω
  obtain ⟨φ, hφ, hlocal⟩ := preparedTightness_pathwise_local 𝒮 h31 hγ hγ2 hρ hρ1
    S hS D hD hDo hDc e he he0 (fun ω n a => v n a ω) hvm hb
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hall, hlocal] with ω hω hlocalω
  intro ψ hψ
  obtain ⟨θ, hθ, w, hw, hwconv⟩ := hlocalω ψ hψ
  refine ⟨θ, hθ, w, hw, ?_⟩
  intro K hK hKD
  simpa only [hω] using hwconv K hK hKD

end MatedCRT
