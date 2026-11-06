import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SequenceClipping
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedSingleDomain
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaEdge

/-! Prepared local compactness for eventually harmonic data. -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory Topology Metric

/-- A deterministic thinning can be prepared before a measurable random
sequence of indices is selected, as in the proof of Lemma 3.3. -/
theorem prepared_compactness_of_eventual_estimates_random_ae (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        matedLaplacian (S.mult (e n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ K / e n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ (I : Ω → ℕ → ℕ), (∀ n, Measurable[S.envSigma] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∃ Φ : Ω → ℕ → ℕ,
      (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ v : ℂ → ℝ, ContinuousOn v D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (e (φ (I ω (Φ ω k))))) (e (φ (I ω (Φ ω k))))
            (S.η ω) (u ω (φ (I ω (Φ ω k))))) v atTop O := by
  classical
  obtain ⟨φ, hφ, hprep⟩ := preparedTightness_singleDomain 𝒮 h31 hγ hγ2 hρ hρ1 S hS e he he0
  refine ⟨φ, hφ, ?_⟩
  intro I hIm hI
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P,
        (∀ a, a ∈ interiorCellVertices (e (φ n)) (S.η ω) D →
          matedLaplacian (S.mult (e (φ n)) ω) (v ω) a = 0) ∧
        (∀ a, a ∈ cellVertices (e (φ n)) (S.η ω) D → |v ω a| ≤ K / e (φ n)) ∧
        ((∀ a ∈ interiorCellVertices (e (φ n)) (S.η ω) D,
            matedLaplacian (S.mult (e (φ n)) ω) (u ω (φ n)) a = 0) →
          (∀ a ∈ cellVertices (e (φ n)) (S.η ω) D, |u ω (φ n) a| ≤ K / e (φ n)) →
            v ω = u ω (φ n)) := by
    intro n
    choose M hMm hMa using fun j k => hS.exists_envSigma_measurable_mult (e (φ n)) j k
    obtain ⟨V, hVm, hVa⟩ := hS.exists_envSigma_measurable_cellVertices (e (φ n)) D (Or.inl hDo)
    obtain ⟨W, hWm, hWa⟩ := hS.exists_envSigma_measurable_interiorCellVertices (e (φ n)) D (Or.inl hDo)
    have hMall : ∀ᵐ ω ∂S.P, ∀ j k, M j k ω = S.mult (e (φ n)) ω j k :=
      ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hMa j k
    have hcm : ∃ v : Ω → ℤ → ℝ,
        (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
        (∀ ω a, a ∈ W ω → matedLaplacian (fun j k => M j k ω) (v ω) a = 0) ∧
        (∀ ω a, a ∈ V ω → |v ω a| ≤ K / e (φ n)) ∧
        ∀ ω, (∀ a ∈ W ω, matedLaplacian (fun j k => M j k ω) (u ω (φ n)) a = 0) →
          (∀ a ∈ V ω, |u ω (φ n) a| ≤ K / e (φ n)) → v ω = u ω (φ n) := by
      let : MeasurableSpace Ω := S.envSigma
      exact exists_measurable_clipped_harmonic (fun ω j k => M j k ω) hMm V W hVm hWm
        (fun ω => u ω (φ n)) (hu (φ n)) K (e (φ n)) hK.le (he (φ n))
    obtain ⟨v, hvm, hvl, hvb, hve⟩ := hcm
    refine ⟨v, hvm, ?_⟩
    filter_upwards [hMall, hVa, hWa] with ω hm hv hw
    have hm' : (fun j k => M j k ω) = S.mult (e (φ n)) ω := by funext j k; exact hm j k
    have hl := hvl ω
    have hb := hvb ω
    have heq := hve ω
    simp only [hm', hv, hw] at hl hb heq
    exact ⟨hl, hb, heq⟩
  choose v hvm hv using hclip
  have hvall : ∀ᵐ ω ∂S.P, ∀ n,
      (∀ a, a ∈ interiorCellVertices (e (φ n)) (S.η ω) D →
        matedLaplacian (S.mult (e (φ n)) ω) (v n ω) a = 0) ∧
      (∀ a, a ∈ cellVertices (e (φ n)) (S.η ω) D → |v n ω a| ≤ K / e (φ n)) ∧
      ((∀ a ∈ interiorCellVertices (e (φ n)) (S.η ω) D,
          matedLaplacian (S.mult (e (φ n)) ω) (u ω (φ n)) a = 0) →
        (∀ a ∈ cellVertices (e (φ n)) (S.η ω) D, |u ω (φ n) a| ≤ K / e (φ n)) →
          v n ω = u ω (φ n)) := ae_all_iff.mpr hv
  let E : Ω → ℕ → ℝ := fun ω n => e (φ (I ω n))
  let U : Ω → ℕ → ℤ → ℝ := fun ω n => v (I ω n) ω
  have hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n := by
    intro n
    let : MeasurableSpace Ω := S.envSigma
    exact (measurable_from_nat (f := e ∘ φ)).comp (hIm n)
  have hUm : ∀ n a, Measurable[S.envSigma] fun ω => U ω n a := by
    intro n a
    let : MeasurableSpace Ω := S.envSigma
    have hv : Measurable fun p : Ω × ℕ => v p.2 p.1 a :=
      measurable_from_prod_countable_left fun m => hvm m a
    exact hv.comp (measurable_id.prodMk (hIm n))
  have hItends : ∀ ω, Tendsto (I ω) atTop atTop := fun ω =>
    tendsto_atTop_mono (hI ω) tendsto_id
  have hb : ∀ᵐ ω ∂S.P, 0 < K ∧
      (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
        |matedLaplacian (S.mult (E ω n) ω) (U ω n) a| ≤ K) ∧
      (∀ n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |U ω n a| ≤ K / E ω n) := by
    filter_upwards [hvall] with ω hvω
    refine ⟨hK, ?_, ?_⟩
    · intro n a ha
      rw [(hvω (I ω n)).1 a ha, abs_zero]
      exact hK.le
    · exact fun n a ha => (hvω (I ω n)).2.1 a ha
  obtain ⟨Φ, hΦm, hΦ⟩ := hprep D hD hDo hDc E U (fun _ => K)
    hEm (fun ω n => ⟨I ω n, rfl⟩)
    (fun ω => he0.comp (hφ.tendsto_atTop.comp (hItends ω))) hUm measurable_const hb
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hgood, hvall] with ω hω hg hvω
  obtain ⟨hm, vbar, hvbar, hconv, _⟩ := hω
  refine ⟨hm, vbar, hvbar, ?_⟩
  intro O hO hOD
  apply (hconv O hO hOD).congr
  filter_upwards [(hφ.tendsto_atTop.comp ((hItends ω).comp hm.tendsto_atTop)).eventually hg] with k hk
  have heq : U ω (Φ ω k) = u ω (φ (I ω (Φ ω k))) :=
    (hvω (I ω (Φ ω k))).2.2 hk.1 hk.2
  intro x hx
  rw [heq]

end MatedCRT.GreenEnvironment
