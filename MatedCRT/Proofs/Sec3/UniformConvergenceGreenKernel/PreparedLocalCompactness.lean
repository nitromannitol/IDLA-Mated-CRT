import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SequenceClipping
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedSingleDomain

/-! Prepared local compactness for eventually harmonic data. -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory Topology Metric

/-- A deterministic thinning can be prepared before applying eventual
harmonicity and size bounds, as in the proof of Lemma 3.3. -/
theorem prepared_compactness_of_eventual_estimates (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hM : ∀ n j k, Measurable[S.envSigma] fun ω => S.mult (e n) ω j k)
    (hV : ∀ n, Measurable[S.envSigma] fun ω => cellVertices (e n) (S.η ω) D)
    (hW : ∀ n, Measurable[S.envSigma] fun ω => interiorCellVertices (e n) (S.η ω) D)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        matedLaplacian (S.mult (e n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ K / e n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Φ : Ω → ℕ → ℕ,
      (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ v : ℂ → ℝ, ContinuousOn v D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (e (φ (Φ ω k)))) (e (φ (Φ ω k)))
            (S.η ω) (u ω (φ (Φ ω k)))) v atTop O := by
  classical
  obtain ⟨φ, hφ, hprep⟩ := preparedTightness_singleDomain 𝒮 h31 hγ hγ2 hρ hρ1 S hS e he he0
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      (∀ ω a, a ∈ interiorCellVertices (e (φ n)) (S.η ω) D →
        matedLaplacian (S.mult (e (φ n)) ω) (v ω) a = 0) ∧
      (∀ ω a, a ∈ cellVertices (e (φ n)) (S.η ω) D → |v ω a| ≤ K / e (φ n)) ∧
      ∀ ω, (∀ a ∈ interiorCellVertices (e (φ n)) (S.η ω) D,
          matedLaplacian (S.mult (e (φ n)) ω) (u ω (φ n)) a = 0) →
        (∀ a ∈ cellVertices (e (φ n)) (S.η ω) D, |u ω (φ n) a| ≤ K / e (φ n)) →
          v ω = u ω (φ n) := by
    intro n
    let M : Ω → ℤ → ℤ → ℕ := fun ω => S.mult (e (φ n)) ω
    let V : Ω → Set ℤ := fun ω => cellVertices (e (φ n)) (S.η ω) D
    let W : Ω → Set ℤ := fun ω => interiorCellVertices (e (φ n)) (S.η ω) D
    let : MeasurableSpace Ω := S.envSigma
    exact exists_measurable_clipped_harmonic M (hM (φ n)) V W (hV (φ n)) (hW (φ n))
      (fun ω => u ω (φ n)) (hu (φ n)) K (e (φ n)) hK.le (he (φ n))
  choose v hvm hvl hvb hve using hclip
  let E : Ω → ℕ → ℝ := fun _ n => e (φ n)
  let U : Ω → ℕ → ℤ → ℝ := fun ω n => v n ω
  have hb : ∀ᵐ ω ∂S.P, 0 < K ∧
      (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
        |matedLaplacian (S.mult (E ω n) ω) (U ω n) a| ≤ K) ∧
      (∀ n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |U ω n a| ≤ K / E ω n) := by
    filter_upwards with ω
    refine ⟨hK, ?_, ?_⟩
    · intro n a ha
      rw [hvl n ω a ha, abs_zero]
      exact hK.le
    · exact fun n a ha => hvb n ω a ha
  obtain ⟨Φ, hΦm, hΦ⟩ := hprep D hD hDo hDc E U (fun _ => K)
    (fun _ => measurable_const) (fun _ n => ⟨n, rfl⟩)
    (fun _ => he0.comp hφ.tendsto_atTop) hvm measurable_const hb
  refine ⟨φ, hφ, Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hgood] with ω hω hg
  obtain ⟨hm, vbar, hvbar, hconv, _⟩ := hω
  refine ⟨hm, vbar, hvbar, ?_⟩
  intro O hO hOD
  apply (hconv O hO hOD).congr
  filter_upwards [(hφ.tendsto_atTop.comp hm.tendsto_atTop).eventually hg] with k hk
  have heq : U ω (Φ ω k) = u ω (φ (Φ ω k)) := hve (Φ ω k) ω hk.1 hk.2
  intro x hx
  rw [heq]

end MatedCRT.GreenEnvironment
