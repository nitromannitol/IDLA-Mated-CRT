import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SequenceClipping
import MatedCRT.Steps.Sec3.DiscretePotentialTightness

/-! # Local compactness from eventually harmonic data -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory Topology Metric

/-- The corrected tightness theorem (Lemma 3.1, corrected) applies to data whose harmonicity and
size estimates hold eventually almost surely, along polynomially summable deterministic scales,
provided the graph and cell sets are measurable with respect to the field-and-curve
sigma-algebra. -/
theorem compactness_of_eventual_estimates (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (ε : ℕ → ℝ) (hεs : IsPolySummableScales ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hM : ∀ n j k, Measurable[S.envSigma] fun ω => S.mult (ε n) ω j k)
    (hV : ∀ n, Measurable[S.envSigma] fun ω => cellVertices (ε n) (S.η ω) D)
    (hW : ∀ n, Measurable[S.envSigma] fun ω => interiorCellVertices (ε n) (S.η ω) D)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
        matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (ε (Φ ω k))) (ε (Φ ω k))
            (S.η ω) (u ω (Φ ω k))) ubar atTop O := by
  classical
  have hε : ∀ n, 0 < ε n := hεs.1
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      (∀ ω a, a ∈ interiorCellVertices (ε n) (S.η ω) D →
        matedLaplacian (S.mult (ε n) ω) (v ω) a = 0) ∧
      (∀ ω a, a ∈ cellVertices (ε n) (S.η ω) D → |v ω a| ≤ K / ε n) ∧
      ∀ ω, (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
          matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) →
        (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n) →
          v ω = u ω n := by
    intro n
    let M : Ω → ℤ → ℤ → ℕ := fun ω => S.mult (ε n) ω
    let V : Ω → Set ℤ := fun ω => cellVertices (ε n) (S.η ω) D
    let W : Ω → Set ℤ := fun ω => interiorCellVertices (ε n) (S.η ω) D
    let : MeasurableSpace Ω := S.envSigma
    exact exists_measurable_clipped_harmonic
      M (hM n) V W (hV n) (hW n)
      (fun ω => u ω n) (hu n) K (ε n) hK.le (hε n)
  choose v hvm hvl hvb hve using hclip
  let U : Ω → ℕ → ℤ → ℝ := fun ω n => v n ω
  obtain ⟨Φ, hΦm, hΦ⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hDo hDc ε hεs
    (fun _ n => ε n) U (fun _ => K) (fun _ => measurable_const)
    (fun _ n => ⟨n, rfl⟩) (fun _ => hεlim) hvm measurable_const (fun _ => hK)
    (fun ω n a ha => by rw [hvl n ω a ha, abs_zero]; exact hK.le)
    (fun ω n a ha => hvb n ω a ha)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hgood] with ω hω hgoodω
  obtain ⟨hmono, ubar, hcont, hconv, -⟩ := hω
  refine ⟨hmono, ubar, hcont, ?_⟩
  intro O hOc hOD
  apply (hconv O hOc hOD).congr
  filter_upwards [hmono.tendsto_atTop.eventually hgoodω] with k hk
  have heq : U ω (Φ ω k) = u ω (Φ ω k) := hve (Φ ω k) ω hk.1 hk.2
  intro x hx
  rw [heq]

/-- Random-index form of `compactness_of_eventual_estimates`: along the random scales
`ε (I ω n)` (with `I` measurable and `I ω n ≥ n`), the corrected Lemma 3.1 gives a measurable random
subsequence and a continuous limit, for data whose harmonicity and size estimates hold eventually
almost surely along the deterministic scales `ε n`. -/
theorem compactness_of_eventual_estimates_random (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (ε : ℕ → ℝ) (hεs : IsPolySummableScales ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hM : ∀ n j k, Measurable[S.envSigma] fun ω => S.mult (ε n) ω j k)
    (hV : ∀ n, Measurable[S.envSigma] fun ω => cellVertices (ε n) (S.η ω) D)
    (hW : ∀ n, Measurable[S.envSigma] fun ω => interiorCellVertices (ε n) (S.η ω) D)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
        matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n))
    (I : Ω → ℕ → ℕ) (hIm : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hI : ∀ ω n, n ≤ I ω n) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (ε (I ω (Φ ω k)))) (ε (I ω (Φ ω k)))
            (S.η ω) (u ω (I ω (Φ ω k)))) ubar atTop O := by
  classical
  have hε : ∀ n, 0 < ε n := hεs.1
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      (∀ ω a, a ∈ interiorCellVertices (ε n) (S.η ω) D →
        matedLaplacian (S.mult (ε n) ω) (v ω) a = 0) ∧
      (∀ ω a, a ∈ cellVertices (ε n) (S.η ω) D → |v ω a| ≤ K / ε n) ∧
      ∀ ω, (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
          matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) →
        (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n) →
          v ω = u ω n := by
    intro n
    let M : Ω → ℤ → ℤ → ℕ := fun ω => S.mult (ε n) ω
    let V : Ω → Set ℤ := fun ω => cellVertices (ε n) (S.η ω) D
    let W : Ω → Set ℤ := fun ω => interiorCellVertices (ε n) (S.η ω) D
    let : MeasurableSpace Ω := S.envSigma
    exact exists_measurable_clipped_harmonic
      M (hM n) V W (hV n) (hW n)
      (fun ω => u ω n) (hu n) K (ε n) hK.le (hε n)
  choose v hvm hvl hvb hve using hclip
  let E : Ω → ℕ → ℝ := fun ω n => ε (I ω n)
  let U : Ω → ℕ → ℤ → ℝ := fun ω n => v (I ω n) ω
  have hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n := by
    intro n
    let : MeasurableSpace Ω := S.envSigma
    exact (measurable_from_nat (f := ε)).comp (hIm n)
  have hUm : ∀ n a, Measurable[S.envSigma] fun ω => U ω n a := by
    intro n a
    let : MeasurableSpace Ω := S.envSigma
    have h1 : Measurable fun p : Ω × ℕ => v p.2 p.1 a :=
      measurable_from_prod_countable_left fun m => hvm m a
    exact h1.comp (measurable_id.prodMk (hIm n))
  have hItends : ∀ ω, Tendsto (I ω) atTop atTop := fun ω =>
    tendsto_atTop_mono (hI ω) tendsto_id
  obtain ⟨Φ, hΦm, hΦ⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hDo hDc ε hεs
    E U (fun _ => K) hEm (fun ω n => ⟨I ω n, rfl⟩) (fun ω => hεlim.comp (hItends ω))
    hUm measurable_const (fun _ => hK)
    (fun ω n a ha => by
      show |matedLaplacian (S.mult (ε (I ω n)) ω) (v (I ω n) ω) a| ≤ K
      rw [hvl (I ω n) ω a ha, abs_zero]; exact hK.le)
    (fun ω n a ha => hvb (I ω n) ω a ha)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hgood] with ω hω hgoodω
  obtain ⟨hmono, ubar, hcont, hconv, -⟩ := hω
  refine ⟨hmono, ubar, hcont, ?_⟩
  intro O hOc hOD
  apply (hconv O hOc hOD).congr
  have hIΦ : Tendsto (fun k => I ω (Φ ω k)) atTop atTop :=
    (hItends ω).comp hmono.tendsto_atTop
  filter_upwards [hIΦ.eventually hgoodω] with k hk
  have heq : U ω (Φ ω k) = u ω (I ω (Φ ω k)) := hve (I ω (Φ ω k)) ω hk.1 hk.2
  intro x hx
  show rescale (S.mε (ε (I ω (Φ ω k)))) (ε (I ω (Φ ω k))) (S.η ω) (U ω (Φ ω k)) x = _
  rw [heq]

end MatedCRT.GreenEnvironment
