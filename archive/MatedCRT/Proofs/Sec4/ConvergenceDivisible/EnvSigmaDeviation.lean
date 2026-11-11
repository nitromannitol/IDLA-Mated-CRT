import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaLeastSupersolution
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.DeviationMeasurable
import MatedCRT.Draft.Section4

/-! # Measurable uniform deviation events of the rescaled least supersolution

For a compact `K` and a function `V` continuous on `K`, the event `{∃ x ∈ K, δ < |w̄^ε_t(x) - V(x)|}` for the rescaled
mated least supersolution has a `σ(h, η)`-measurable version, equal almost surely. This is the least-supersolution
analogue of `MatedCRTEnv.IsValid.exists_envSigma_measurable_greenKernel_deviation`: the vertex values are the
envSigma versions of `MatedCRTEnv.IsValid.exists_envSigma_measurable_matedLeastSupersolution`, scaled by `mε⁻¹`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_rescaledLeastSupersolution_deviation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t : ℝ) (ht : 0 < t)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite)
    (K : Set ℂ) (hK : IsCompact K) (V : ℂ → ℝ) (hV : ContinuousOn V K) (δ : ℝ) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K, δ < |rescaledMatedLeastSupersolution S ρ t ε ω x - V x|) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  choose G hG hGa using fun a : ℤ =>
    hS.exists_envSigma_measurable_matedLeastSupersolution hγ hγ' hε ρ t ht a hlf
  have hGall : ∀ᵐ ω ∂S.P, ∀ a, G a ω = matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a :=
    ae_all_iff.mpr hGa
  let u : Ω → ℤ → ℝ := fun ω a => (S.mε ε)⁻¹ * G a ω
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a :=
    fun a => measurable_const.mul (hG a)
  have hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty := by
    intro k
    exact ⟨ε * (k - 1), le_rfl, mul_le_mul_of_nonneg_left (by linarith) hε.le⟩
  let A : Set Ω := {ω | ∃ N a : ℤ, ∃ q : ℚ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      (((q : ℝ) < u ω a ∧ ∃ x ∈ K ∩ V ⁻¹' Iic ((q : ℝ) - δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∨
        (u ω a < (q : ℝ) ∧ ∃ x ∈ K ∩ V ⁻¹' Ici ((q : ℝ) + δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j))}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    exact measurableSet_bounded_index_deviation η hηm u hum ε δ K hK V hV hI
  · filter_upwards [hη, hGall, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
      with ω hηω hGω harea hp
    have hfin := Tightness.cellVertices_finite harea.1 hp hε hK.isBounded
    obtain ⟨N, hN⟩ := hfin.bddBelow
    have hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j := by
      refine ⟨N, ?_⟩
      intro j hj x hx hcell
      have hjN : N ≤ j := hN ⟨x, by simpa [hηω] using hcell, hx⟩
      exact (not_lt_of_ge hjN) hj
    have hsel : ∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x) := by
      intro x hx
      rw [hηω]
      exact Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
    have hiff := bounded_index_deviation_iff (η ω) (u ω) ε δ K V hbound hsel
    change (∃ N a : ℤ, ∃ q : ℚ, _) ↔ _
    rw [← hiff]
    simp only [hηω, u, hGω, rescaledMatedLeastSupersolution, rescale]

end MatedCRT
