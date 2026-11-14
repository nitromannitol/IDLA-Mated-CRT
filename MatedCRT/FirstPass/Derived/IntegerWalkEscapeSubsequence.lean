import MatedCRT.FirstPass.Derived.AreaCellEscapeSubsequence

/-! # Escaping subsequences for integer-labelled walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- Almost every integer-labelled walk has a strictly increasing sequence of
  times at which its scaled embedded vertex has norm at least the sequence index. -/
theorem ae_exists_escape_subsequence_vertexPoint
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {s : ℝ} (hs : s ≠ 0) (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ k : ℕ,
        (k : ℝ) ≤ ‖s • Complex.orthonormalBasisOneI.repr (vertexPoint ε η (ξ (f k)))‖ := by
  let T : (ℕ → ℤ) → ℕ → (areaCellConfig h hε m).cells :=
    fun ξ n => euclideanCellEquiv h hε (ξ n)
  have hT : Measurable T :=
    Measurable.of_eval fun n => (measurable_of_countable (euclideanCellEquiv h hε)).comp
      (measurable_pi_apply n)
  have hmap := ae_exists_escape_subsequence_areaCellRepresentative h hε m hlf H hH hconn hs x
    ((srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map T) rfl
  filter_upwards [ae_of_ae_map hT.aemeasurable hmap] with ξ hξ
  obtain ⟨f, hf, hbound⟩ := hξ
  refine ⟨f, hf, fun k => ?_⟩
  simpa only [T, areaCellRepresentative_equiv] using hbound k

end MatedCRT
end
