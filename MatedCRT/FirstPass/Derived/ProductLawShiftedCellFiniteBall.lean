import MatedCRT.FirstPass.Derived.ProductLawCompactCellIncidence

/-! # Shifted compact-cell incidence in balls -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- The retained product-law space is a probability space and its shifted
compact cells are measurable, with finitely many labels meeting each fixed ball
almost surely. -/
theorem product_law_shiftedCells_measurable_finite_ball
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q ≪ volume) (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε)
    (S : Ξ → Ω) (T : Ξ → ℝ) (hS : Measurable S) (hT : Measurable T)
    (hlaw : R.map (fun ξ => (S ξ, T ξ)) = P.prod Q) :
    IsProbabilityMeasure R ∧
    (∀ k : ℤ, Measurable (fun ξ => LatticeProb.shiftedCompactCell
      ((⟨Complex.orthonormalBasisOneI.repr,
        Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
      ε (T ξ / ε) k)) ∧
    ∀ᵐ ξ ∂(R), ∀ b : ℝ, {k : ℤ | ((LatticeProb.shiftedCompactCell
      ((⟨Complex.orthonormalBasisOneI.repr,
        Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
      ε (T ξ / ε) k : Set ReflectedGMS.Plane) ∩ Metric.ball 0 b).Nonempty}.Finite := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hmap : IsProbabilityMeasure (R.map (fun ξ => (S ξ, T ξ))) := by
    rw [hlaw]
    infer_instance
  let : IsProbabilityMeasure (R.map (fun ξ => (S ξ, T ξ))) := hmap
  have hR : IsProbabilityMeasure R :=
    (Measure.isProbabilityMeasure_map_iff (hS.prodMk hT).aemeasurable).1 hmap
  refine ⟨hR, ?_, ?_⟩
  · intro k
    let e : C(ℂ, ReflectedGMS.Plane) :=
      ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
    exact (LatticeProb.continuous_shiftedCompactCell k).measurable.comp
      ((e.continuous_postcomp.measurable.comp (D.measurable_curves.2.1.comp hS)).prodMk
        (measurable_const.prodMk (hT.div_const ε)))
  · obtain ⟨H, Z, E, hZ, hE, hlawE, hZ₀, hevent⟩ :=
      exists_jointEnvironment_originCellWalk_compactIncidence_of_product_law
        D hγ hε m Q hQ hsupport S T hS hT hlaw
    filter_upwards [hevent] with ξ hξ
    obtain ⟨h, hlf, heq, hv, hl, hz, hg, he, hor, hcompact, hrest⟩ := hξ
    intro b
    have hf := hcompact (Metric.closedBall 0 b) (isCompact_closedBall 0 b)
    exact hf.subset (by
      intro k hk
      obtain ⟨x, hx, hxb⟩ := hk
      exact ⟨x, hx, Metric.ball_subset_closedBall hxb⟩)

end MatedCRT
end
