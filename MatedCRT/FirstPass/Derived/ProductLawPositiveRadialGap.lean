import MatedCRT.FirstPass.Derived.ProductLawShiftedCellFiniteBall
import LatticeProb.Topology.PositiveRadialGap

/-! # Radial gaps under a product-law realization -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A positive-probability radial gap on the joint environment and walk realization. -/
theorem exists_jointEnvironment_originCellWalk_positiveRadialGap_of_product_law
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q ≪ volume) (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε)
    (S : Ξ → Ω) (T : Ξ → ℝ) (hS : Measurable S) (hT : Measurable T)
    (hlaw : R.map (fun ξ => (S ξ, T ξ)) = P.prod Q)
    {a b : ℝ} (hab : a < b) :
    ∃ (H : Ξ → CellConfig)
      (Z : Ξ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (E : Ξ → ReflectedGMS.Code.EnvGeneral),
      ∃ p q : ℚ, a < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < b ∧
      MeasurableSet {ξ | ∀ k : ℤ, Metric.infDist (0 : ReflectedGMS.Plane)
        (LatticeProb.shiftedCompactCell
          ((⟨Complex.orthonormalBasisOneI.repr,
            Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
          ε (T ξ / ε) k : Set ReflectedGMS.Plane) ≤ p ∨
        (q : ℝ) ≤ Metric.infDist (0 : ReflectedGMS.Plane)
        (LatticeProb.shiftedCompactCell
          ((⟨Complex.orthonormalBasisOneI.repr,
            Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
          ε (T ξ / ε) k : Set ReflectedGMS.Plane)} ∧
      0 < R {ξ | ∀ k : ℤ, Metric.infDist (0 : ReflectedGMS.Plane)
        (LatticeProb.shiftedCompactCell
          ((⟨Complex.orthonormalBasisOneI.repr,
            Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
          ε (T ξ / ε) k : Set ReflectedGMS.Plane) ≤ p ∨
        (q : ℝ) ≤ Metric.infDist (0 : ReflectedGMS.Plane)
        (LatticeProb.shiftedCompactCell
          ((⟨Complex.orthonormalBasisOneI.repr,
            Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S ξ)))
          ε (T ξ / ε) k : Set ReflectedGMS.Plane)} ∧
      Measurable Z ∧ Measurable E ∧
      R.map (fun p => ((E p).val, (Z p).2)) = R.map Z ∧
      (∃ Z₀ : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ),
        Measurable Z₀ ∧ (∀ ξ, Z ξ = Z₀ (S ξ, T ξ)) ∧
        R.map Z = (P.prod Q).map Z₀) ∧
      ∀ᵐ p ∂(R),
        ∃ (h : IsAreaParametrized ((cellModelOfCoupling D hγ).area (S p)) (η (S p)))
          (_hlf : IsLocallyFinite ε ⟨fun t => bm (S p) (t + (T p)),
            (bm (S p)).continuous.comp (by fun_prop)⟩),
          H p = shiftedAreaCellConfig h hε ((T p) / ε)
            (bmEdgeCount ε (fun t => (bm (S p) (t + (T p))).1)
              (fun t => (bm (S p) (t + (T p))).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected ∧
          (Z p).1 = (H p).code ∧ (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 ∧
          vertexOf ε (fun t => η (S p) (t + (T p))) 0 = 0 ∧
          (∀ K : Set ReflectedGMS.Plane, IsCompact K →
            {a : ℤ | (((LatticeProb.shiftedCompactCell
              ((⟨Complex.orthonormalBasisOneI.repr,
                Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S p)))
              ε ((T p) / ε) a) : Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite) ∧
          let M := bmEdgeCount ε (fun t => (bm (S p) (t + (T p))).1)
            (fun t => (bm (S p) (t + (T p))).2)
          let C := shiftedAreaCellConfig h hε ((T p) / ε) M
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε ((T p) / ε) a)
            ((srwLaw M a).map (fun path n =>
              shiftedEuclideanCellEquiv h hε ((T p) / ε) (path n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h hε ((T p) / ε)
              0) R →
            (Z p).2 = R.map (fun path =>
              interpPathCM (vertexPoint ε (fun t => η (S p) (t + (T p)))) m.coe_nonneg
                (fun n => (shiftedEuclideanCellEquiv h hε ((T p) / ε)).symm (path n))) := by
  obtain ⟨hR, hC, hfin⟩ :=
    product_law_shiftedCells_measurable_finite_ball
      D hγ hε m Q hQ hsupport S T hS hT hlaw
  let : IsProbabilityMeasure R := hR
  obtain ⟨H, Z, E, hZ, hE, hlawE, hZ₀, hevent⟩ :=
    exists_jointEnvironment_originCellWalk_compactIncidence_of_product_law
      D hγ hε m Q hQ hsupport S T hS hT hlaw
  let e : C(ℂ, ReflectedGMS.Plane) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  let C : ℤ → Ξ → TopologicalSpace.NonemptyCompacts ReflectedGMS.Plane :=
    fun k ξ => LatticeProb.shiftedCompactCell (e.comp (η (S ξ))) ε (T ξ / ε) k
  have hfinb : ∀ᵐ ξ ∂(R), {k | ((C k ξ : Set ReflectedGMS.Plane) ∩
      Metric.ball 0 b).Nonempty}.Finite := by
    filter_upwards [hfin] with ξ hξ
    exact hξ b
  obtain ⟨p, q, hp, hpq, hq, hm, hpos⟩ :=
    LatticeProb.exists_positive_measure_compactCell_radial_gap R C hC 0 hab hfinb
  exact ⟨H, Z, E, p, q, hp, hpq, hq, hm, hpos, hZ, hE, hlawE, hZ₀, hevent⟩

end MatedCRT
end
