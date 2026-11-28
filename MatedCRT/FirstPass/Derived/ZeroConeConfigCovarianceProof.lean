import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1

/-!
# The shifted zero-cone configuration as a covariant Borel function of field, curve and phase

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1)
assert that the configuration `H` of (3.1) is a measurable function of `(h, η̂, θ)` satisfying the coordinate-change
identity (3.2). The written argument builds such a Borel
version in two steps:

* (lines 9 and 11) the quantum-time curve is a Borel function `Q` of the field and the Lebesgue-parametrized curve,
  obtained by changing clocks with a field-to-area map with simultaneous coordinate covariance (Sheffield–Wang,
  arXiv:1605.06171, Theorem 1.1); under every positive similarity `T(w) = C w + z` the new quantum-time curve is
  `T⁻¹ ∘ η(τ_z + ·)`, `τ_z` the quantum time of the first visit to `z`;
* (lines 13 and 15) the weighted cells of a curve form a Borel code `K` of the curve which is covariant under positive
  similarities and integer time shifts on a set of curves carrying the curves `η(· + θ)`, and every realization of
  (3.1) is `K(η(· + θ))` (the conductances are determined by the ordered planar curve: GMS (1.2), Figure 7 and the proof
  of Proposition 2.2; Duplantier–Miller–Sheffield, arXiv:1409.7055, §8.2).

This file states these two steps as named hypotheses (`ZeroConeQuantumCurveCovariance`, `ZeroConeCellWeightCode`) and
proves `ZeroConeConfigCovariance` from them (`zeroConeConfigCovariance`): the code is `Cfg((h, e), θ) = K(Q(h, e)(· + θ))`;
after a change of coordinates the curve at the new phase `[θ − τ_z]` is `T⁻¹ ∘ Q(h, e)(· + θ + j)` for an integer `j`
(lines 9 and 15: "the normalized path at the new phase is exactly the original `p_{j+θ}` for `j = −⌊θ − τ_z⌋`"), and the
almost sure statements about the coupling pass to the product of the laws of the field and the curve through the
measurable version of the zero-cone field independent of the curve (`exists_zeroConeField_version_indepFun_igCurve`).
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-- The curve `t ↦ q(t + θ)`. -/
def curveTimeTranslate (θ : ℝ) (q : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => q (t + θ), by fun_prop⟩

@[simp]
theorem curveTimeTranslate_apply (θ : ℝ) (q : C(ℝ, ℂ)) (t : ℝ) :
    curveTimeTranslate θ q t = q (t + θ) := rfl

/-- The curve `t ↦ C⁻¹ (q(t) − z)`: the image of `q` under `ψ⁻¹` for the positive similarity `ψ(w) = C w + z`. -/
def curveSimilarityPullback (C : ℝ) (z : ℂ) (q : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => ((C⁻¹ : ℝ) : ℂ) * (q t - z), by fun_prop⟩

@[simp]
theorem curveSimilarityPullback_apply (C : ℝ) (z : ℂ) (q : C(ℝ, ℂ)) (t : ℝ) :
    curveSimilarityPullback C z q t = ((C⁻¹ : ℝ) : ℂ) * (q t - z) := rfl

/-- The time translate `(q, θ) ↦ q(· + θ)` is jointly measurable. -/
theorem measurable_curveTimeTranslate :
    Measurable fun p : C(ℝ, ℂ) × ℝ => curveTimeTranslate p.2 p.1 := by
  have hev : Measurable fun q : C(ℝ, ℂ) × ℝ => q.1 q.2 := continuous_eval.measurable
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  show Measurable ((fun q : C(ℝ, ℂ) × ℝ => q.1 q.2) ∘ fun p : C(ℝ, ℂ) × ℝ => (p.1, t + p.2))
  exact hev.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))

/-- The set of inputs `x` for which `qc(x)(· + θ) ∈ S` for almost every phase `θ` is measurable. -/
theorem measurableSet_ae_curveTimeTranslate_mem {α : Type*} [MeasurableSpace α] {qc : α → C(ℝ, ℂ)}
    (hqc : Measurable qc) {S : Set C(ℝ, ℂ)} (hS : MeasurableSet S) :
    MeasurableSet {x : α | ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc x) ∈ S} := by
  have hE : MeasurableSet {p : α × ℝ | curveTimeTranslate p.2 (qc p.1) ∉ S} :=
    (measurable_curveTimeTranslate.comp ((hqc.comp measurable_fst).prodMk measurable_snd) hS).compl
  have hm := measurable_measure_prodMk_left (ν := zeroConePhase) hE
  have heq : {x : α | ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc x) ∈ S} =
      (fun x => zeroConePhase (Prod.mk x ⁻¹' {p : α × ℝ | curveTimeTranslate p.2 (qc p.1) ∉ S})) ⁻¹'
        {0} := by
    ext x
    show (∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc x) ∈ S) ↔
      zeroConePhase {θ | curveTimeTranslate θ (qc x) ∉ S} = 0
    exact ae_iff
  rw [heq]
  exact hm (measurableSet_singleton 0)

/-- **Almost sure properties of a pair with a measurable independent version, in product form.** If `H` is a
measurable version of `x`, independent of the measurable `y`, and the measurable set `A` contains `(x, y)` almost
surely, then `(a, b) ∈ A` for almost every `a` (law of `x`) and almost every `b` (law of `y`). -/
theorem ae_ae_mem_of_indepFun_version {Ω' α β : Type*} [MeasurableSpace Ω'] [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure Ω'} [IsProbabilityMeasure μ] {x H : Ω' → α} {y : Ω' → β}
    (hH : Measurable H) (hy : Measurable y) (hHy : IndepFun H y μ) (hHx : H =ᵐ[μ] x)
    {A : Set (α × β)} (hA : MeasurableSet A) (hxy : ∀ᵐ ω ∂μ, (x ω, y ω) ∈ A) :
    ∀ᵐ a ∂μ.map x, ∀ᵐ b ∂μ.map y, (a, b) ∈ A := by
  have hjoint : μ.map (fun ω => (H ω, y ω)) = (μ.map H).prod (μ.map y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH.aemeasurable hy.aemeasurable).1 hHy
  have h1 : ∀ᵐ p ∂μ.map (fun ω => (H ω, y ω)), p ∈ A := by
    refine (ae_map_iff (hH.prodMk hy).aemeasurable hA).2 ?_
    filter_upwards [hxy, hHx] with ω h1 h2
    rw [h2]
    exact h1
  rw [hjoint] at h1
  rw [← Measure.map_congr hHx]
  exact Measure.ae_ae_of_ae_prod h1

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The quantum-time curve as a Borel function of the field and the curve, with the LQG coordinate change**
(the written argument: "For every such similarity the new quantum-time curve is
`η^T(t) = T⁻¹η(τ_z + t)`"; line 11: "Use the field-to-area map with simultaneous coordinate covariance and the signed
mass of `e([0, t])` (of `e([t, 0])` for negative `t`) to change clocks ... The compact images, mass evaluations and
inverse clock are Borel"; sources cited there: Sheffield–Wang, arXiv:1605.06171, Theorem 1.1; Miller–Sheffield,
Imaginary geometry IV, arXiv:1302.4738, (1.2) and §4.3; Gwynne–Miller–Sheffield, arXiv:1705.11161, §§2.2, 2.3.1, 2.5
and (3.1)). PENDING TRUTH CHECK.

There is a measurable map `qc` from (field, Lebesgue-parametrized curve) to curves (the curve reparametrized by the
quantum area of the field, rooted at time `0`) with `qc(h₀, ηL) = η₀` almost surely, such that for almost every `h`
(law of the zero-cone field), almost every `e` (law of `ηL`) and all `C > 0`, `z ∈ ℂ` there is a quantum time `τ`
with `qc(h(C · + z) + Q log C, ψ⁻¹ ∘ e re-rooted at z) = ψ⁻¹ ∘ qc(h, e)(· + τ)`, `ψ(w) = C w + z`. -/
def ZeroConeQuantumCurveCovariance (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ qc : Field × C(ℝ, ℂ) → C(ℝ, ℂ), Measurable qc ∧
    (∀ᵐ ω ∂P, qc (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) = η₀ ω) ∧
    ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      ∃ τ : ℝ, qc (lqgSimilarityField γ C z h, affineReroot z C 0 e) =
        curveSimilarityPullback C z (curveTimeTranslate τ (qc (h, e)))

/-- **The weighted cells of a curve as a Borel code covariant under positive similarities and integer time shifts**
(the written argument: the conductances of the cells of the curve on integer
intervals "are determined by the ordered planar curve" (GMS (1.2), Figure 7 and the proof of Proposition 2.2;
Duplantier–Miller–Sheffield, arXiv:1409.7055, §8.2), "In particular the contour pair at the clock of the zero cone in
the formal realization computes these very weights"; line 15: "Use the usual standard Borel codes of continuous paths
and locally finite configurations of compact cells with weights ... Its atom gives a Borel map `K(p)` ... Almost surely
the same version works at every integer `j`. Define the code at a general input by `η(θ) + d_θ K(p_θ)`"). PENDING TRUTH
CHECK.

There are a measurable `K : C(ℝ, ℂ) → GMSSpace` and a measurable set `S` of curves such that: for `q ∈ S`, every
integer `j` and all `C > 0`, `z ∈ ℂ`, `K(ψ⁻¹ ∘ q(· + j)) = C⁻¹ (K(q) − z)`, `ψ(w) = C w + z`; almost surely, for almost
every phase `θ`, the curve `η₀(· + θ)` lies in `S`; and every realization `F` of the configuration (3.1) is almost surely
`K(η₀(· + θ))`. -/
def ZeroConeCellWeightCode (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ (K : C(ℝ, ℂ) → GMSSpace) (S : Set C(ℝ, ℂ)), Measurable K ∧ MeasurableSet S ∧
    (∀ q ∈ S, ∀ j : ℤ, ∀ C : ℝ, ∀ hC : 0 < C, ∀ z : ℂ,
      IsSimilar C⁻¹ (Complex.orthonormalBasisOneI.repr z) (inv_pos.2 hC) (K q)
        (K (curveSimilarityPullback C z (curveTimeTranslate j q)))) ∧
    (∀ᵐ ω ∂P, ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (η₀ ω) ∈ S) ∧
    ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
      ∀ᵐ p ∂P.prod zeroConePhase, F p = K (curveTimeTranslate p.2 (η₀ p.1))

/-- **The configuration (3.1) as a measurable function of `(h, η̂, θ)` with the coordinate-change identity (3.2)**
(arXiv:1705.11161; the written argument), from the Borel
quantum-time curve with its LQG coordinate change and the covariant Borel code of the weighted cells. The code is
`Cfg((h, e), θ) = K(qc(h, e)(· + θ))` and the phase shift for `ψ(w) = C w + z` is `s = −τ`. -/
theorem zeroConeConfigCovariance (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hQ : ZeroConeQuantumCurveCovariance D hγ)
    (hK : ZeroConeCellWeightCode D hγ) : ZeroConeConfigCovariance D hγ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨qc, hqcm, hqca, hqcov⟩ := hQ
  obtain ⟨K, S, hKm, hSm, hKcov, hsupp, hlink⟩ := hK
  obtain ⟨H, hHm, hHind, hHeq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hηm : Measurable ηL := D.measurable_curves.1
  have hA := measurableSet_ae_curveTimeTranslate_mem hqcm hSm
  have hxy : ∀ᵐ ω ∂P, (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) ∈
      {x : Field × C(ℝ, ℂ) | ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc x) ∈ S} := by
    filter_upwards [hsupp, hqca] with ω h1 h2
    show ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω)) ∈ S
    rw [h2]
    exact h1
  have hsupp' := ae_ae_mem_of_indepFun_version hHm hηm hHind hHeq hA hxy
  refine ⟨fun x => K (curveTimeTranslate x.2 (qc x.1)),
    hKm.comp (measurable_curveTimeTranslate.comp ((hqcm.comp measurable_fst).prodMk measurable_snd)),
    ?_, ?_⟩
  · intro G F hF
    have h2 : ∀ᵐ p ∂P.prod zeroConePhase, qc (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1) = η₀ p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hqca
    filter_upwards [hlink G F hF, h2] with p hp1 hp2
    show F p = K (curveTimeTranslate p.2 (qc (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1)))
    rw [hp2]
    exact hp1
  · filter_upwards [hqcov, hsupp'] with h hh1 hh2
    filter_upwards [hh1, hh2] with e he1 he2
    intro C hC z
    obtain ⟨τ, hτ⟩ := he1 C hC z
    have he2' : ∀ᵐ θ ∂zeroConePhase, curveTimeTranslate θ (qc (h, e)) ∈ S := he2
    refine ⟨-τ, ?_⟩
    filter_upwards [he2'] with θ hθ
    have hk : toIcoMod (zero_lt_one' ℝ) 0 (θ + -τ) =
        θ + -τ - (toIcoDiv (zero_lt_one' ℝ) 0 (θ + -τ) : ℝ) := by
      rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, mul_one]
    have key : curveTimeTranslate (toIcoMod (zero_lt_one' ℝ) 0 (θ + -τ))
        (qc (lqgSimilarityField γ C z h, affineReroot z C 0 e)) =
        curveSimilarityPullback C z (curveTimeTranslate
          ((-toIcoDiv (zero_lt_one' ℝ) 0 (θ + -τ) : ℤ) : ℝ) (curveTimeTranslate θ (qc (h, e)))) := by
      rw [hτ]
      ext t
      simp only [curveTimeTranslate_apply, curveSimilarityPullback_apply]
      have harg : t + toIcoMod (zero_lt_one' ℝ) 0 (θ + -τ) + τ =
          t + ((-toIcoDiv (zero_lt_one' ℝ) 0 (θ + -τ) : ℤ) : ℝ) + θ := by
        rw [hk]
        push_cast
        ring
      rw [harg]
    show IsSimilar C⁻¹ (Complex.orthonormalBasisOneI.repr z) (inv_pos.2 hC)
      (K (curveTimeTranslate θ (qc (h, e))))
      (K (curveTimeTranslate (toIcoMod (zero_lt_one' ℝ) 0 (θ + -τ))
        (qc (lqgSimilarityField γ C z h, affineReroot z C 0 e))))
    rw [key]
    exact hKcov _ hθ _ C hC z

end Hypotheses

end MatedCRT
