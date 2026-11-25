import MatedCRT.FirstPass.Derived.ZeroConeFiniteExpectation
import MatedCRT.FirstPass.Derived.IGCurveScaleLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TInputs

/-!
# Ergodicity modulo scaling of the shifted zero-cone configuration from Lemma A.1

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1, paragraph "Ergodicity modulo scaling",
`notes/refs/1705.11161.txt` lines 1124-1196) derive the ergodicity modulo scaling of the cell configuration (3.1) from
Lemma A.1 there (lines 1952-1956: a bounded, non-negative, measurable functional of the `0`-quantum cone `h` which is
almost surely invariant under `h ↦ h(C · + z) + Q log C` for all `C > 0`, `z ∈ ℂ` is almost surely constant) and from
the whole-plane GFF analogue of Remark A.2 (lines 1958-1964), applied at lines 1188-1192 to the imaginary-geometry
field `h^IG` that generates the space-filling SLE `η̂`.

This file states these two inputs as one named hypothesis `ZeroConeLemmaA1` on the zero-cone field and the
imaginary-geometry field of a mating-of-trees coupling, and derives from it `ZeroConeTailTriviality`
(`zeroConeTailTriviality_of_lemmaA1`) following the printed paragraph:

* lines 1145-1172 (averaging over the phase `θ`): proved here (`zeroConePhase_preimage_eq_of_ae_toIcoMod`);
* lines 1173-1186 (averaging over `η̂`, Lemma A.1): proved here from `ZeroConeLemmaA1` and the law invariance of `η̂`
  (`ae_eq_const_of_jointInvariance`), together with the independence of `G'` and `h` (line 1187, first sentence,
  `indepFun_of_ae_const_section`);
* lines 1188-1193 (Remark A.2 through the imaginary-geometry coordinate change of the coupling): proved here;
* lines 1193-1194 (independence of `G` from `(h, h^IG)`): proved here (`indepFun_of_ae_const_section`).

The steps of the paragraph that the coupling does not supply are separate named hypotheses, each citing its lines:
`ZeroConeConfigCovariance` (lines 1127-1137: the configuration is a measurable function of `(h, η̂, θ)` satisfying the
coordinate-change identity (3.2)), `SpaceFillingSLESimilarityLaw` (lines 1182-1183: the law of `η̂` is scale and
translation invariant), `ZeroConeCurveFactorStep` (lines 1186-1187: `G'`, independent of `h`, is almost surely a
function of `η̂` alone) and `ZeroConePhaseFactorStep` (lines 1193-1196: the configuration functional, independent of
`(h, η̂)`, is almost surely constant).

`exists_zeroCone_config_gmsHypotheses_of_lemmaA1` is the assembly `exists_zeroCone_config_gmsHypotheses` with the tail
triviality replaced by these hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-- The field `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')` of the `0`-quantum cone of the coupling (circle-average
embedding). -/
def zeroConeFieldOf (γ : ℝ) {Ω : Type} (X₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Field :=
  coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))

/-- The LQG coordinate change of a field along `w ↦ C w + z`: `h(C · + z) + Q log C`. -/
def lqgSimilarityField (γ C : ℝ) (z : ℂ) (h : Field) : Field :=
  LQGMetric.addConst (LQGMetric.affineComp C z h) (MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log C)

/-- The circle-average process `(ρ, w) ↦ h^IG_ρ(w)` of the imaginary-geometry field `h^IG = hIG₀ + U` of the
coupling (the input of the curve map of `IsMatingOfTreesCoupling.igMap`). -/
def igCircleProcess {Ω : Type} (hIG₀ : Ω → Field) (U : Ω → ℝ) (ω : Ω) : ℝ → ℂ → ℝ :=
  fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω

/-- The mass of a set under a probability measure is at most `1`, in real form. -/
theorem toReal_measure_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s))
  rwa [ENNReal.toReal_one] at h

/-- The uniform law of the phase is invariant under `θ ↦ (θ + c) mod 1`. -/
theorem zeroConePhase_toIcoMod_preimage (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    zeroConePhase ((fun x => toIcoMod (zero_lt_one' ℝ) 0 (x + c)) ⁻¹' S) = zeroConePhase S := by
  have key : ∀ T : Set ℝ, zeroConePhase T = volume (Ico (0 : ℝ) 1 ∩ T) := by
    intro T
    rw [zeroConePhase, Measure.restrict_apply' measurableSet_Icc, inter_comm]
    exact measure_congr (ae_eq_set_inter Ico_ae_eq_Icc.symm (ae_eq_refl T))
  rw [key, key]
  exact LatticeProb.volume_Ico_inter_map (zero_lt_one' ℝ) hS c

/-- **Averaging over the phase** (arXiv:1705.11161, lines 1153-1170: `t ↦ [t − τ_z]` preserves the uniform law on
`[0, 1]`). If `f((θ + s) mod 1) = g(θ)` for almost every `θ`, then `f` and `g` have the same law under the uniform
phase. -/
theorem zeroConePhase_preimage_eq_of_ae_toIcoMod {f g : ℝ → ℝ} (hf : Measurable f) (s : ℝ)
    (hfg : ∀ᵐ θ ∂zeroConePhase, f (toIcoMod (zero_lt_one' ℝ) 0 (θ + s)) = g θ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    zeroConePhase (f ⁻¹' A) = zeroConePhase (g ⁻¹' A) := by
  rw [← zeroConePhase_toIcoMod_preimage s (hf hA)]
  refine measure_congr ?_
  filter_upwards [hfg] with θ hθ
  show (f (toIcoMod (zero_lt_one' ℝ) 0 (θ + s)) ∈ A) = (g θ ∈ A)
  rw [hθ]

/-- **Independence from almost surely constant section laws** (arXiv:1705.11161, line 1187, first sentence, and lines
1193-1194). If `x` and `y` are independent and, for every measurable `s`, the law of `G(a, y)` gives `s` a mass which
is almost surely (in `a`, under the law of `x`) a constant, then `G(x, y)` is independent of `x`. -/
theorem indepFun_of_ae_const_section {Ω' α β : Type*} [MeasurableSpace Ω'] [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure Ω'} [IsProbabilityMeasure μ] {x : Ω' → α} {y : Ω' → β}
    (hx : Measurable x) (hy : Measurable y) (hxy : IndepFun x y μ) {G : α × β → ℝ} (hG : Measurable G)
    (hc : ∀ s : Set ℝ, MeasurableSet s → ∃ c : ℝ≥0∞,
      ∀ᵐ a ∂μ.map x, μ.map y (Prod.mk a ⁻¹' (G ⁻¹' s)) = c) :
    IndepFun (fun ω => G (x ω, y ω)) x μ := by
  have hxP : IsProbabilityMeasure (μ.map x) :=
    (Measure.isProbabilityMeasure_map_iff hx.aemeasurable).2 inferInstance
  have hjoint : μ.map (fun ω => (x ω, y ω)) = (μ.map x).prod (μ.map y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).1 hxy
  have hxy' : Measurable fun ω => (x ω, y ω) := hx.prodMk hy
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  obtain ⟨c, hcae⟩ := hc s hs
  have hS : MeasurableSet (G ⁻¹' s) := hG hs
  have key : ∀ t' : Set α, MeasurableSet t' →
      μ ((fun ω => G (x ω, y ω)) ⁻¹' s ∩ x ⁻¹' t') = c * μ.map x t' := by
    intro t' ht'
    have hW : MeasurableSet (G ⁻¹' s ∩ Prod.fst ⁻¹' t') := hS.inter (measurable_fst ht')
    have h1 : (fun ω => G (x ω, y ω)) ⁻¹' s ∩ x ⁻¹' t' =
        (fun ω => (x ω, y ω)) ⁻¹' (G ⁻¹' s ∩ Prod.fst ⁻¹' t') := rfl
    rw [h1, ← Measure.map_apply hxy' hW, hjoint, Measure.prod_apply hW,
      ← lintegral_indicator_const ht']
    refine lintegral_congr_ae ?_
    filter_upwards [hcae] with a ha
    by_cases hat : a ∈ t'
    · have he : Prod.mk a ⁻¹' (G ⁻¹' s ∩ Prod.fst ⁻¹' t') = Prod.mk a ⁻¹' (G ⁻¹' s) := by
        ext b
        simp [hat]
      rw [he, ha, Set.indicator_of_mem hat]
    · have he : Prod.mk a ⁻¹' (G ⁻¹' s ∩ Prod.fst ⁻¹' t') = ∅ := by
        ext b
        simp [hat]
      rw [he, measure_empty, Set.indicator_of_notMem hat]
  have h2 := key univ MeasurableSet.univ
  rw [preimage_univ, inter_univ, measure_univ, mul_one] at h2
  rw [key t ht, h2, Measure.map_apply hx ht]

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Lemma A.1 and Remark A.2 of Gwynne–Miller–Sheffield, arXiv:1705.11161** (`notes/refs/1705.11161.txt`
lines 1952-1964, as used in the proof of Proposition 3.1, lines 1141-1142, 1186 and 1188-1192). PENDING TRUTH CHECK.

1. (Lemma A.1, lines 1952-1956.) Let `h` be the circle-average embedding of the `0`-quantum cone (the field
   `zeroConeFieldOf γ X₀ B₀ B₀'` of the coupling). Every bounded, non-negative, measurable functional `F` of `h` which
   is scale and translation invariant in the sense that, almost surely, `F(h(C · + z) + Q log C) = F(h)` for all
   `C > 0` and `z ∈ ℂ` (A.1), is almost surely equal to a deterministic constant.
2. (Remark A.2, lines 1958-1962, extended at lines 1188-1192 to the imaginary-geometry field.) The analogue for the
   whole-plane GFF `h^IG = hIG₀ + U` of the coupling (a whole-plane GFF modulo `2πχ`), seen through its circle-average
   process `igCircleProcess hIG₀ U`: every bounded, non-negative, measurable functional `F` of it which is invariant
   under replacing `h^IG` by `h^IG ∘ ψ`, `ψ(w) = z + C w` (`C > 0`, `z ∈ ℂ`; line 1189 writes `h^IG(C⁻¹ · + z)`), is
   almost surely constant. The invariance is required almost surely for each fixed `(C, z)`, the form in which the
   imaginary-geometry coordinate change of the coupling (`IsMatingOfTreesCoupling.igMap`) carries invariance of a
   functional of `η̂` to the field (lines 1188-1190). -/
def ZeroConeLemmaA1 (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  (∀ F : Field → ℝ, Measurable F → (∃ M : ℝ, ∀ h, F h ≤ M) → (∀ h, 0 ≤ F h) →
    (∀ᵐ ω ∂P, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      F (lqgSimilarityField γ C z (zeroConeFieldOf γ X₀ B₀ B₀' ω)) = F (zeroConeFieldOf γ X₀ B₀ B₀' ω)) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, F (zeroConeFieldOf γ X₀ B₀ B₀' ω) = c) ∧
  (∀ F : (ℝ → ℂ → ℝ) → ℝ, Measurable F → (∃ M : ℝ, ∀ K, F K ≤ M) → (∀ K, 0 ≤ F K) →
    (∀ C : ℝ, 0 < C → ∀ z : ℂ, ∀ᵐ ω ∂P,
      F (igPullback γ z C 0 (igCircleProcess hIG₀ U ω)) = F (igCircleProcess hIG₀ U ω)) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, F (igCircleProcess hIG₀ U ω) = c)

/-- **The configuration as a function of `(h, η̂, θ)` and the coordinate-change identity (3.2)**
(arXiv:1705.11161, lines 1127-1128: "By definition, `H` is a measurable function of `h`, `η̂`, and `θ`"; lines
1129-1137: (3.2), "by the definition of `H` and the LQG coordinate change formula"). There is a measurable `Cfg` such
that every realization `F` of the configuration (3.1) is almost surely `Cfg((h, η̂), θ)` (`η̂` represented by the
Lebesgue-parametrized curve `ηL`), and, for almost every `h` (law of the zero-cone field) and almost every `η̂` (law of
`ηL`), for all `C > 0` and `z ∈ ℂ` there is a phase shift `s` such that for almost every `θ` the configuration of
`(h(C · + z) + Q log C, ψ⁻¹ ∘ η̂ re-rooted at the hitting time of z, (θ + s) mod 1)`, `ψ(w) = C w + z`, is
`C⁻¹(H − z)` for `H` the configuration of `(h, η̂, θ)`. In the coupling the conductances of (3.1) are read from the
boundary-length pair `bm` (`IsZeroConeConfigRealization`), so the first clause is not a matter of definition here. -/
def ZeroConeConfigCovariance (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∃ Cfg : (Field × C(ℝ, ℂ)) × ℝ → GMSSpace, Measurable Cfg ∧
    (∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
      ∀ᵐ p ∂P.prod zeroConePhase, F p = Cfg ((zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1), p.2)) ∧
    ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, ∀ hC : 0 < C, ∀ z : ℂ,
      ∃ s : ℝ, ∀ᵐ θ ∂zeroConePhase,
        IsSimilar C⁻¹ (Complex.orthonormalBasisOneI.repr z) (inv_pos.2 hC) (Cfg ((h, e), θ))
          (Cfg ((lqgSimilarityField γ C z h, affineReroot z C 0 e), toIcoMod (zero_lt_one' ℝ) 0 (θ + s)))

/-- **Scale and translation invariance of the law of whole-plane space-filling SLE** (arXiv:1705.11161, lines
1182-1183: "Since the law of `η̂` is scale and translation invariant"). For all `C > 0` and `z ∈ ℂ`, the curve
`ψ⁻¹ ∘ ηL`, `ψ(w) = z + C w`, re-rooted at its hitting time of `z` and reparametrized by Lebesgue measure, has the law
of `ηL`. -/
def SpaceFillingSLESimilarityLaw (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ z : ℂ, IdentDistrib (fun ω => affineReroot z C 0 (ηL ω)) ηL P P

/-- **The step from `h` to `η̂`** (arXiv:1705.11161, lines 1186-1187: "so `G'` is independent from `h`. Therefore,
`G'` is a.s. equal to a measurable function of only `η̂`", where `G'` is invariant by (3.3), lines 1153-1172). Every
bounded measurable functional `G'` of `(h, η̂)` which is almost surely invariant under the joint coordinate change and
independent of `h` is almost surely `g(η̂)` for a measurable `g` which is almost surely invariant under each
`η̂ ↦ ψ⁻¹ ∘ η̂` (re-rooted), the invariance used at lines 1188-1192. -/
def ZeroConeCurveFactorStep (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G' : Field × C(ℝ, ℂ) → ℝ, Measurable G' → (∃ M : ℝ, ∀ x, |G' x| ≤ M) →
    (∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      G' (lqgSimilarityField γ C z h, affineReroot z C 0 e) = G' (h, e)) →
    IndepFun (fun ω => G' (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω)) (zeroConeFieldOf γ X₀ B₀ B₀') P →
    ∃ g : C(ℝ, ℂ) → ℝ, Measurable g ∧
      (∀ᵐ ω ∂P, G' (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) = g (ηL ω)) ∧
      ∀ C : ℝ, 0 < C → ∀ z : ℂ, ∀ᵐ ω ∂P, g (affineReroot z C 0 (ηL ω)) = g (ηL ω)

/-- **The step from `(h, η̂)` to `θ`** (arXiv:1705.11161, lines 1193-1196: "we infer that `G` is independent from `h`
and `h^IG`, so `G` is a.s. equal to a function of only `θ`. By (3.2), we have `G([θ − τ_z]) = G(θ)` for each `z ∈ ℂ`.
Since `[θ − τ_z]` ranges over all of `[0, 1]` as `z` ranges over `ℂ`, we get that `G` is a.s. equal to a
deterministic constant"). For every realization `F` of the configuration (3.1) and every bounded measurable
similarity-invariant `Φ`, if `Φ(F)` is independent of the pair (zero-cone field, `ηL`), then `Φ(F)` is almost surely
constant. -/
def ZeroConePhaseFactorStep (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
    ∀ Φ : GMSSpace → ℝ, Measurable Φ → (∃ M : ℝ, ∀ H, |Φ H| ≤ M) →
      (∀ (s : ℝ) (u) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' → Φ H' = Φ H) →
      IndepFun (fun p => Φ (F p)) (fun p => (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1))
        (P.prod zeroConePhase) →
      ∃ c : ℝ, ∀ᵐ p ∂P.prod zeroConePhase, Φ (F p) = c

/-- **A measurable version of the zero-cone field, independent of the curve.** The zero-cone field is almost surely
a measurable function of `X₀` and the continuous versions of `B₀, B₀'`, which are independent of `ηL` (a measurable
function of the imaginary-geometry data, `indep_curve`). -/
theorem exists_zeroConeField_version_indepFun_igCurve
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ H : Ω → Field, Measurable H ∧ IndepFun H ηL P ∧ H =ᵐ[P] zeroConeFieldOf γ X₀ B₀ B₀' := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀'
  let zeroData : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
    fun q => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2))
  have hzeroData : Measurable zeroData := by fun_prop
  have hXBB : IndepFun ηL (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    (MatedCRT.Sec1.indepFun_igCurve_cone D).comp measurable_id hzeroData
  have hpath : (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) =ᵐ[P]
      fun ω => (X₀ ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hXBc : IndepFun ηL (fun ω => (X₀ ω, (Bc ω, Bc' ω))) P :=
    MatedCRTHarmonic.IGLaw.indepFun_triple_continuousMap_of_coe (hXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ 0 (Bc ω, Bc' ω)
  have hWm : Measurable W := (ConeScaling.measurable_radMap γ 0).comp (hBcm.prodMk hBc'm)
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hHm : Measurable fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω) :=
    hF.comp (D.gff₀.measurable.prodMk hWm)
  have hηH : IndepFun ηL (fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)) P :=
    hXBc.comp measurable_id (hF.comp (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ 0).comp measurable_snd)))
  have hQ0 : 0 < CellScaling.lqgQ γ - 0 := by
    have hq := CellScaling.lqgQ_sub_pos hγ.1 hγ.2
    linarith [hγ.1]
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B₀.eval_zero_ae_eq_zero,
      D.bm_B₀'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B₀' hQ0]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B₀ s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B₀' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ 0 (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ 0 (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  refine ⟨_, hHm, hηH.symm, ?_⟩
  filter_upwards [hW] with ω hω
  show ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω) =
    coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  simp only [CellScaling.coneField, ConeScaling.fieldOf]
  have he : ConeScaling.radialOf (W ω) =
      (fun z : ℂ => CellScaling.coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω) (-Real.log ‖z‖)) := by
    funext z
    exact hω (-Real.log ‖z‖)
  rw [he]

/-- **Lines 1173-1192 of arXiv:1705.11161: a jointly invariant functional of `(h, η̂)` is almost surely constant.**
Let `G'` be a measurable functional of (zero-cone field, curve) with values in `[0, 1]`, almost surely invariant under
the joint coordinate change (3.3). For every measurable `B`, `G''(h) = P[G'(h, η̂) ∈ B]` is invariant under the
coordinate change of `h` (law invariance of `η̂`, lines 1179-1185), hence almost surely constant by Lemma A.1 (line
1186); so `G'(h, η̂)` is independent of `h` (line 1187), almost surely `g(η̂)` by `ZeroConeCurveFactorStep`, and
`g(η̂)` is almost surely constant by Remark A.2 through the imaginary-geometry coordinate change (lines 1188-1193). -/
theorem ae_eq_const_of_jointInvariance
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hA1 : ZeroConeLemmaA1 D hγ) (hlaw : SpaceFillingSLESimilarityLaw D hγ)
    (hcurve : ZeroConeCurveFactorStep D hγ)
    {G' : Field × C(ℝ, ℂ) → ℝ} (hG'm : Measurable G') (hG'01 : ∀ x, 0 ≤ G' x ∧ G' x ≤ 1)
    (hG'inv : ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      G' (lqgSimilarityField γ C z h, affineReroot z C 0 e) = G' (h, e)) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, G' (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω) = c := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H', hH'm, hH'ind, hH'eq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hηm : Measurable ηL := D.measurable_curves.1
  have hνP : IsProbabilityMeasure (P.map ηL) :=
    (Measure.isProbabilityMeasure_map_iff hηm.aemeasurable).2 inferInstance
  have hh₀ : AEMeasurable (zeroConeFieldOf γ X₀ B₀ B₀') P := hH'm.aemeasurable.congr hH'eq
  have hlaw₀ : P.map H' = P.map (zeroConeFieldOf γ X₀ B₀ B₀') := Measure.map_congr hH'eq
  -- the section masses are almost surely constant (Lemma A.1)
  have hsec : ∀ s : Set ℝ, MeasurableSet s → ∃ c : ℝ≥0∞,
      ∀ᵐ h ∂P.map H', P.map ηL (Prod.mk h ⁻¹' (G' ⁻¹' s)) = c := by
    intro s hs
    have hS : MeasurableSet (G' ⁻¹' s) := hG'm hs
    let L : Field → ℝ := fun h => (P.map ηL (Prod.mk h ⁻¹' (G' ⁻¹' s))).toReal
    have hLm : Measurable L := (measurable_measure_prodMk_left hS).ennreal_toReal
    have hLb : ∀ h, L h ≤ 1 := fun h => toReal_measure_le_one (P.map ηL) _
    have hL0 : ∀ h, 0 ≤ L h := fun _ => ENNReal.toReal_nonneg
    have hLinv : ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ C : ℝ, 0 < C → ∀ z : ℂ,
        L (lqgSimilarityField γ C z h) = L h := by
      filter_upwards [hG'inv] with h hh C hC z
      have hω : ∀ᵐ ω ∂P, G' (lqgSimilarityField γ C z h, affineReroot z C 0 (ηL ω)) = G' (h, ηL ω) :=
        (ae_of_ae_map hηm.aemeasurable hh).mono fun ω hω => hω C hC z
      have hE : MeasurableSet (Prod.mk (lqgSimilarityField γ C z h) ⁻¹' (G' ⁻¹' s)) :=
        measurable_prodMk_left hS
      show (P.map ηL (Prod.mk (lqgSimilarityField γ C z h) ⁻¹' (G' ⁻¹' s))).toReal =
        (P.map ηL (Prod.mk h ⁻¹' (G' ⁻¹' s))).toReal
      rw [Measure.map_apply hηm hE, Measure.map_apply hηm (measurable_prodMk_left hS),
        ← (hlaw C hC z).measure_mem_eq hE]
      refine congrArg ENNReal.toReal (measure_congr ?_)
      filter_upwards [hω] with ω hω'
      show (G' (lqgSimilarityField γ C z h, affineReroot z C 0 (ηL ω)) ∈ s) = (G' (h, ηL ω) ∈ s)
      rw [hω']
    obtain ⟨c, hc⟩ := hA1.1 L hLm ⟨1, hLb⟩ hL0 (ae_of_ae_map hh₀ hLinv)
    refine ⟨ENNReal.ofReal c, ?_⟩
    rw [hlaw₀]
    have hcL : ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), L h = c :=
      (ae_map_iff hh₀ (measurableSet_eq_fun hLm measurable_const)).2 hc
    filter_upwards [hcL] with h hh
    rw [← hh, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- `G'(h, η̂)` is independent of `h` (line 1187)
  have hind : IndepFun (fun ω => G' (H' ω, ηL ω)) H' P :=
    indepFun_of_ae_const_section hH'm hηm hH'ind hG'm hsec
  have hind' : IndepFun (fun ω => G' (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω))
      (zeroConeFieldOf γ X₀ B₀ B₀') P :=
    hind.congr (hH'eq.mono fun ω hω => by simp only [hω]) hH'eq
  obtain ⟨g, hgm, hgae, hginv⟩ := hcurve G' hG'm
    ⟨1, fun x => abs_le.2 ⟨by linarith [(hG'01 x).1], (hG'01 x).2⟩⟩ hG'inv hind'
  -- Remark A.2 through the imaginary-geometry coordinate change (lines 1188-1193)
  obtain ⟨Φig, hΦm, -, hrep, hcc, -⟩ := D.igMap
  let gc : C(ℝ, ℂ) → ℝ := fun e => max 0 (min 1 (g e))
  have hgcm : Measurable gc := measurable_const.max (measurable_const.min hgm)
  have hinvIG : ∀ C : ℝ, 0 < C → ∀ z : ℂ, ∀ᵐ ω ∂P,
      gc (Φig (igPullback γ z C 0 (igCircleProcess hIG₀ U ω))) = gc (Φig (igCircleProcess hIG₀ U ω)) := by
    intro C hC z
    filter_upwards [hcc z C 0 hC, hrep, hginv C hC z] with ω h1 h2 h3
    show gc (Φig (igPullback γ z C 0 (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω))) =
      gc (Φig (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω))
    rw [h1, ← h2]
    show max 0 (min 1 (g (affineReroot z C 0 (ηL ω)))) = max 0 (min 1 (g (ηL ω)))
    rw [h3]
  obtain ⟨c, hc⟩ := hA1.2 (fun K => gc (Φig K)) (hgcm.comp hΦm)
    ⟨1, fun _ => max_le zero_le_one (min_le_left _ _)⟩ (fun _ => le_max_left _ _) hinvIG
  refine ⟨c, ?_⟩
  filter_upwards [hc, hrep, hgae] with ω h1 h2 h3
  have h1' : gc (ηL ω) = c := by
    rw [h2]
    exact h1
  have h01 := hG'01 (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω)
  rw [h3] at h01 ⊢
  rw [← h1']
  show g (ηL ω) = max 0 (min 1 (g (ηL ω)))
  rw [min_eq_right h01.2, max_eq_right h01.1]

/-- **Ergodicity modulo scaling of the shifted zero-cone configuration from Lemma A.1** (arXiv:1705.11161, proof of
Proposition 3.1, paragraph "Ergodicity modulo scaling", lines 1124-1196). Under Lemma A.1 and Remark A.2
(`ZeroConeLemmaA1`) and the named steps of the paragraph (`ZeroConeConfigCovariance`, lines 1127-1137;
`SpaceFillingSLESimilarityLaw`, lines 1182-1183; `ZeroConeCurveFactorStep`, lines 1186-1187;
`ZeroConePhaseFactorStep`, lines 1193-1196), every bounded measurable similarity-invariant functional of the
configuration (3.1) is almost surely constant. For each measurable `A`, the phase average
`G'(h, η̂) = P[Φ(H) ∈ A | h, η̂]` is invariant (lines 1145-1172) and hence almost surely constant
(`ae_eq_const_of_jointInvariance`), so `Φ(H)` is independent of `(h, η̂)` (lines 1193-1194). -/
theorem zeroConeTailTriviality_of_lemmaA1
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hA1 : ZeroConeLemmaA1 D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) :
    ZeroConeTailTriviality D hγ := by
  intro G F hF Φ hΦm hΦb hΦinv
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Cfg, hCfgm, hreal, hinv⟩ := hcov
  obtain ⟨H', hH'm, -, hH'eq⟩ := exists_zeroConeField_version_indepFun_igCurve D hγ
  have hηm : Measurable ηL := D.measurable_curves.1
  have hΨm : Measurable fun q : (Field × C(ℝ, ℂ)) × ℝ => Φ (Cfg q) := hΦm.comp hCfgm
  refine hphase G F hF Φ hΦm hΦb hΦinv ?_
  have hxm : Measurable fun p : Ω × ℝ => (H' p.1, ηL p.1) :=
    (hH'm.comp measurable_fst).prodMk (hηm.comp measurable_fst)
  have hfs : IndepFun (Prod.fst : Ω × ℝ → Ω) Prod.snd (P.prod zeroConePhase) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
      measure_univ, one_smul, one_smul]
    exact Measure.map_id
  have hxy : IndepFun (fun p : Ω × ℝ => (H' p.1, ηL p.1)) Prod.snd (P.prod zeroConePhase) :=
    hfs.comp (hH'm.prodMk hηm) measurable_id
  have hmapx : (P.prod zeroConePhase).map (fun p : Ω × ℝ => (H' p.1, ηL p.1)) =
      P.map (fun ω => (H' ω, ηL ω)) := by
    rw [show (fun p : Ω × ℝ => (H' p.1, ηL p.1)) = (fun ω => (H' ω, ηL ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hH'm.prodMk hηm) measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul]
  have hmapy : (P.prod zeroConePhase).map Prod.snd = zeroConePhase := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hsec : ∀ A : Set ℝ, MeasurableSet A → ∃ c : ℝ≥0∞,
      ∀ᵐ a ∂(P.prod zeroConePhase).map (fun p : Ω × ℝ => (H' p.1, ηL p.1)),
        (P.prod zeroConePhase).map Prod.snd
          (Prod.mk a ⁻¹' ((fun q : (Field × C(ℝ, ℂ)) × ℝ => Φ (Cfg q)) ⁻¹' A)) = c := by
    intro A hA
    rw [hmapx, hmapy]
    let G' : Field × C(ℝ, ℂ) → ℝ := fun a => (zeroConePhase (Prod.mk a ⁻¹'
      ((fun q : (Field × C(ℝ, ℂ)) × ℝ => Φ (Cfg q)) ⁻¹' A))).toReal
    have hG'm : Measurable G' := (measurable_measure_prodMk_left (hΨm hA)).ennreal_toReal
    have hG'01 : ∀ a, 0 ≤ G' a ∧ G' a ≤ 1 := fun a =>
      ⟨ENNReal.toReal_nonneg, toReal_measure_le_one zeroConePhase _⟩
    have hG'inv : ∀ᵐ h ∂P.map (zeroConeFieldOf γ X₀ B₀ B₀'), ∀ᵐ e ∂P.map ηL, ∀ C : ℝ, 0 < C →
        ∀ z : ℂ, G' (lqgSimilarityField γ C z h, affineReroot z C 0 e) = G' (h, e) := by
      filter_upwards [hinv] with h hh
      filter_upwards [hh] with e he C hC z
      obtain ⟨s, hs⟩ := he C hC z
      have hfm : Measurable fun θ => Φ (Cfg ((lqgSimilarityField γ C z h, affineReroot z C 0 e), θ)) :=
        hΨm.comp measurable_prodMk_left
      have key := zeroConePhase_preimage_eq_of_ae_toIcoMod
        (g := fun θ => Φ (Cfg ((h, e), θ))) hfm s
        (by
          filter_upwards [hs] with θ hθ
          exact hΦinv _ _ _ _ _ hθ) hA
      exact congrArg ENNReal.toReal key
    obtain ⟨c, hc⟩ := ae_eq_const_of_jointInvariance D hγ hA1 hlaw hcurve hG'm hG'01 hG'inv
    refine ⟨ENNReal.ofReal c, ?_⟩
    have hc' : ∀ᵐ ω ∂P, G' (H' ω, ηL ω) = c := by
      filter_upwards [hc, hH'eq] with ω h1 h2
      rw [h2]
      exact h1
    have hc'' : ∀ᵐ a ∂P.map (fun ω => (H' ω, ηL ω)), G' a = c :=
      (ae_map_iff (hH'm.prodMk hηm).aemeasurable (measurableSet_eq_fun hG'm measurable_const)).2 hc'
    filter_upwards [hc''] with a ha
    rw [← ha, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hind := indepFun_of_ae_const_section hxm measurable_snd hxy hΨm hsec
  have hlift : ∀ᵐ p ∂P.prod zeroConePhase, H' p.1 = zeroConeFieldOf γ X₀ B₀ B₀' p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hH'eq
  refine hind.congr ?_ ?_
  · filter_upwards [hreal G F hF, hlift] with p h1 h2
    show Φ (Cfg ((H' p.1, ηL p.1), p.2)) = Φ (F p)
    rw [h2, h1]
  · filter_upwards [hlift] with p hp
    show (H' p.1, ηL p.1) = (zeroConeFieldOf γ X₀ B₀ B₀' p.1, ηL p.1)
    rw [hp]

end Hypotheses

section Assembly

open MatedCRTHarmonic.MatedCRT (degInner degOuter diamAreaSup)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The hypotheses of the invariance principle for the shifted zero-cone configuration from Lemma A.1**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Proposition 3.1; hypotheses of arXiv:1807.07515, Theorem 1.16): the
assembly `exists_zeroCone_config_gmsHypotheses` with the tail triviality of the zero cone replaced by Lemma A.1 and
Remark A.2 (`ZeroConeLemmaA1`) and the named steps of the paragraph "Ergodicity modulo scaling" (lines 1124-1196). -/
theorem exists_zeroCone_config_gmsHypotheses_of_lemmaA1
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1 D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) :
    ∃ G : Ω → Path2, ∃ H : Ω × ℝ → CellConfig,
      (∀ᵐ p ∂P.prod zeroConePhase, ∃ h : IsAreaParametrized
          ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
        H p = shiftedAreaCellConfig h one_pos p.2
          (bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1) (fun t => (G p.1 (t + 1 * p.2)).2)) ∧
          (H p).IsCellConfiguration) ∧
      AEMeasurable (fun p => (H p).code) (P.prod zeroConePhase) ∧
      ∀ F : Ω × ℝ → GMSSpace, AEMeasurable F (P.prod zeroConePhase) →
        (∀ᵐ p ∂P.prod zeroConePhase, (F p).1 = H p) →
        IsZeroConeConfigRealization D hγ G F ∧
          MassTransport ((P.prod zeroConePhase).map F) ∧
          ErgodicModuloScaling ((P.prod zeroConePhase).map F) ∧
          FiniteExpectation ((P.prod zeroConePhase).map F) ∧
          ConnectedAlongLines ((P.prod zeroConePhase).map F) :=
  exists_zeroCone_config_gmsHypotheses D hγ hf hI h25
    (zeroConeTailTriviality_of_lemmaA1 D hγ hA1 hcov hlaw hcurve hphase)

end Assembly

end MatedCRT
