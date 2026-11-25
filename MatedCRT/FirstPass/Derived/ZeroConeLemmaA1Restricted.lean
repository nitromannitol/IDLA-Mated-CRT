import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1

/-!
# Ergodicity modulo scaling of the shifted zero-cone configuration from Lemma A.1, curve form of Remark A.2

Gwynne–Miller–Sheffield (arXiv:1705.11161, proof of Proposition 3.1, paragraph "Ergodicity modulo scaling",
`notes/refs/1705.11161.txt` lines 1124-1196) use Lemma A.1 (lines 1952-1956) for the `0`-quantum cone, and at lines
1188-1193 the analogue of Remark A.2 (lines 1958-1964) for the imaginary-geometry field `h^IG`, only through its
consequence for the space-filling SLE `η̂` that `h^IG` generates: a measurable function `g(η̂)` which is almost surely
invariant under each coordinate change `η̂ ↦ ψ⁻¹ ∘ η̂` (re-rooted at the hitting time of `ψ(0)`), `ψ(w) = C w + z`, is
almost surely constant.

`ZeroConeLemmaA1Pos` states Lemma A.1 for the circle-average embedding of the `0`-quantum cone (the first clause of
`ZeroConeLemmaA1`, verbatim) together with this consequence for the Lebesgue-parametrized curve `ηL` of the coupling
directly, in place of the statement for all functionals of the circle-average process of `h^IG` at all real radii.
This file re-derives `ZeroConeTailTriviality` (`zeroConeTailTriviality_of_lemmaA1Pos`) and the assembly
(`exists_zeroCone_config_gmsHypotheses_of_lemmaA1Pos`) from it, following `ZeroConeTailOfLemmaA1.lean`; the
remaining named steps (`ZeroConeConfigCovariance`, `SpaceFillingSLESimilarityLaw`, `ZeroConeCurveFactorStep`,
`ZeroConePhaseFactorStep`) are those of that file.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Lemma A.1 of Gwynne–Miller–Sheffield, arXiv:1705.11161, with Remark A.2 in the form used for the
space-filling SLE** (`notes/refs/1705.11161.txt` lines 1952-1964, as used in the proof of Proposition 3.1, lines
1141-1142, 1186 and 1188-1193; written answer on this proof: `notes/fp-gaps/CODEX-MQ-sbl-15.md`, lines 17-35 for
Lemma A.1 and the curve, lines 27 and 47 for the dilations, line 59 for this form of the second clause).
PENDING TRUTH CHECK.

1. (Lemma A.1, lines 1952-1956.) Let `h` be the circle-average embedding of the `0`-quantum cone (the field
   `zeroConeFieldOf γ X₀ B₀ B₀'` of the coupling). Every bounded, non-negative, measurable functional `F` of `h` which
   is scale and translation invariant in the sense that, almost surely, `F(h(C · + z) + Q log C) = F(h)` for all
   `C > 0` and `z ∈ ℂ` (A.1), is almost surely equal to a deterministic constant.
2. (Remark A.2, lines 1958-1962, for the imaginary-geometry field `h^IG` of the coupling, lines 1188-1192, stated for
   the curve it generates.) Let `ηL` be the whole-plane space-filling SLE of the coupling, parametrized by Lebesgue
   measure with `ηL 0 = 0`. Every bounded, non-negative, measurable functional `g` of the curve which is invariant
   under each coordinate change `ηL ↦ ψ⁻¹ ∘ ηL`, `ψ(w) = C w + z` (`C > 0`, `z ∈ ℂ`), re-rooted at the hitting time
   of `z` and reparametrized by Lebesgue measure (`affineReroot z C 0`), almost surely for each fixed `(C, z)`, is
   almost surely constant: the law of `ηL` is ergodic under the coordinate changes by positive similarities. By the
   imaginary-geometry coordinate change of the coupling (`IsMatingOfTreesCoupling.igMap`) this is the statement of
   Remark A.2 for the functionals of `h^IG` modulo `2πχ` that factor through the curve. It already follows from
   ergodicity under the dilations alone (`z = 0`), the form of the written answer (lines 27 and 47). -/
def ZeroConeLemmaA1Pos (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  (∀ F : Field → ℝ, Measurable F → (∃ M : ℝ, ∀ h, F h ≤ M) → (∀ h, 0 ≤ F h) →
    (∀ᵐ ω ∂P, ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      F (lqgSimilarityField γ C z (zeroConeFieldOf γ X₀ B₀ B₀' ω)) = F (zeroConeFieldOf γ X₀ B₀ B₀' ω)) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, F (zeroConeFieldOf γ X₀ B₀ B₀' ω) = c) ∧
  (∀ g : C(ℝ, ℂ) → ℝ, Measurable g → (∃ M : ℝ, ∀ e, g e ≤ M) → (∀ e, 0 ≤ g e) →
    (∀ C : ℝ, 0 < C → ∀ z : ℂ, ∀ᵐ ω ∂P, g (affineReroot z C 0 (ηL ω)) = g (ηL ω)) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, g (ηL ω) = c)

/-- **Lines 1173-1193 of arXiv:1705.11161: a jointly invariant functional of `(h, η̂)` is almost surely constant**,
from `ZeroConeLemmaA1Pos`. Let `G'` be a measurable functional of (zero-cone field, curve) with values in `[0, 1]`,
almost surely invariant under the joint coordinate change (3.3). For every measurable `B`, `G''(h) = P[G'(h, η̂) ∈ B]`
is invariant under the coordinate change of `h` (law invariance of `η̂`, lines 1179-1185), hence almost surely
constant by Lemma A.1 (line 1186); so `G'(h, η̂)` is independent of `h` (line 1187), almost surely `g(η̂)` by
`ZeroConeCurveFactorStep`, and `g(η̂)` is almost surely constant by the second clause of `ZeroConeLemmaA1Pos`
(lines 1188-1193). -/
theorem ae_eq_const_of_jointInvariance_of_lemmaA1Pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hA1 : ZeroConeLemmaA1Pos D hγ) (hlaw : SpaceFillingSLESimilarityLaw D hγ)
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
  -- the curve form of Remark A.2 (lines 1188-1193)
  let gc : C(ℝ, ℂ) → ℝ := fun e => max 0 (min 1 (g e))
  have hgcm : Measurable gc := measurable_const.max (measurable_const.min hgm)
  have hinv : ∀ C : ℝ, 0 < C → ∀ z : ℂ, ∀ᵐ ω ∂P, gc (affineReroot z C 0 (ηL ω)) = gc (ηL ω) := by
    intro C hC z
    filter_upwards [hginv C hC z] with ω h3
    show max 0 (min 1 (g (affineReroot z C 0 (ηL ω)))) = max 0 (min 1 (g (ηL ω)))
    rw [h3]
  obtain ⟨c, hc⟩ := hA1.2 gc hgcm ⟨1, fun _ => max_le zero_le_one (min_le_left _ _)⟩
    (fun _ => le_max_left _ _) hinv
  refine ⟨c, ?_⟩
  filter_upwards [hc, hgae] with ω h1 h3
  have h01 := hG'01 (zeroConeFieldOf γ X₀ B₀ B₀' ω, ηL ω)
  rw [h3] at h01 ⊢
  rw [← h1]
  show g (ηL ω) = max 0 (min 1 (g (ηL ω)))
  rw [min_eq_right h01.2, max_eq_right h01.1]

/-- **Ergodicity modulo scaling of the shifted zero-cone configuration from Lemma A.1, curve form of Remark A.2**
(arXiv:1705.11161, proof of Proposition 3.1, paragraph "Ergodicity modulo scaling", lines 1124-1196). Under
`ZeroConeLemmaA1Pos` and the named steps of the paragraph (`ZeroConeConfigCovariance`, lines 1127-1137;
`SpaceFillingSLESimilarityLaw`, lines 1182-1183; `ZeroConeCurveFactorStep`, lines 1186-1187;
`ZeroConePhaseFactorStep`, lines 1193-1196), every bounded measurable similarity-invariant functional of the
configuration (3.1) is almost surely constant. For each measurable `A`, the phase average
`G'(h, η̂) = P[Φ(H) ∈ A | h, η̂]` is invariant (lines 1145-1172) and hence almost surely constant
(`ae_eq_const_of_jointInvariance_of_lemmaA1Pos`), so `Φ(H)` is independent of `(h, η̂)` (lines 1193-1194). -/
theorem zeroConeTailTriviality_of_lemmaA1Pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hA1 : ZeroConeLemmaA1Pos D hγ) (hcov : ZeroConeConfigCovariance D hγ)
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
    obtain ⟨c, hc⟩ := ae_eq_const_of_jointInvariance_of_lemmaA1Pos D hγ hA1 hlaw hcurve hG'm hG'01 hG'inv
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

/-- **The hypotheses of the invariance principle for the shifted zero-cone configuration from Lemma A.1, curve form
of Remark A.2** (Gwynne–Miller–Sheffield, arXiv:1705.11161, Proposition 3.1; hypotheses of arXiv:1807.07515,
Theorem 1.16): the assembly `exists_zeroCone_config_gmsHypotheses` with the tail triviality of the zero cone replaced
by `ZeroConeLemmaA1Pos` and the named steps of the paragraph "Ergodicity modulo scaling" (lines 1124-1196). -/
theorem exists_zeroCone_config_gmsHypotheses_of_lemmaA1Pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1Pos D hγ) (hcov : ZeroConeConfigCovariance D hγ)
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
    (zeroConeTailTriviality_of_lemmaA1Pos D hγ hA1 hcov hlaw hcurve hphase)

end Assembly

end MatedCRT
