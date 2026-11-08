import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import MatedCRT.Proofs.Sec1.EnvironmentScaling.PrestonPolishTransfer
import MatedCRT.Proposed.PrestonAnalytic2008
import MatedCRT.Proofs.Sec5.StoppedMarginContinuousDecoder

/-!
# Borel versions of finite real infima on a Borel relation (steps2-r3:3374-3388)

Source: `notes/wpn-steps2/steps2-r3.tex`, lines 3374-3388 (sha256 `88dfb1f9…`), the countable Borel-version passage that
produces the continuous surplus `f(x) = v_ρ(μ,t)(x) + tG_ρ(0,x)` on `A = marginDomain s (ρ/2)`.

Let `S ⊆ X × Y` be a measurable relation between Polish spaces (`X` the circle-array state, `Y` the continuous-function
carrier), `g : Y → ℝ` continuous, and `G ⊆ X` a measurable good set on which every section
`relSection S c = {w | (c, w) ∈ S}` is nonempty and bounded below under `g`. Then:

* the strict sublevel sets `{c | ∃ w ∈ relSection S c, g w < a}` of the infimum are first-coordinate projections of
  Borel subsets of `X × Y`, hence analytic (`MeasurableSet.analyticSet`, `AnalyticSet.image_of_continuous`);
* each is universally measurable by the Preston transfer `prestonAnalyticUniversallyMeasurable_of_cantor`, whose two
  printed inputs stay explicit as the hypotheses `hCantor : PrestonAnalyticCantorStmt` (Preston, Theorem 7.1,
  printed p. 39) and `hT61 : PrestonTheorem61Stmt` (Preston, Theorem 6.1(1), printed p. 35);
* a real function with null-measurable sublevel preimages has an a.e. equal Borel version under every probability law,
  so the infimum on `G` has a Borel version (`exists_measurable_infimum_version`);
* countably many such versions agree with their infima simultaneously almost surely (`ae_all_iff`);
* along a dense sequence `a` of a compact metric space `A`, the `denseDecoder` of `StoppedMarginContinuousDecoder`
  decodes the shifted versions into a Borel map `X → C(A, ℝ)` which agrees almost surely on `G` with any family of
  continuous functions whose values at `a n` are almost surely the shifted infima.

The almost-sure variants (`…_ae`) take the section hypotheses only almost surely on `G`, as the Borel obstacle code
`CodeSectionStmt` provides them; they reduce to the everywhere versions on a measurable subset of `G` whose complement
in `G` is a null set.

The identity between the infima and the actual surplus `v_ρ(μ,t)`, the nonemptiness and lower bounds of the sections on
the good set, the Borel obstacle code `CodeSectionStmt`, and the continuity of the actual surplus are not proved here.
They enter as explicit hypotheses (`hbdd`, `hId`, `w`).
-/

namespace MatedCRT.StoppedMarginValueVersions

open MeasureTheory Set MatedCRT.StoppedMarginDecoder MatedCRT.StoppedInteriorMargin

/-- A real function whose sublevel preimages `h ⁻¹' Iio a` are all null-measurable is null-measurable. The sets whose
preimage is null-measurable form a σ-algebra on `ℝ`, which contains the generators `Iio a` of the Borel σ-algebra
(`borel_eq_generateFrom_Iio`). -/
theorem nullMeasurable_of_nullMeasurableSet_preimage_Iio {Z : Type} [MeasurableSpace Z] {μ : Measure Z}
    {h : Z → ℝ} (hI : ∀ a : ℝ, NullMeasurableSet (h ⁻¹' Iio a) μ) : NullMeasurable h μ := by
  let M : MeasurableSpace ℝ :=
    { MeasurableSet' := fun B => NullMeasurableSet (h ⁻¹' B) μ
      measurableSet_empty := by
        show NullMeasurableSet (h ⁻¹' ∅) μ
        rw [Set.preimage_empty]
        exact MeasurableSet.empty.nullMeasurableSet
      measurableSet_compl := fun B hB => by
        show NullMeasurableSet (h ⁻¹' Bᶜ) μ
        rw [Set.preimage_compl]
        exact NullMeasurableSet.compl hB
      measurableSet_iUnion := fun f hf => by
        show NullMeasurableSet (h ⁻¹' ⋃ i, f i) μ
        rw [Set.preimage_iUnion]
        exact NullMeasurableSet.iUnion (s := fun i => h ⁻¹' f i) (fun i => hf i) }
  have hle : borel ℝ ≤ M := by
    rw [borel_eq_generateFrom_Iio]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨a, rfl⟩
    exact hI a
  intro B hB
  exact hle B hB

/-- The compactness of `marginDomain s R = closedBall 0 R ∩ {x | s ≤ |x|}` (the domain `A` of steps2-r3 has `R = ρ/2`). -/
theorem marginDomain_compactSpace (s R : ℝ) : CompactSpace (marginDomain s R) := by
  have hc : IsCompact (marginDomain s R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_right (isClosed_le continuous_const continuous_norm)
  exact isCompact_iff_compactSpace.mp hc

section Sections

variable {X Y : Type}

/-- The section `{w | (c, w) ∈ S}` of a relation `S` over the first coordinate `c`. -/
def relSection (S : Set (X × Y)) (c : X) : Set Y :=
  {w | (c, w) ∈ S}

/-- The first-coordinate projection of the strict sublevel set `{(c, w) ∈ S | g w < a}`: the set of states `c` whose
section contains a point at which the evaluation `g` lies strictly below `a`. -/
def strictSublevelProj (S : Set (X × Y)) (g : Y → ℝ) (a : ℝ) : Set X :=
  Prod.fst '' (S ∩ {p : X × Y | g p.2 < a})

theorem mem_strictSublevelProj_iff (S : Set (X × Y)) (g : Y → ℝ) (a : ℝ) (c : X) :
    c ∈ strictSublevelProj S g a ↔ ∃ w ∈ relSection S c, g w < a := by
  constructor
  · rintro ⟨⟨c', w⟩, ⟨hS, hlt⟩, rfl⟩
    exact ⟨w, hS, hlt⟩
  · rintro ⟨w, hw, hlt⟩
    exact ⟨(c, w), ⟨hw, hlt⟩, rfl⟩

/-- A real infimum over a nonempty set bounded below under `g` is below `a` exactly when some point is. -/
theorem csInf_image_lt_iff {g : Y → ℝ} {s : Set Y} (hne : s.Nonempty) (hbdd : BddBelow (g '' s)) (a : ℝ) :
    sInf (g '' s) < a ↔ ∃ w ∈ s, g w < a := by
  rw [csInf_lt_iff hbdd (hne.image g)]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, hlt⟩
    exact ⟨w, hw, hlt⟩
  · rintro ⟨w, hw, hlt⟩
    exact ⟨g w, ⟨w, hw, rfl⟩, hlt⟩

end Sections

section Polish

variable {X Y : Type}

variable [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The strict sublevel projection is analytic: it is the image under the continuous `Prod.fst` of a Borel subset of the
Polish space `X × Y`. -/
theorem analyticSet_strictSublevelProj {S : Set (X × Y)} (hS : MeasurableSet S) {g : Y → ℝ}
    (hg : Continuous g) (a : ℝ) : AnalyticSet (strictSublevelProj S g a) := by
  have hlt : MeasurableSet {p : X × Y | g p.2 < a} :=
    measurableSet_lt (f := fun p : X × Y => g p.2) (g := fun _ : X × Y => a)
      (hg.measurable.comp measurable_snd) measurable_const
  exact AnalyticSet.image_of_continuous (hS.inter hlt).analyticSet continuous_fst

/-- Universal measurability of the strict sublevel projections, by the Preston transfer from the two printed inputs
`PrestonAnalyticCantorStmt` (Theorem 7.1) and `PrestonTheorem61Stmt` (Theorem 6.1(1)). -/
theorem nullMeasurableSet_strictSublevelProj (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {g : Y → ℝ}
    (hg : Continuous g) (a : ℝ) (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet (strictSublevelProj S g a) μ :=
  prestonAnalyticUniversallyMeasurable_of_cantor hCantor hT61 X _
    (analyticSet_strictSublevelProj hS hg a) μ inferInstance

/-- **Borel version of a real infimum.** On a measurable good set `G`, where every section is nonempty and bounded below
under the continuous evaluation `g`, the infimum `c ↦ sInf (g '' relSection S c)` has a Borel version `v`, which agrees
with the infimum almost surely on `G`, for every probability measure `μ` on `X`. -/
theorem exists_measurable_infimum_version (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {g : Y → ℝ}
    (hg : Continuous g) {G : Set X} (hG : MeasurableSet G)
    (hbdd : ∀ c ∈ G, (relSection S c).Nonempty ∧ BddBelow (g '' relSection S c))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ v : X → ℝ, Measurable v ∧ ∀ᵐ c ∂μ, c ∈ G → v c = sInf (g '' relSection S c) := by
  classical
  let h : X → ℝ := fun c => if c ∈ G then sInf (g '' relSection S c) else 0
  have hI : ∀ a : ℝ, NullMeasurableSet (h ⁻¹' Iio a) μ := by
    intro a
    have heq : h ⁻¹' Iio a =
        (G ∩ strictSublevelProj S g a) ∪ (Gᶜ ∩ {_c : X | (0 : ℝ) < a}) := by
      ext c
      by_cases hc : c ∈ G
      · obtain ⟨hne, hbd⟩ := hbdd c hc
        have hval : h c = sInf (g '' relSection S c) := by simp [h, hc]
        have key : h c < a ↔ c ∈ strictSublevelProj S g a := by
          rw [mem_strictSublevelProj_iff, hval]
          exact csInf_image_lt_iff hne hbd a
        constructor
        · intro hlt
          exact Or.inl ⟨hc, key.1 hlt⟩
        · rintro (⟨-, hP⟩ | ⟨hnc, -⟩)
          · exact key.2 hP
          · exact (hnc hc).elim
      · have hval : h c = 0 := by simp [h, hc]
        constructor
        · intro hlt
          refine Or.inr ⟨hc, ?_⟩
          show (0 : ℝ) < a
          rw [← hval]
          exact hlt
        · rintro (⟨hcG, -⟩ | ⟨-, ha⟩)
          · exact (hc hcG).elim
          · show h c < a
            rw [hval]
            exact ha
    rw [heq]
    exact (hG.nullMeasurableSet.inter
      (nullMeasurableSet_strictSublevelProj hCantor hT61 hS hg a μ)).union
      (hG.compl.nullMeasurableSet.inter (MeasurableSet.const _).nullMeasurableSet)
  have hae : AEMeasurable h μ :=
    (nullMeasurable_of_nullMeasurableSet_preimage_Iio hI).aemeasurable
  refine ⟨hae.mk h, hae.measurable_mk, ?_⟩
  filter_upwards [hae.ae_eq_mk] with c hc hcG
  rw [← hc]
  simp [h, hcG]

/-- **Countable family.** For countably many continuous evaluations `g i`, with measurable good sets `G i`, there are
Borel versions `v i` of the infima which agree with them simultaneously almost surely (`ae_all_iff`). -/
theorem exists_measurable_infimum_versions (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {ι : Type} [Countable ι]
    {g : ι → Y → ℝ} (hg : ∀ i, Continuous (g i)) {G : ι → Set X} (hG : ∀ i, MeasurableSet (G i))
    (hbdd : ∀ i, ∀ c ∈ G i, (relSection S c).Nonempty ∧ BddBelow (g i '' relSection S c))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ v : ι → X → ℝ, (∀ i, Measurable (v i)) ∧
      ∀ᵐ c ∂μ, ∀ i, c ∈ G i → v i c = sInf (g i '' relSection S c) := by
  choose v hvm hva using fun i =>
    exists_measurable_infimum_version hCantor hT61 hS (hg i) (hG i) (hbdd i) μ
  exact ⟨v, hvm, ae_all_iff.2 hva⟩

/-- **Continuous surplus version.** Let `a` be a dense sequence in a compact metric space `A`, let `ev x` be the
continuous evaluation at `x`, and let `shift n` be the surplus shift `t G(0, a n)`. Decoding the shifted countable
family of Borel infimum versions along `a` with `denseDecoder` gives a Borel map `X → C(A, ℝ)`. It agrees almost surely on
`G` with a state-dependent continuous function `w c` as soon as the finite-infimum identity `hId` holds at the points
`a n` almost surely on `G`. -/
theorem exists_continuous_surplus_version (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {A : Type} [MetricSpace A]
    [CompactSpace A] {a : ℕ → A} (ha : DenseRange a) {ev : A → Y → ℝ} (hev : ∀ x, Continuous (ev x))
    {shift : ℕ → ℝ} {G : Set X} (hG : MeasurableSet G)
    (hbdd : ∀ n, ∀ c ∈ G, (relSection S c).Nonempty ∧ BddBelow (ev (a n) '' relSection S c))
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → C(A, ℝ))
    (hId : ∀ᵐ c ∂μ, c ∈ G → ∀ n, sInf (ev (a n) '' relSection S c) + shift n = w c (a n)) :
    ∃ F : X → C(A, ℝ), @Measurable X C(A, ℝ) _ (borel C(A, ℝ)) F ∧
      ∀ᵐ c ∂μ, c ∈ G → F c = w c := by
  obtain ⟨v, hvm, hva⟩ := exists_measurable_infimum_versions hCantor hT61 hS (ι := ℕ)
    (g := fun n => ev (a n)) (fun n => hev (a n)) (G := fun _ => G) (fun _ => hG) hbdd μ
  let V : ℕ → X → ℝ := fun n c => v n c + shift n
  have hVm : ∀ n, Measurable (V n) := fun n => (hvm n).add_const (shift n)
  have hV : ∀ᵐ c ∂μ, c ∈ G → ∀ n, V n c = w c (a n) := by
    filter_upwards [hva, hId] with c hc1 hc2 hcG n
    show v n c + shift n = w c (a n)
    rw [hc1 n hcG]
    exact hc2 hcG n
  refine ⟨fun c => denseDecoder a (fun n => V n c), measurable_denseDecoder_comp ha V hVm, ?_⟩
  have hD := denseDecoder_ae_eq ha V w ((ae_restrict_iff' hG).2 hV)
  exact (ae_restrict_iff' hG).1 hD

/-- **Continuous surplus version on `marginDomain`.** The dense sequence is the one supplied by the proved
`marginDomain_denseDecoder`. The finite-infimum identity `hId` is required at every point of `marginDomain s R` almost
surely on `G`, as the source asserts ("almost surely, `f(x) = v_ρ(μ,t)(x) + tG_ρ(0,x)` for `x ∈ A`"). -/
theorem exists_continuous_surplus_version_marginDomain (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) (s R : ℝ)
    (hne : (marginDomain s R).Nonempty) {ev : marginDomain s R → Y → ℝ}
    (hev : ∀ x, Continuous (ev x)) {shift : marginDomain s R → ℝ} {G : Set X} (hG : MeasurableSet G)
    (hbdd : ∀ x : marginDomain s R, ∀ c ∈ G, (relSection S c).Nonempty ∧ BddBelow (ev x '' relSection S c))
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → C(marginDomain s R, ℝ))
    (hId : ∀ᵐ c ∂μ, c ∈ G → ∀ x : marginDomain s R, sInf (ev x '' relSection S c) + shift x = w c x) :
    ∃ F : X → C(marginDomain s R, ℝ),
      @Measurable X C(marginDomain s R, ℝ) _ (borel C(marginDomain s R, ℝ)) F ∧
        ∀ᵐ c ∂μ, c ∈ G → F c = w c := by
  obtain ⟨a, ha, -⟩ := marginDomain_denseDecoder s R hne
  have := marginDomain_compactSpace s R
  exact exists_continuous_surplus_version hCantor hT61 hS ha hev (shift := fun n => shift (a n)) hG
    (fun n => hbdd (a n)) μ w (hId.mono fun c hc hcG n => hc hcG (a n))

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
/-- **Good subsets.** An almost sure property `P` on a measurable set `G` holds everywhere on a measurable subset
`G' ⊆ G`, and `G'` contains almost all of `G`: the bad set `{c ∈ G | ¬P c}` is enlarged to a measurable null set by
`toMeasurable`. -/
theorem exists_measurable_subset_of_ae_on {P : X → Prop} {G : Set X} (hG : MeasurableSet G) (μ : Measure X)
    (hP : ∀ᵐ c ∂μ, c ∈ G → P c) :
    ∃ G' ⊆ G, MeasurableSet G' ∧ (∀ c ∈ G', P c) ∧ ∀ᵐ c ∂μ, c ∈ G → c ∈ G' := by
  let B : Set X := {c | c ∈ G ∧ ¬P c}
  have hB : ∀ᵐ c ∂μ, c ∉ B := hP.mono fun c hc hcB => hcB.2 (hc hcB.1)
  have hB0 : μ B = 0 := by simpa using ae_iff.1 hB
  have hN0 : μ (toMeasurable μ B) = 0 := by
    rw [measure_toMeasurable]
    exact hB0
  have hN : ∀ᵐ c ∂μ, c ∉ toMeasurable μ B := ae_iff.2 (by simpa using hN0)
  refine ⟨G \ toMeasurable μ B, fun c hc => hc.1, hG.diff (measurableSet_toMeasurable μ B), ?_, ?_⟩
  · rintro c ⟨hcG, hcN⟩
    by_contra hPc
    exact hcN (subset_toMeasurable μ B ⟨hcG, hPc⟩)
  · filter_upwards [hN] with c hcN hcG
    exact ⟨hcG, hcN⟩

/-- **Borel version, almost sure hypotheses.** As `exists_measurable_infimum_version`, with the section hypotheses only
almost surely on `G`, which is the form the Borel obstacle code provides. -/
theorem exists_measurable_infimum_version_ae (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {g : Y → ℝ}
    (hg : Continuous g) {G : Set X} (hG : MeasurableSet G) (μ : Measure X) [IsProbabilityMeasure μ]
    (hbdd : ∀ᵐ c ∂μ, c ∈ G → (relSection S c).Nonempty ∧ BddBelow (g '' relSection S c)) :
    ∃ v : X → ℝ, Measurable v ∧ ∀ᵐ c ∂μ, c ∈ G → v c = sInf (g '' relSection S c) := by
  obtain ⟨G', hG'G, hG', hP, hae⟩ := exists_measurable_subset_of_ae_on hG μ hbdd
  obtain ⟨v, hvm, hv⟩ := exists_measurable_infimum_version hCantor hT61 hS hg hG' hP μ
  exact ⟨v, hvm, (hv.and hae).mono fun c hc hcG => hc.1 (hc.2 hcG)⟩

/-- **Continuous surplus version, almost sure hypotheses.** The section hypotheses and the finite-infimum identity are
required only almost surely on `G`. -/
theorem exists_continuous_surplus_version_ae (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) {A : Type} [MetricSpace A]
    [CompactSpace A] {a : ℕ → A} (ha : DenseRange a) {ev : A → Y → ℝ} (hev : ∀ x, Continuous (ev x))
    {shift : ℕ → ℝ} {G : Set X} (hG : MeasurableSet G) (μ : Measure X) [IsProbabilityMeasure μ]
    (w : X → C(A, ℝ))
    (hbdd : ∀ᵐ c ∂μ, c ∈ G → ∀ n, (relSection S c).Nonempty ∧ BddBelow (ev (a n) '' relSection S c))
    (hId : ∀ᵐ c ∂μ, c ∈ G → ∀ n, sInf (ev (a n) '' relSection S c) + shift n = w c (a n)) :
    ∃ F : X → C(A, ℝ), @Measurable X C(A, ℝ) _ (borel C(A, ℝ)) F ∧
      ∀ᵐ c ∂μ, c ∈ G → F c = w c := by
  have hP : ∀ᵐ c ∂μ, c ∈ G →
      (∀ n, (relSection S c).Nonempty ∧ BddBelow (ev (a n) '' relSection S c)) ∧
        ∀ n, sInf (ev (a n) '' relSection S c) + shift n = w c (a n) :=
    (hbdd.and hId).mono fun c hc hcG => ⟨hc.1 hcG, hc.2 hcG⟩
  obtain ⟨G', hG'G, hG', hP', hae⟩ := exists_measurable_subset_of_ae_on hG μ hP
  obtain ⟨F, hFm, hF⟩ := exists_continuous_surplus_version hCantor hT61 hS ha hev (shift := shift) hG'
    (fun n c hc => (hP' c hc).1 n) μ w (ae_of_all μ fun c hc n => (hP' c hc).2 n)
  exact ⟨F, hFm, (hF.and hae).mono fun c hc hcG => hc.1 (hc.2 hcG)⟩

/-- **Continuous surplus version on `marginDomain`, almost sure hypotheses.** -/
theorem exists_continuous_surplus_version_marginDomain_ae (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) {S : Set (X × Y)} (hS : MeasurableSet S) (s R : ℝ)
    (hne : (marginDomain s R).Nonempty) {ev : marginDomain s R → Y → ℝ}
    (hev : ∀ x, Continuous (ev x)) {shift : marginDomain s R → ℝ} {G : Set X} (hG : MeasurableSet G)
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → C(marginDomain s R, ℝ))
    (hbdd : ∀ᵐ c ∂μ, c ∈ G → ∀ x : marginDomain s R,
      (relSection S c).Nonempty ∧ BddBelow (ev x '' relSection S c))
    (hId : ∀ᵐ c ∂μ, c ∈ G → ∀ x : marginDomain s R, sInf (ev x '' relSection S c) + shift x = w c x) :
    ∃ F : X → C(marginDomain s R, ℝ),
      @Measurable X C(marginDomain s R, ℝ) _ (borel C(marginDomain s R, ℝ)) F ∧
        ∀ᵐ c ∂μ, c ∈ G → F c = w c := by
  obtain ⟨a, ha, -⟩ := marginDomain_denseDecoder s R hne
  have := marginDomain_compactSpace s R
  exact exists_continuous_surplus_version_ae hCantor hT61 hS ha hev (shift := fun n => shift (a n)) hG μ w
    (hbdd.mono fun c hc hcG n => hc hcG (a n)) (hId.mono fun c hc hcG n => hc hcG (a n))

end Polish

end MatedCRT.StoppedMarginValueVersions
