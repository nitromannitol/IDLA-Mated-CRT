import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulus
import LatticeProb.Prob.AnalyticUniversalMeasurable
import LatticeProb.Topology.PolishContinuousMap

/-!
# Rotation invariance of the shifted zero-cone configuration on a standard Borel sample space

Gwynne–Miller–Sheffield (arXiv:1705.11161), proof of Proposition 3.1, lines 1212-1213: "the law of `(h, η)` is
invariant under rotations about the origin", so the law of the cell configuration (3.1) is invariant under the
quarter turn of the plane. The written argument is `notes/fp-gaps/CODEX-MQ-sbl-30.md`, "M5 and A2" (line 39).

On a standard Borel sample space the law of every realization `F` of the configuration is a function of the law of
the data `((η₀, G), θ)` alone, although the configuration is not a Borel function of the data
(`map_eq_map_of_ae_eq_comp`): if `F = Φ ∘ d` almost everywhere, a Borel set of configurations pulls back under `d` to
a set sandwiched between the analytic image `d(B₁)` of a Borel subset `B₁` of the preimage and the complement of the
analytic image of a Borel subset of its complement; analytic sets are universally measurable (Lusin; Kechris,
*Classical Descriptive Set Theory*, Theorem 21.10, `LatticeProb.AnalyticSet.nullMeasurableSet`), so the measure of
the preimage is computed from the law of `d`. The quarter turn of the plane carries the unit cells of a curve to the
unit cells of the rotated curve with the same labels (`isometryCellConfig_quarterTurn_shiftedAreaCellConfig`), so the
rotated configuration is the configuration of the rotated data. The remaining input is the rotation invariance of
the joint law of the zero-cone curve and its boundary-length pair (`ZeroConeBoundaryPairRotationLaw`).

Main declarations:

* `map_eq_map_of_ae_eq_comp`: the law of a random element almost everywhere equal to a fixed function of Polish
  data on a standard Borel space depends only on the law of the data.
* `isometryCellConfig_quarterTurn_shiftedAreaCellConfig`: the quarter turn of the shifted unit cells of an
  area-parametrized curve.
* `ZeroConeBoundaryPairRotationLaw`: the named rotation step.
* `zeroConeConfigRotationInvariance`: `ZeroConeConfigRotationInvariance` on standard Borel sample spaces.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

/-! ### The law of a function of standard Borel data -/

section LawOfData

/-- **The law of a random element is determined by the law of the data it is a function of.** On a standard Borel
space `X` with a finite measure `μ`, let `d, d'` be Borel maps into a Polish space with the same law, and let `F, F'`
be almost measurable, almost everywhere equal to `Φ ∘ d` and `Φ ∘ d'` for one (arbitrary) map `Φ`. Then `F` and `F'`
have the same law. The preimage `Φ⁻¹(A)` of a Borel set lies between the analytic set `d(B₁)` and the complement of
the analytic set `d(B₃)`, for Borel sets `B₁ ⊆ d⁻¹(Φ⁻¹(A))` and `B₃ ⊆ d⁻¹(Φ⁻¹(A))ᶜ` of full measure in them; analytic
sets are null-measurable for the law of `d` (Lusin; Kechris, Theorem 21.10). -/
theorem map_eq_map_of_ae_eq_comp {X Y Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Z]
    {μ : Measure X} [IsFiniteMeasure μ] {d d' : X → Y} (hd : Measurable d) (hd' : Measurable d')
    (hdd : μ.map d = μ.map d') {F F' : X → Z} (hF : AEMeasurable F μ) (hF' : AEMeasurable F' μ)
    (Φ : Y → Z) (hFΦ : F =ᵐ[μ] Φ ∘ d) (hFΦ' : F' =ᵐ[μ] Φ ∘ d') :
    μ.map F = μ.map F' := by
  ext A hA
  rw [Measure.map_apply_of_aemeasurable hF hA, Measure.map_apply_of_aemeasurable hF' hA]
  have h1 : F ⁻¹' A =ᵐ[μ] d ⁻¹' (Φ ⁻¹' A) := hFΦ.fun_comp (· ∈ A)
  have h1' : F' ⁻¹' A =ᵐ[μ] d' ⁻¹' (Φ ⁻¹' A) := hFΦ'.fun_comp (· ∈ A)
  rw [measure_congr h1, measure_congr h1']
  have hnull : NullMeasurableSet (d ⁻¹' (Φ ⁻¹' A)) μ := (hF.nullMeasurable hA).congr h1
  obtain ⟨B₁, hB₁sub, hB₁, hB₁ae⟩ := hnull.exists_measurable_subset_ae_eq
  obtain ⟨B₃, hB₃sub, hB₃, hB₃ae⟩ := hnull.compl.exists_measurable_subset_ae_eq
  have hI : NullMeasurableSet (d '' B₁) (μ.map d) :=
    LatticeProb.AnalyticSet.nullMeasurableSet _ (hB₁.analyticSet_image hd)
  have hJ : NullMeasurableSet (d '' B₃) (μ.map d) :=
    LatticeProb.AnalyticSet.nullMeasurableSet _ (hB₃.analyticSet_image hd)
  have hI' : NullMeasurableSet (d '' B₁) (μ.map d') := hdd ▸ hI
  have hJ' : NullMeasurableSet (d '' B₃) (μ.map d') := hdd ▸ hJ
  have hIE : d '' B₁ ⊆ Φ ⁻¹' A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB₁sub hx
  have hEJ : Φ ⁻¹' A ⊆ (d '' B₃)ᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hB₃sub hx hy
  have hle1 : μ (d ⁻¹' (Φ ⁻¹' A)) ≤ μ.map d (d '' B₁) := by
    rw [← measure_congr hB₁ae, Measure.map_apply₀ hd.aemeasurable hI]
    exact measure_mono (subset_preimage_image d B₁)
  have hle2 : μ.map d (d '' B₃)ᶜ ≤ μ (d ⁻¹' (Φ ⁻¹' A)) := by
    rw [Measure.map_apply₀ hd.aemeasurable hJ.compl]
    calc μ (d ⁻¹' (d '' B₃)ᶜ) ≤ μ B₃ᶜ := by
          refine measure_mono ?_
          rw [preimage_compl]
          exact compl_subset_compl.mpr (subset_preimage_image d B₃)
      _ = μ (d ⁻¹' (Φ ⁻¹' A)) := by
          rw [measure_congr hB₃ae.compl, compl_compl]
  have hle3 : μ.map d (d '' B₁) ≤ μ (d' ⁻¹' (Φ ⁻¹' A)) := by
    rw [hdd, Measure.map_apply₀ hd'.aemeasurable hI']
    exact measure_mono (preimage_mono hIE)
  have hle4 : μ (d' ⁻¹' (Φ ⁻¹' A)) ≤ μ.map d (d '' B₃)ᶜ := by
    rw [hdd, Measure.map_apply₀ hd'.aemeasurable hJ'.compl]
    exact measure_mono (preimage_mono hEJ)
  exact le_antisymm (hle1.trans hle3) (hle4.trans hle2)

end LawOfData

/-! ### The quarter turn of the shifted unit cells -/

section QuarterTurnCells

open ReflectedGMS.GMS

theorem cellConfig_eq_of {H H' : CellConfig} (h1 : H.cells = H'.cells) (h2 : H.c = H'.c) : H = H' := by
  cases H
  cases H'
  cases h1
  cases h2
  rfl

theorem mapCell_mapCell_symm_of (e : ReflectedGMS.Plane ≃ₜ ReflectedGMS.Plane) (K : Cell) :
    CellConfig.mapCell e (CellConfig.mapCell e.symm K) = K := by
  apply SetLike.coe_injective
  rw [CellConfig.coe_mapCell_eq_image, CellConfig.coe_mapCell_eq_image, Set.image_image]
  simp

theorem mapCell_symm_mapCell_of (e : ReflectedGMS.Plane ≃ₜ ReflectedGMS.Plane) (K : Cell) :
    CellConfig.mapCell e.symm (CellConfig.mapCell e K) = K := by
  apply SetLike.coe_injective
  rw [CellConfig.coe_mapCell_eq_image, CellConfig.coe_mapCell_eq_image, Set.image_image]
  simp

/-- The cells `f k`, `k ∈ ℤ`, of an injective family, with the conductance `m j k` between `f j` and `f k`. -/
def familyCellConfig (f : ℤ → Cell) (hf : Function.Injective f) (m : ℤ → ℤ → ℕ) : CellConfig := by
  classical
  refine ⟨Set.range f, ?_⟩
  intro A B
  exact if ha : A ∈ Set.range f then
    if hb : B ∈ Set.range f then
      (m ((Equiv.ofInjective f hf).symm ⟨A, ha⟩) ((Equiv.ofInjective f hf).symm ⟨B, hb⟩) : ℝ)
    else 0
    else 0

theorem familyCellConfig_c_apply (f : ℤ → Cell) (hf : Function.Injective f) (m : ℤ → ℤ → ℕ) (a b : ℤ) :
    (familyCellConfig f hf m).c (f a) (f b) = m a b := by
  classical
  show (if ha : f a ∈ Set.range f then
    if hb : f b ∈ Set.range f then
      (m ((Equiv.ofInjective f hf).symm ⟨f a, ha⟩) ((Equiv.ofInjective f hf).symm ⟨f b, hb⟩) : ℝ)
    else 0
    else 0) = m a b
  rw [dite_eq_left (Set.mem_range_self (f := f) a), dite_eq_left (Set.mem_range_self (f := f) b)]
  simp

theorem familyCellConfig_c_eq_zero (f : ℤ → Cell) (hf : Function.Injective f) (m : ℤ → ℤ → ℕ) {A B : Cell}
    (hAB : ¬ (A ∈ Set.range f ∧ B ∈ Set.range f)) : (familyCellConfig f hf m).c A B = 0 := by
  classical
  show (if ha : A ∈ Set.range f then
    if hb : B ∈ Set.range f then
      (m ((Equiv.ofInjective f hf).symm ⟨A, ha⟩) ((Equiv.ofInjective f hf).symm ⟨B, hb⟩) : ℝ)
    else 0
    else 0) = 0
  by_cases ha : A ∈ Set.range f
  · rw [dite_eq_left ha]
    exact dite_eq_right fun hb => hAB ⟨ha, hb⟩
  · exact dite_eq_right ha

/-- The image of the configuration of an injective family of cells under a linear isometry `e` is the
configuration of the image family, with the same conductances. -/
theorem isometryCellConfig_familyCellConfig (e : ReflectedGMS.Plane ≃ₗᵢ[ℝ] ReflectedGMS.Plane)
    (f f' : ℤ → Cell) (hf : Function.Injective f) (hf' : Function.Injective f')
    (hff : ∀ k, CellConfig.mapCell e.toHomeomorph (f k) = f' k) (m : ℤ → ℤ → ℕ) :
    isometryCellConfig e (familyCellConfig f hf m) = familyCellConfig f' hf' m := by
  have hinv : ∀ k, CellConfig.mapCell e.toHomeomorph.symm (f' k) = f k := fun k => by
    rw [← hff k, mapCell_symm_mapCell_of]
  have hpre : ∀ A : Cell, CellConfig.mapCell e.toHomeomorph.symm A ∈ Set.range f ↔ A ∈ Set.range f' := by
    intro A
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hff k, hk, mapCell_mapCell_symm_of]
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hinv k).symm⟩
  apply cellConfig_eq_of
  · show CellConfig.mapCell e.toHomeomorph '' Set.range f = Set.range f'
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hff)
  · funext A B
    show (familyCellConfig f hf m).c (CellConfig.mapCell e.toHomeomorph.symm A)
        (CellConfig.mapCell e.toHomeomorph.symm B) = (familyCellConfig f' hf' m).c A B
    by_cases hAB : A ∈ Set.range f' ∧ B ∈ Set.range f'
    · obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := hAB
      rw [hinv k, hinv l, familyCellConfig_c_apply, familyCellConfig_c_apply]
    · rw [familyCellConfig_c_eq_zero f' hf' m hAB, familyCellConfig_c_eq_zero f hf m]
      rwa [hpre, hpre]

/-- The quarter turn of the plane is multiplication by `i` in the complex coordinate. -/
theorem quarterTurn_repr (z : ℂ) :
    quarterTurn (Complex.orthonormalBasisOneI.repr z) =
      Complex.orthonormalBasisOneI.repr (Complex.I * z) := by
  ext i
  fin_cases i <;> simp

/-- The quarter turn of a cell of a curve is the cell of the rotated curve `t ↦ i η(t)`. -/
theorem mapCell_quarterTurn_euclideanCell (ε : ℝ) (c : ℝ → ℂ) (hc : Continuous c)
    (hc' : Continuous fun t => Complex.I * c t) (hε : 0 < ε) (k : ℤ) :
    CellConfig.mapCell quarterTurn.toHomeomorph (euclideanCell ε c hc hε k) =
      euclideanCell ε (fun t => Complex.I * c t) hc' hε k := by
  apply SetLike.coe_injective
  rw [CellConfig.coe_mapCell_eq_image, coe_euclideanCell, coe_euclideanCell]
  simp only [MatedCRT.cell, Set.image_image]
  exact Set.image_congr fun t _ => quarterTurn_repr (c t)

/-- The shifted unit cells of an area-parametrized curve as the configuration of an injective family. -/
theorem shiftedAreaCellConfig_eq_familyCellConfig {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ) :
    shiftedAreaCellConfig h hε θ m =
      familyCellConfig _ (shiftedEuclideanCell_injective h hε θ) m := rfl

/-- **The quarter turn of the shifted cells of a curve** are the shifted cells of the rotated curve `t ↦ i η(t)`,
with the same conductances. -/
theorem isometryCellConfig_quarterTurn_shiftedAreaCellConfig {μ μ' : Measure ℂ} {c : ℝ → ℂ}
    (h : IsAreaParametrized μ c) (h' : IsAreaParametrized μ' (fun t => Complex.I * c t))
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ) :
    isometryCellConfig quarterTurn (shiftedAreaCellConfig h hε θ m) =
      shiftedAreaCellConfig h' hε θ m := by
  rw [shiftedAreaCellConfig_eq_familyCellConfig, shiftedAreaCellConfig_eq_familyCellConfig]
  exact isometryCellConfig_familyCellConfig quarterTurn _ _ _ _
    (fun k => mapCell_quarterTurn_euclideanCell ε _ _ _ hε k) m

/-- An area parametrization of a curve gives one of the rotated curve `t ↦ i η(t)`, for the rotated measure. -/
theorem isAreaParametrized_quarterTurn {μ : Measure ℂ} {c : ℝ → ℂ} (h : IsAreaParametrized μ c) :
    IsAreaParametrized (μ.map fun z => Complex.I * z) (fun t => Complex.I * c t) := by
  obtain ⟨hc, h0, hs, hμ⟩ := h
  refine ⟨continuous_const.mul hc, ?_, ?_, ?_⟩
  · show Complex.I * c 0 = 0
    rw [h0, mul_zero]
  · intro w
    obtain ⟨t, ht⟩ := hs (-Complex.I * w)
    refine ⟨t, ?_⟩
    show Complex.I * c t = w
    rw [ht, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  · intro a b hab
    have hg : Continuous fun z : ℂ => Complex.I * z := continuous_const.mul continuous_id
    have hinj : Function.Injective fun z : ℂ => Complex.I * z := mul_right_injective₀ Complex.I_ne_zero
    have himg : (fun t => Complex.I * c t) '' Icc a b =
        (fun z : ℂ => Complex.I * z) '' (c '' Icc a b) := by
      rw [Set.image_image]
    have hcpt : IsCompact ((fun z : ℂ => Complex.I * z) '' (c '' Icc a b)) :=
      (isCompact_Icc.image hc).image hg
    rw [himg, Measure.map_apply hg.measurable hcpt.isClosed.measurableSet, Set.preimage_image_eq _ hinj]
    exact hμ a b hab

end QuarterTurnCells

/-! ### The configuration as a function of the data `((η, G), θ)` -/

section DataConfig

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

/-- The quarter turn `t ↦ i η(t)` of a planar curve. -/
def quarterTurnCurve (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  (⟨fun z => Complex.I * z, continuous_const.mul continuous_id⟩ : C(ℂ, ℂ)).comp c

theorem continuous_quarterTurnCurve : Continuous quarterTurnCurve :=
  ContinuousMap.continuous_postcomp _

/-- The configuration of the unit cells `η([x - 1 + θ, x + θ])` of a curve with the contour edge counts at mesh `1`
of the time-translated pair `t ↦ G(t + θ)`, read off the data `((η, G), θ)` (the empty configuration when `η` is
not parametrized by the area of any measure). -/
def shiftedDataCellConfig (s : (C(ℝ, ℂ) × Path2) × ℝ) : CellConfig := by
  classical
  exact if h : ∃ μ : Measure ℂ, IsAreaParametrized μ s.1.1 then
    shiftedAreaCellConfig h.choose_spec one_pos s.2
      (bmEdgeCount 1 (fun t => (s.1.2 (t + 1 * s.2)).1) (fun t => (s.1.2 (t + 1 * s.2)).2))
  else ⟨∅, fun _ _ => 0⟩

theorem shiftedDataCellConfig_eq {s : (C(ℝ, ℂ) × Path2) × ℝ} {μ : Measure ℂ}
    (h : IsAreaParametrized μ s.1.1) :
    shiftedDataCellConfig s = shiftedAreaCellConfig h one_pos s.2
      (bmEdgeCount 1 (fun t => (s.1.2 (t + 1 * s.2)).1) (fun t => (s.1.2 (t + 1 * s.2)).2)) := by
  unfold shiftedDataCellConfig
  exact dite_eq_left (show ∃ μ : Measure ℂ, IsAreaParametrized μ s.1.1 from ⟨μ, h⟩)

/-- The configuration of the rotated data is the quarter turn of the configuration of the data. -/
theorem shiftedDataCellConfig_quarterTurn {s : (C(ℝ, ℂ) × Path2) × ℝ} {μ : Measure ℂ}
    (h : IsAreaParametrized μ s.1.1) :
    shiftedDataCellConfig ((quarterTurnCurve s.1.1, s.1.2), s.2) =
      isometryCellConfig quarterTurn (shiftedDataCellConfig s) := by
  rw [shiftedDataCellConfig_eq (s := ((quarterTurnCurve s.1.1, s.1.2), s.2))
      (isAreaParametrized_quarterTurn h), shiftedDataCellConfig_eq h]
  exact (isometryCellConfig_quarterTurn_shiftedAreaCellConfig h (isAreaParametrized_quarterTurn h)
    one_pos s.2 _).symm

/-- The configuration of the data as a point of the GMS space (the point `H₀` when it is not a cell
configuration). -/
def shiftedDataGMS (H₀ : GMSSpace) (s : (C(ℝ, ℂ) × Path2) × ℝ) : GMSSpace := by
  classical
  exact if hv : (shiftedDataCellConfig s).IsCellConfiguration then ⟨_, hv⟩ else H₀

theorem shiftedDataGMS_eq {H₀ : GMSSpace} {s : (C(ℝ, ℂ) × Path2) × ℝ} {H : GMSSpace}
    (h : shiftedDataCellConfig s = H.1) : shiftedDataGMS H₀ s = H := by
  have hv : (shiftedDataCellConfig s).IsCellConfiguration := by
    rw [h]
    exact H.2
  unfold shiftedDataGMS
  rw [dite_eq_left hv]
  exact Subtype.ext h

end DataConfig

/-! ### Rotation invariance of the configuration -/

section ZeroCone

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Rotation invariance of the zero-cone curve with its boundary-length pair** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, lines 1212-1213: "the law of `(h, η)` is invariant under rotations about the origin"; written
answer `notes/fp-gaps/CODEX-MQ-sbl-30.md`, line 39, "M5": the zero-cone field law is rotation invariant by its
radial/lateral decomposition, the independent rooted imaginary-geometry curve law is rotation invariant by the
imaginary-geometry coordinate change and the uniform angle, and the area clock commutes with the quarter turn;
the quantum boundary lengths are invariant under rotations by the LQG coordinate change, Duplantier–Miller–Sheffield,
arXiv:1409.7055, Theorem 1.9). PENDING TRUTH CHECK.

For every measurable version `G` of the boundary-length pair of the zero-cone curve, the pair `(i η₀, G)` has the
law of `(η₀, G)`. -/
def ZeroConeBoundaryPairRotationLaw (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    P.map (fun ω => (quarterTurnCurve (η₀ ω), G ω)) = P.map (fun ω => (η₀ ω, G ω))

/-- **Rotation invariance of the shifted zero-cone configuration on a standard Borel sample space**
(arXiv:1705.11161, lines 1212-1213; written answer `notes/fp-gaps/CODEX-MQ-sbl-30.md`, line 39). Every realization
`F` is almost everywhere the configuration of the data `((η₀, G), θ)`, and its quarter turn is the configuration of
the rotated data `((i η₀, G), θ)`; the two data have the same law (`ZeroConeBoundaryPairRotationLaw`), so the law
of `F` and of its quarter turn agree (`map_eq_map_of_ae_eq_comp`). -/
theorem zeroConeConfigRotationInvariance [StandardBorelSpace Ω]
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hrot : ZeroConeBoundaryPairRotationLaw D hγ) : ZeroConeConfigRotationInvariance D hγ := by
  intro G F hF
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hPC : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have hP2 : PolishSpace Path2 := LatticeProb.polishSpace_continuousMap ℝ (ℝ × ℝ)
  obtain ⟨hGm, hGclock, hFae, hFeq⟩ := hF
  have hη₀ : Measurable η₀ := D.measurable_curves.2.2.1
  obtain ⟨p₀, -⟩ := hFeq.exists
  let d : Ω × ℝ → (C(ℝ, ℂ) × Path2) × ℝ := fun p => ((η₀ p.1, G p.1), p.2)
  let d' : Ω × ℝ → (C(ℝ, ℂ) × Path2) × ℝ := fun p => ((quarterTurnCurve (η₀ p.1), G p.1), p.2)
  have hg : Measurable fun ω => (η₀ ω, G ω) := hη₀.prodMk hGm
  have hg' : Measurable fun ω => (quarterTurnCurve (η₀ ω), G ω) :=
    (continuous_quarterTurnCurve.measurable.comp hη₀).prodMk hGm
  have hd : Measurable d := (hg.comp measurable_fst).prodMk measurable_snd
  have hd' : Measurable d' := (hg'.comp measurable_fst).prodMk measurable_snd
  have hlaw : ∀ g : Ω → C(ℝ, ℂ) × Path2, Measurable g →
      (P.prod zeroConePhase).map (fun p => (g p.1, p.2)) = (P.map g).prod zeroConePhase := by
    intro g hgm
    have h := Measure.map_prod_map P zeroConePhase hgm measurable_id
    rw [Measure.map_id] at h
    exact h.symm
  have hdd : (P.prod zeroConePhase).map d' = (P.prod zeroConePhase).map d := by
    have h1 : (P.prod zeroConePhase).map d' =
        (P.map fun ω => (quarterTurnCurve (η₀ ω), G ω)).prod zeroConePhase := hlaw _ hg'
    have h2 : (P.prod zeroConePhase).map d = (P.map fun ω => (η₀ ω, G ω)).prod zeroConePhase := hlaw _ hg
    rw [h1, h2, hrot G ⟨hGm, hGclock⟩]
  have hF₁ : F =ᵐ[P.prod zeroConePhase] shiftedDataGMS (F p₀) ∘ d := by
    filter_upwards [hFeq] with p hp
    obtain ⟨hpa, hpeq⟩ := hp
    exact (shiftedDataGMS_eq ((shiftedDataCellConfig_eq (s := d p) hpa).trans hpeq.symm)).symm
  have hF₂ : isometryGMS quarterTurn ∘ F =ᵐ[P.prod zeroConePhase] shiftedDataGMS (F p₀) ∘ d' := by
    filter_upwards [hFeq] with p hp
    obtain ⟨hpa, hpeq⟩ := hp
    have hc : shiftedDataCellConfig (d p) = (F p).1 :=
      (shiftedDataCellConfig_eq (s := d p) hpa).trans hpeq.symm
    show isometryGMS quarterTurn (F p) = shiftedDataGMS (F p₀) (d' p)
    refine (shiftedDataGMS_eq ?_).symm
    show shiftedDataCellConfig ((quarterTurnCurve (d p).1.1, (d p).1.2), (d p).2) =
      isometryCellConfig quarterTurn (F p).1
    rw [shiftedDataCellConfig_quarterTurn (s := d p) hpa, hc]
  have hmain := map_eq_map_of_ae_eq_comp hd' hd hdd
    ((measurable_isometryGMS quarterTurn).comp_aemeasurable hFae) hFae (shiftedDataGMS (F p₀)) hF₂ hF₁
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_isometryGMS quarterTurn).aemeasurable hFae]
  exact hmain

end ZeroCone

end MatedCRT.GMS310Transfer
