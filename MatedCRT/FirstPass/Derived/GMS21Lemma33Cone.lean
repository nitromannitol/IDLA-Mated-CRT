import MatedCRT.FirstPass.Derived.GMS21Lemma33
import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLP
import MatedCRT.FirstPass.Derived.ConeLQGAreaMeasurable
import MatedCRT.FirstPass.Derived.IGCurveScaleLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Bundle
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# Lemma 3.3 of Gwynne–Miller–Sheffield for a mating-of-trees coupling

Gwynne–Miller–Sheffield (arXiv:1705.11161), Lemma 3.3, in the form used in the proof of Theorem 3.4, case 1: the
local configurations near the annulus `B_R(0) \ closedBall 0 α` of the `γ`-quantum cone at mesh `1/n` (phase `0`)
and of the `0`-quantum cone read on the shifted lattice `n⁻¹ ℤ + n⁻¹ θ` (`θ` an independent uniform phase) have
uniformly mutually absolutely continuous laws as `n → ∞` (`CouplingLocalConfigUMAC`).

The argument compares both cones through the curve `ηL` (space-filling SLE parametrized by Lebesgue measure) and
two random offsets. Write `μ` for the `γ`-LQG area measure of the cone field. Fix cutoffs `a > 0` and
`0 < δ < M`.

* **Outer data.** The curve and the area measure restricted to the annulus `{δ < |z| < M}`
  (`annulusOuterData`).
* **Offsets.** The signed quantum times `C₋ = -μ(ηL([-a, 0]))` and `C₊ = μ(ηL([0, a]))` of the inner endpoints
  `ηL(∓a)` (`quantumTimeOffsets`). At mesh `1/n` with phase `θ` the cell endpoints on the two time blocks of `ηL`
  outside `[-a, a]` sit at relative clock values determined by the residues `fract(n C_± - θ)`
  (`offsetResidues`).

Three inputs, each a named hypothesis of this file with its source (all PENDING TRUTH CHECK):

* `ConeAnnulusAreaLawEquivalence`: the laws of the outer data of the two cones are mutually absolutely
  continuous;
* `ConeOffsetDensity`: given the outer data, the two offsets have a joint Lebesgue density;
* `ConeConfigReconstruction`: for every `ε > 0` there are cutoffs and an event of the curve of probability at least
  `1 - ε` on which, with probability tending to one, the local configuration of either cone at mesh `1/n` is the
  same Borel function of the outer data and the residues.

From these, `couplingLocalConfigUMAC_of_lemma33Inputs` proves `CouplingLocalConfigUMAC D hγ` through the general
form of Lemma 3.3 (`localConfigUniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction`): the
`γ`-cone marked phase vector has phase `0`, the `0`-cone marked phase vector has the independent uniform phase of
`P ⊗ Unif[0, 1]` (`absolutelyContinuous_indepUniformPhase`).

## Main statements

* `ConeAnnulusAreaLawEquivalence`, `ConeOffsetDensity`, `IsOffsetReconstruction`, `ConeConfigReconstruction`.
* `couplingLocalConfigUMAC_of_lemma33Inputs`: Lemma 3.3 for every mating-of-trees coupling from the three inputs.
* `forall_couplingLocalConfigUMAC_of_lemma33Inputs`: the same for every `γ ∈ (0, 2)` and every coupling, in the
  form of the premise `h33` of the canonical Tutte assembly (`GMS21CanonicalTutteLP.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open LatticeProb (CountablePhaseSpace measurableEmbedding_countablePhase_inject)

/-! ### Slices of marked phase vectors with two coordinates -/

section Slices

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

theorem comap_sigmaMk_map_self {P : Measure Ω} {K : ℕ} {v : Ω → E × (Fin K → ℝ)}
    (hv : AEMeasurable v P) :
    (P.map fun ω => (⟨K, v ω⟩ : CountablePhaseSpace E)).comap
      (@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) K) = P.map v := by
  have he := measurableEmbedding_countablePhase_inject (E := E) K
  have hcomp : (fun ω => (⟨K, v ω⟩ : CountablePhaseSpace E)) =
      (@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) K) ∘ v := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable he.measurable.aemeasurable hv]
  exact he.comap_map _

theorem comap_sigmaMk_map_of_ne {P : Measure Ω} {K k : ℕ} (hk : k ≠ K) {v : Ω → E × (Fin K → ℝ)}
    (hv : AEMeasurable v P) :
    (P.map fun ω => (⟨K, v ω⟩ : CountablePhaseSpace E)).comap
      (@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) k) = 0 := by
  have he := measurableEmbedding_countablePhase_inject (E := E) k
  have hae : AEMeasurable (fun ω => (⟨K, v ω⟩ : CountablePhaseSpace E)) P :=
    (measurableEmbedding_countablePhase_inject (E := E) K).measurable.comp_aemeasurable hv
  ext s hs
  rw [he.comap_apply, Measure.coe_zero, Pi.zero_apply,
    Measure.map_apply_of_aemeasurable hae (he.measurableSet_image' hs)]
  convert measure_empty (μ := P)
  ext ω
  simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro x _ hx
  exact hk (congrArg Sigma.fst hx)

/-- **Slices of a marked phase vector with a constant number of coordinates.** If the law of `v` is absolutely
continuous with respect to the law of its mark times Lebesgue measure, then so is every slice of the law of
`⟨K, v⟩`. -/
theorem absolutelyContinuous_slice {P : Measure Ω} {K : ℕ} {v : Ω → E × (Fin K → ℝ)}
    (hv : AEMeasurable v P)
    (hac : P.map v ≪ ((P.map v).map Prod.fst).prod (volume : Measure (Fin K → ℝ))) (k : ℕ) :
    let ν := (P.map fun ω => (⟨K, v ω⟩ : CountablePhaseSpace E)).comap
      (@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ)) := by
  intro ν
  rcases eq_or_ne k K with rfl | hk
  · have hν : ν = P.map v := comap_sigmaMk_map_self hv
    rw [hν]
    exact hac
  · have hν : ν = 0 := comap_sigmaMk_map_of_ne hk hv
    rw [hν]
    exact Measure.AbsolutelyContinuous.zero _

end Slices

/-! ### Absolute continuity of the coordinates given the mark -/

section MarkedLaws

theorem absolutelyContinuous_map_prodMap_fst {Y Y' : Type*} [MeasurableSpace Y] [MeasurableSpace Y']
    {K : ℕ} {W : Measure (Y × (Fin K → ℝ))} [IsFiniteMeasure W]
    (hW : W ≪ (W.map Prod.fst).prod (volume : Measure (Fin K → ℝ))) {f : Y → Y'} (hf : Measurable f) :
    W.map (Prod.map f id) ≪
      ((W.map (Prod.map f id)).map Prod.fst).prod (volume : Measure (Fin K → ℝ)) := by
  have hg : Measurable (Prod.map f (id : (Fin K → ℝ) → (Fin K → ℝ))) := hf.prodMap measurable_id
  have h1 : (W.map (Prod.map f id)).map Prod.fst = (W.map Prod.fst).map f := by
    rw [Measure.map_map measurable_fst hg, Measure.map_map hf measurable_fst]
    rfl
  have h2 := Measure.map_prod_map (W.map Prod.fst) (volume : Measure (Fin K → ℝ)) hf measurable_id
  rw [Measure.map_id] at h2
  rw [h1, h2]
  exact hW.map hg

/-- Rearranging `((y, c), θ) ↦ ((y, θ), c)` carries `(A ⊗ Leb) ⊗ U` to `(A ⊗ U) ⊗ Leb`. -/
theorem measurePreserving_rearrange {Y : Type*} [MeasurableSpace Y] {K : ℕ} (A : Measure Y) [SFinite A]
    (U : Measure ℝ) [SFinite U] :
    MeasurePreserving (fun q : (Y × (Fin K → ℝ)) × ℝ => ((q.1.1, q.2), q.1.2))
      ((A.prod (volume : Measure (Fin K → ℝ))).prod U) ((A.prod U).prod (volume : Measure (Fin K → ℝ))) := by
  have e1 := measurePreserving_prodAssoc A (volume : Measure (Fin K → ℝ)) U
  have e2 : MeasurePreserving (Prod.map (id : Y → Y) (Prod.swap : (Fin K → ℝ) × ℝ → ℝ × (Fin K → ℝ)))
      (A.prod ((volume : Measure (Fin K → ℝ)).prod U)) (A.prod (U.prod (volume : Measure (Fin K → ℝ)))) :=
    (MeasurePreserving.id A).prod Measure.measurePreserving_swap
  have e3 := MeasurePreserving.symm _ (measurePreserving_prodAssoc A U (volume : Measure (Fin K → ℝ)))
  exact e3.comp (e2.comp e1)

/-- **An independent phase in the mark.** If `W ≪ (W.map fst) ⊗ Leb`, then the law of `((y, θ), c)` under
`W ⊗ U` is absolutely continuous with respect to the law of its mark `(y, θ)` times Lebesgue measure. -/
theorem absolutelyContinuous_indepPhase {Y : Type*} [MeasurableSpace Y] {K : ℕ}
    {W : Measure (Y × (Fin K → ℝ))} [IsFiniteMeasure W]
    (hW : W ≪ (W.map Prod.fst).prod (volume : Measure (Fin K → ℝ))) (U : Measure ℝ) [IsFiniteMeasure U] :
    (W.prod U).map (fun q => ((q.1.1, q.2), q.1.2)) ≪
      (((W.prod U).map (fun q => ((q.1.1, q.2), q.1.2))).map Prod.fst).prod
        (volume : Measure (Fin K → ℝ)) := by
  have hr : Measurable (fun q : (Y × (Fin K → ℝ)) × ℝ => ((q.1.1, q.2), q.1.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hfst : ((W.prod U).map (fun q : (Y × (Fin K → ℝ)) × ℝ => ((q.1.1, q.2), q.1.2))).map Prod.fst =
      (W.map Prod.fst).prod U := by
    rw [Measure.map_map measurable_fst hr]
    have h := Measure.map_prod_map W U measurable_fst measurable_id
    rw [Measure.map_id] at h
    rw [h]
    rfl
  rw [hfst, ← (measurePreserving_rearrange (W.map Prod.fst) U).map_eq]
  exact (hW.prod (Measure.AbsolutelyContinuous.refl U)).map hr

theorem aemeasurable_comp_fst_prod {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsFiniteMeasure P] {U : Measure ℝ} [IsFiniteMeasure U] {w : Ω → β} (hw : AEMeasurable w P) :
    AEMeasurable (fun p : Ω × ℝ => w p.1) (P.prod U) :=
  hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst

theorem map_comp_fst_prod {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsFiniteMeasure P] {U : Measure ℝ} [IsProbabilityMeasure U] {w : Ω → β} (hw : AEMeasurable w P) :
    (P.prod U).map (fun p => w p.1) = P.map w := by
  have hfst : (P.prod U).map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h := AEMeasurable.map_map_of_aemeasurable (μ := P.prod U) (f := Prod.fst) (g := w)
    (by rw [hfst]; exact hw) measurable_fst.aemeasurable
  rw [hfst] at h
  exact h.symm

theorem map_prod_fst_pair {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsFiniteMeasure P] (U : Measure ℝ) [IsFiniteMeasure U] {w : Ω → β} (hw : AEMeasurable w P) :
    (P.prod U).map (fun p => (w p.1, p.2)) = (P.map w).prod U := by
  have hae : (fun p : Ω × ℝ => (w p.1, p.2)) =ᵐ[P.prod U] Prod.map (hw.mk w) id := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := U)).ae_eq_comp hw.ae_eq_mk]
      with p hp
    simp only [Function.comp_apply] at hp
    show (w p.1, p.2) = (hw.mk w p.1, p.2)
    rw [hp]
  rw [Measure.map_congr hae, ← Measure.map_prod_map P U hw.measurable_mk measurable_id, Measure.map_id,
    Measure.map_congr hw.ae_eq_mk.symm]

/-- **Phase zero.** If the joint law of the outer data `o` and the coordinates `c` is absolutely continuous with
respect to the law of `o` times Lebesgue measure, the slices of the law of `⟨2, ((o, 0), c)⟩` are absolutely
continuous with respect to the law of their mark times Lebesgue measure. -/
theorem absolutelyContinuous_phaseZero {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} [IsFiniteMeasure P] {o : Ω → Y} {c : Ω → Fin 2 → ℝ} (ho : AEMeasurable o P)
    (hc : AEMeasurable c P) (hac : P.map (fun ω => (o ω, c ω)) ≪ (P.map o).prod volume) (k : ℕ) :
    let ν := (P.map fun ω => (⟨2, ((o ω, (0 : ℝ)), c ω)⟩ : CountablePhaseSpace (Y × ℝ))).comap
      (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ)) := by
  have hw : AEMeasurable (fun ω => (o ω, c ω)) P := ho.prodMk hc
  have hf : Measurable fun y : Y => (y, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have hg : Measurable (Prod.map (fun y : Y => (y, (0 : ℝ))) (id : (Fin 2 → ℝ) → (Fin 2 → ℝ))) :=
    hf.prodMap measurable_id
  have hv : AEMeasurable (fun ω => ((o ω, (0 : ℝ)), c ω)) P := hg.comp_aemeasurable hw
  have hW : P.map (fun ω => (o ω, c ω)) ≪
      ((P.map fun ω => (o ω, c ω)).map Prod.fst).prod (volume : Measure (Fin 2 → ℝ)) := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hw]
    exact hac
  have hmap : P.map (fun ω => ((o ω, (0 : ℝ)), c ω)) =
      (P.map fun ω => (o ω, c ω)).map (Prod.map (fun y : Y => (y, (0 : ℝ))) id) := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hw]
    rfl
  have hac' : P.map (fun ω => ((o ω, (0 : ℝ)), c ω)) ≪
      ((P.map fun ω => ((o ω, (0 : ℝ)), c ω)).map Prod.fst).prod (volume : Measure (Fin 2 → ℝ)) := by
    rw [hmap]
    exact absolutelyContinuous_map_prodMap_fst hW hf
  exact absolutelyContinuous_slice hv hac' k

/-- **Independent uniform phase.** If the joint law of the outer data `o` and the coordinates `c` under `P` is
absolutely continuous with respect to the law of `o` times Lebesgue measure, then under `P ⊗ U` the slices of the
law of `⟨2, ((o, θ), c)⟩` (`θ` the second coordinate) are absolutely continuous with respect to the law of their
mark `(o, θ)` times Lebesgue measure. -/
theorem absolutelyContinuous_indepUniformPhase {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} [IsFiniteMeasure P] {U : Measure ℝ} [IsFiniteMeasure U] {o : Ω → Y} {c : Ω → Fin 2 → ℝ}
    (ho : AEMeasurable o P) (hc : AEMeasurable c P)
    (hac : P.map (fun ω => (o ω, c ω)) ≪ (P.map o).prod volume) (k : ℕ) :
    let ν := ((P.prod U).map fun p => (⟨2, ((o p.1, p.2), c p.1)⟩ : CountablePhaseSpace (Y × ℝ))).comap
      (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ)) := by
  have hw : AEMeasurable (fun ω => (o ω, c ω)) P := ho.prodMk hc
  have hr : Measurable (fun q : (Y × (Fin 2 → ℝ)) × ℝ => ((q.1.1, q.2), q.1.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hf : AEMeasurable (fun p : Ω × ℝ => ((fun ω => (o ω, c ω)) p.1, p.2)) (P.prod U) :=
    (aemeasurable_comp_fst_prod hw).prodMk measurable_snd.aemeasurable
  have hv : AEMeasurable (fun p : Ω × ℝ => ((o p.1, p.2), c p.1)) (P.prod U) := hr.comp_aemeasurable hf
  have hW : P.map (fun ω => (o ω, c ω)) ≪
      ((P.map fun ω => (o ω, c ω)).map Prod.fst).prod (volume : Measure (Fin 2 → ℝ)) := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hw]
    exact hac
  have hmap : (P.prod U).map (fun p : Ω × ℝ => ((o p.1, p.2), c p.1)) =
      ((P.map fun ω => (o ω, c ω)).prod U).map
        (fun q : (Y × (Fin 2 → ℝ)) × ℝ => ((q.1.1, q.2), q.1.2)) := by
    rw [← map_prod_fst_pair U hw, AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hf]
    rfl
  have hac' : (P.prod U).map (fun p : Ω × ℝ => ((o p.1, p.2), c p.1)) ≪
      (((P.prod U).map fun p : Ω × ℝ => ((o p.1, p.2), c p.1)).map Prod.fst).prod
        (volume : Measure (Fin 2 → ℝ)) := by
    rw [hmap]
    exact absolutelyContinuous_indepPhase hW U
  exact absolutelyContinuous_slice hv hac' k

/-- **The laws of the number of coordinates and the outer data.** If `countOuter (Zᵢ ω) = (2, oᵢ ω)` and the laws of
the outer data are absolutely continuous, so are the laws of `countOuter ∘ Zᵢ`. -/
theorem absolutelyContinuous_map_countOuter {Ω₁ Ω₂ Y : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Y] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {Z₁ : Ω₁ → CountablePhaseSpace (Y × ℝ)}
    {Z₂ : Ω₂ → CountablePhaseSpace (Y × ℝ)} {o₁ : Ω₁ → Y} {o₂ : Ω₂ → Y} (hZ₁ : AEMeasurable Z₁ P₁)
    (hZ₂ : AEMeasurable Z₂ P₂) (ho₁ : AEMeasurable o₁ P₁) (ho₂ : AEMeasurable o₂ P₂)
    (h₁ : ∀ ω, countOuter (Z₁ ω) = (2, o₁ ω)) (h₂ : ∀ ω, countOuter (Z₂ ω) = (2, o₂ ω))
    (hac : P₁.map o₁ ≪ P₂.map o₂) :
    (P₁.map Z₁).map countOuter ≪ (P₂.map Z₂).map countOuter := by
  have hg : Measurable fun y : Y => ((2 : ℕ), y) := measurable_const.prodMk measurable_id
  rw [AEMeasurable.map_map_of_aemeasurable measurable_countOuter.aemeasurable hZ₁,
    AEMeasurable.map_map_of_aemeasurable measurable_countOuter.aemeasurable hZ₂]
  have e₁ : countOuter ∘ Z₁ = (fun y : Y => ((2 : ℕ), y)) ∘ o₁ := funext h₁
  have e₂ : countOuter ∘ Z₂ = (fun y : Y => ((2 : ℕ), y)) ∘ o₂ := funext h₂
  rw [e₁, e₂, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable ho₁,
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable ho₂]
  exact hac.map hg

end MarkedLaws

/-! ### Outer data and offsets of a quantum cone -/

/-- The `γ`-LQG area measure of the cone field `coneField X (coneRadial γ β B B')` at `ω` (`β = γ`: the `γ`-quantum
cone; `β = 0`: the `0`-quantum cone): the vague limit of its dyadic area approximations. -/
def quantumConeArea (γ β : ℝ) {Ω : Type*} (X : Ω → Field) (B B' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  MatedCRTHarmonic.CellScaling.lqgArea γ
    (coneField (X ω) (coneRadial γ β (fun t => B t ω) (fun t => B' t ω)))

/-- The open annulus `{δ < |z| < M}`. -/
def offsetOuterAnnulus (δ M : ℝ) : Set ℂ := ball (0 : ℂ) M \ closedBall (0 : ℂ) δ

theorem measurableSet_offsetOuterAnnulus (δ M : ℝ) : MeasurableSet (offsetOuterAnnulus δ M) :=
  measurableSet_ball.diff measurableSet_closedBall

theorem measurable_restrict_of_measurableSet {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable fun μ : Measure ℂ => μ.restrict s :=
  Measure.measurable_of_measurable_coe _ fun t ht => by
    simp only [Measure.restrict_apply ht]
    exact Measure.measurable_coe (ht.inter hs)

/-- **The outer data**: the curve and the area measure restricted to the annulus `{δ < |z| < M}`. -/
def annulusOuterData (e : C(ℝ, ℂ)) (μ : Measure ℂ) (δ M : ℝ) : C(ℝ, ℂ) × Measure ℂ :=
  (e, μ.restrict (offsetOuterAnnulus δ M))

/-- **The two offsets**: the signed quantum times `C₋ = -μ(e([-a, 0]))` and `C₊ = μ(e([0, a]))` of the inner
endpoints `e(-a)` and `e(a)` of the two time blocks. -/
def quantumTimeOffsets (e : C(ℝ, ℂ)) (μ : Measure ℂ) (a : ℝ) : Fin 2 → ℝ :=
  ![-(μ (e '' Icc (-a) 0)).toReal, (μ (e '' Icc 0 a)).toReal]

/-- The marked phase vector `⟨2, ((outer data, θ), (C₋, C₊))⟩`. -/
def offsetPhaseVector (θ : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (a δ M : ℝ) :
    CountablePhaseSpace ((C(ℝ, ℂ) × Measure ℂ) × ℝ) :=
  ⟨2, ((annulusOuterData e μ δ M, θ), quantumTimeOffsets e μ a)⟩

/-- The outer data with the residues `fract(n C_± - θ)` of the offsets at mesh `1/n` with phase `θ`. -/
def offsetResidues (n : ℕ) (θ : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (a δ M : ℝ) :
    CountablePhaseSpace (C(ℝ, ℂ) × Measure ℂ) :=
  ⟨2, (annulusOuterData e μ δ M, fun i => Int.fract ((n : ℝ) * quantumTimeOffsets e μ a i - θ))⟩

/-! ### The three inputs -/

/-- **The laws of the area measures of the `γ`-quantum cone and the `0`-quantum cone on a bounded annulus are
mutually absolutely continuous, jointly with an independent curve.** Let `X`, `X₀` be whole-plane GFFs and
`B, B', B₀, B₀'` standard Brownian motions with the independence structure of the cone data, so that
`coneField X (coneRadial γ γ B B')` is a `γ`-quantum cone and `coneField X₀ (coneRadial γ 0 B₀ B₀')` a
`0`-quantum cone (circle-average embeddings), and let `e` be a random curve independent of these data. Then for
`0 < δ < M` the laws of `(e, μ_γ|{δ < |z| < M})` and `(e, μ_0|{δ < |z| < M})` are mutually absolutely continuous.

Source: the answer to MQ-sbl-18, section "The field laws on a bounded annulus"; Gwynne–Miller–Sheffield
(arXiv:1705.11161) §2.3.1 (definition of the quantum cones by their radial and lateral parts); Miller–Sheffield,
Imaginary geometry I (arXiv:1201.1496), Proposition 3.4 (local absolute continuity of GFFs, p. 59);
Duplantier–Miller–Sheffield (arXiv:1409.7055), Definition 4.10. In the radial decomposition the lateral parts have
the same law; inside the unit circle the radial parts are Brownian motions with drifts `γ` and `0` on a bounded
time interval, outside they are Brownian motions with drift `Q - β > 0` conditioned to stay positive, both with a
positive density with respect to a three-dimensional Bessel process on a bounded time interval. PENDING TRUTH
CHECK. -/
def ConeAnnulusAreaLawEquivalence (γ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X X₀ : Ω → Field)
    (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (e : Ω → C(ℝ, ℂ)), γ ∈ Ioo (0 : ℝ) 2 →
    LQGMetric.IsWholePlaneGFF X P → LQGMetric.IsWholePlaneGFF X₀ P →
    IsBrownianReal B P → IsBrownianReal B' P → IsBrownianReal B₀ P → IsBrownianReal B₀' P →
    (IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) →
    (IndepFun X₀ (fun ω => ((fun t => B₀ t ω), (fun t => B₀' t ω))) P ∧
      IndepFun (fun ω t => B₀ t ω) (fun ω t => B₀' t ω) P) →
    Measurable e →
    IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω, (fun t => B₀ t ω),
      (fun t => B₀' t ω))) P →
    ∀ δ M : ℝ, 0 < δ → δ < M →
      P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ γ X B B' ω) δ M) ≪
          P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) δ M) ∧
        P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) δ M) ≪
          P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ γ X B B' ω) δ M)

/-- **Given the outer data, the two offsets have a joint Lebesgue density**, for the `γ`-quantum cone and for the
`0`-quantum cone of a mating-of-trees coupling: for `a > 0` and `0 < δ < M` the offsets
`(-μ(ηL([-a, 0])), μ(ηL([0, a])))` are random variables, and the joint law of the outer data
`(ηL, μ|{δ < |z| < M})` and the offsets is absolutely continuous with respect to the law of the outer data times
Lebesgue measure on `ℝ²`.

Source: the answer to MQ-sbl-18, section "Two offsets and their conditional density". Two disjoint rational disks
in `B_δ(0) \ {0}`, visited by `ηL` only during `(-a, 0)` and `(0, a)` respectively, carry smooth bumps `f_±`; the
field splits as `h_* + ξ₋ f₋ + ξ₊ f₊` with independent standard normal coefficients independent of `h_*` and of
`ηL` (Miller–Sheffield, Imaginary geometry IV (arXiv:1302.4738), §2.2.1); the outer data are a function of `h_*`
and `ηL`, and by Weyl scaling (Bou-Rabee–Gwynne, arXiv:2211.04891, Fact 2.2(III)) the mass of each gap is a `C¹`
strictly increasing function of its own coefficient. PENDING TRUTH CHECK. -/
def ConeOffsetDensity (γ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2},
    IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → γ ∈ Ioo (0 : ℝ) 2 →
    ∀ a δ M : ℝ, 0 < a → 0 < δ → δ < M →
      (AEMeasurable (fun ω => quantumTimeOffsets (ηL ω) (quantumConeArea γ γ X B B' ω) a) P ∧
        P.map (fun ω => (annulusOuterData (ηL ω) (quantumConeArea γ γ X B B' ω) δ M,
            quantumTimeOffsets (ηL ω) (quantumConeArea γ γ X B B' ω) a)) ≪
          (P.map fun ω => annulusOuterData (ηL ω) (quantumConeArea γ γ X B B' ω) δ M).prod volume) ∧
      (AEMeasurable (fun ω => quantumTimeOffsets (ηL ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) a) P ∧
        P.map (fun ω => (annulusOuterData (ηL ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) δ M,
            quantumTimeOffsets (ηL ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) a)) ≪
          (P.map fun ω => annulusOuterData (ηL ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) δ M).prod volume)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The configurations near the annulus `B_R(0) \ closedBall 0 α` are recovered from the outer data and the
residues**, for cutoffs `a > 0`, `0 < δ < M`, an event `E` of the curve of probability at least `1 - ε` and Borel
maps `Ψ n`: on `{ηL ∈ E}`, with probability tending to one, the local configuration of the `γ`-quantum cone at mesh
`1/n` (phase `0`) and of the `0`-quantum cone on the shifted lattice `n⁻¹ ℤ + n⁻¹ θ` are `Ψ n` of the outer data
`(ηL, μ|{δ < |z| < M})` and the residues `fract(n C_± - θ)` of the offsets. -/
structure IsOffsetReconstruction (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (G : Ω → Path2) (α R : ℝ) (ε : ℝ≥0∞) (a δ M : ℝ) (E : Set C(ℝ, ℂ))
    (Ψ : ℕ → CountablePhaseSpace (C(ℝ, ℂ) × Measure ℂ) → LocalConfig) : Prop where
  pos_a : 0 < a
  pos_δ : 0 < δ
  δ_lt_M : δ < M
  measurableSet_event : MeasurableSet E
  event_compl_le : P {ω | ηL ω ∉ E} ≤ ε
  measurable_recon : ∀ n, Measurable (Ψ n)
  recon_cone : Tendsto (fun n : ℕ => P {ω | ηL ω ∈ E ∧
    localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (coneConfigData η bm n ω)) ≠
      Ψ n (offsetResidues n 0 (ηL ω) (quantumConeArea γ γ X B B' ω) a δ M)}) atTop (𝓝 0)
  recon_zeroCone : Tendsto (fun n : ℕ => (P.prod zeroConePhase) {p | ηL p.1 ∈ E ∧
    localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (vertexData (1 / (n : ℝ)) (zeroConeShiftedData η₀ G n p)) ≠
      Ψ n (offsetResidues n p.2 (ηL p.1) (quantumConeArea γ 0 X₀ B₀ B₀' p.1) a δ M)}) atTop (𝓝 0)

end Coupling

/-- **Recovering the local configurations from the outer data and the residues** (the proof of Lemma 3.3 of
Gwynne–Miller–Sheffield with cutoffs): for every mating-of-trees coupling, every measurable version `G` of the
boundary-length pair of the zero-cone curve, all `0 < α < R` and `ε > 0` there are cutoffs, an event of the curve of
probability at least `1 - ε` and Borel maps with `IsOffsetReconstruction`.

Source: the answer to MQ-sbl-18, sections "Two offsets and their conditional density" (choice of the cutoffs
`a, L, δ, M` and of the curve event: Duplantier–Miller–Sheffield (arXiv:1409.7055) §8.2, Lemmas 8.8 and 8.14;
Gwynne–Miller–Sheffield §§2.2, 2.5) and "Recovering the formal configuration" (cells from the curve and the clock on
each time block, time order with the negative block first, edge counts by the frontier description in the proof of
Gwynne–Miller–Sheffield Proposition 2.2 (arXiv:1705.11161, p. 18-19, Figure 7) and the conductances (3.1); no
equality-only edges almost surely: Berestycki–Gwynne (arXiv:2003.10320) §2.3, (2.3)-(2.4)); Gwynne–Miller–Sheffield,
proof of Lemma 3.3 (p. 24-25). PENDING TRUTH CHECK. -/
def ConeConfigReconstruction (γ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (G : Ω → Path2), IsZeroConeBoundaryPair D hγ G →
    ∀ α R : ℝ, 0 < α → α < R → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (a δ M : ℝ) (E : Set C(ℝ, ℂ)) (Ψ : ℕ → CountablePhaseSpace (C(ℝ, ℂ) × Measure ℂ) → LocalConfig),
        IsOffsetReconstruction D G α R ε a δ M E Ψ

/-! ### Lemma 3.3 for a mating-of-trees coupling -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem measurable_coneConfigData (hη : Measurable η) (hbm : Measurable bm) (n : ℕ) :
    Measurable (coneConfigData η bm n) :=
  hη.prodMk (measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k =>
    (measurable_bmEdgeCount_path (1 / (n : ℝ)) j k).comp hbm)

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield for a mating-of-trees coupling** (arXiv:1705.11161, p. 24, in the form
used in the proof of Theorem 3.4, case 1): from the comparison of the laws of the outer data
(`ConeAnnulusAreaLawEquivalence`), the conditional density of the two offsets (`ConeOffsetDensity`) and the
reconstruction of the local configurations (`ConeConfigReconstruction`), the laws of the local configurations of the
`γ`-quantum cone (phase `0`) and of the shifted `0`-quantum cone (independent uniform phase) near every annulus
`B_R(0) \ closedBall 0 α` are uniformly mutually absolutely continuous as `n → ∞`. -/
theorem couplingLocalConfigUMAC_of_lemma33Inputs (h1 : ConeAnnulusAreaLawEquivalence γ)
    (h2 : ConeOffsetDensity γ) (h3 : ConeConfigReconstruction γ)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    CouplingLocalConfigUMAC D hγ := by
  intro G hG
  have hP := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hη : Measurable η := D.measurable_curves.2.1
  have hη₀ : Measurable η₀ := D.measurable_curves.2.2.1
  have hbm : Measurable bm := D.measurable_curves.2.2.2
  have hAγ : AEMeasurable (quantumConeArea γ γ X B B') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMSCase.aemeasurable_coneField D hγ)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ)
  have hA0 : AEMeasurable (quantumConeArea γ 0 X₀ B₀ B₀') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMS4.aemeasurable_prop48ZeroConeField D)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ)
  have hout : ∀ A : Ω → Measure ℂ, AEMeasurable A P → ∀ δ M : ℝ,
      AEMeasurable (fun ω => annulusOuterData (ηL ω) (A ω) δ M) P := fun A hA δ M =>
    hηL.aemeasurable.prodMk
      ((measurable_restrict_of_measurableSet (measurableSet_offsetOuterAnnulus δ M)).comp_aemeasurable hA)
  have hL1 := h1 P X X₀ B B' B₀ B₀' ηL hγ D.gff D.gff₀ D.bm_B D.bm_B' D.bm_B₀ D.bm_B₀' D.indep_cone
    D.indep_cone₀ hηL (Sec1.indepFun_igCurve_cone D)
  have hc : ∀ α R : ℝ, ∀ m : ℕ, ∃ (a δ M : ℝ) (E : Set C(ℝ, ℂ))
      (Ψ : ℕ → CountablePhaseSpace (C(ℝ, ℂ) × Measure ℂ) → LocalConfig),
      0 < α → α < R → IsOffsetReconstruction D G α R ((m : ℝ≥0∞) + 1)⁻¹ a δ M E Ψ := by
    intro α R m
    by_cases hαR : 0 < α ∧ α < R
    · obtain ⟨a, δ, M, E, Ψ, hrec⟩ := h3 D hγ G hG α R hαR.1 hαR.2 ((m : ℝ≥0∞) + 1)⁻¹
        (ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩))
      exact ⟨a, δ, M, E, Ψ, fun _ _ => hrec⟩
    · exact ⟨1, 1, 2, univ, fun _ _ => (0, 0, 0), fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hαR⟩
  choose a δ M E Ψ hrec using hc
  refine localConfigUniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction
    (Y := fun _ _ _ => C(ℝ, ℂ) × Measure ℂ)
    (fun α R m ω => offsetPhaseVector 0 (ηL ω) (quantumConeArea γ γ X B B' ω) (a α R m) (δ α R m) (M α R m))
    (fun α R m p => offsetPhaseVector p.2 (ηL p.1) (quantumConeArea γ 0 X₀ B₀ B₀' p.1) (a α R m) (δ α R m)
      (M α R m))
    Ψ (fun α R m => {x | x.2.1 ∈ E α R m}) fun α R hα hαR => ?_
  have hr := fun m => hrec α R m hα hαR
  have hV : MeasurableSet (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hd := fun m => h2 D hγ (a α R m) (δ α R m) (M α R m) (hr m).pos_a (hr m).pos_δ (hr m).δ_lt_M
  have hZ₁ : ∀ m, AEMeasurable (fun ω => offsetPhaseVector 0 (ηL ω) (quantumConeArea γ γ X B B' ω)
      (a α R m) (δ α R m) (M α R m)) P := fun m =>
    (measurableEmbedding_countablePhase_inject 2).measurable.comp_aemeasurable
      (((hout _ hAγ _ _).prodMk aemeasurable_const).prodMk (hd m).1.1)
  have hZ₂ : ∀ m, AEMeasurable (fun p : Ω × ℝ => offsetPhaseVector p.2 (ηL p.1)
      (quantumConeArea γ 0 X₀ B₀ B₀' p.1) (a α R m) (δ α R m) (M α R m)) (P.prod zeroConePhase) := fun m =>
    (measurableEmbedding_countablePhase_inject 2).measurable.comp_aemeasurable
      (((aemeasurable_comp_fst_prod (hout _ hA0 _ _)).prodMk measurable_snd.aemeasurable).prodMk
        (aemeasurable_comp_fst_prod (hd m).2.1))
  have hlaw : ∀ m, (P.prod zeroConePhase).map (fun p : Ω × ℝ =>
      annulusOuterData (ηL p.1) (quantumConeArea γ 0 X₀ B₀ B₀' p.1) (δ α R m) (M α R m)) =
      P.map (fun ω => annulusOuterData (ηL ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) (δ α R m) (M α R m)) :=
    fun m => map_comp_fst_prod (hout _ hA0 _ _)
  have hL := fun m => hL1 (δ α R m) (M α R m) (hr m).pos_δ (hr m).δ_lt_M
  exact
    { aemeasurable_mark_left := hZ₁
      aemeasurable_mark_right := hZ₂
      measurable_recon := fun m => (hr m).measurable_recon
      measurableSet_good := fun m => (measurable_fst.comp measurable_snd) (hr m).measurableSet_event
      aemeasurable_left := fun n =>
        ((measurable_localConfig hV).comp ((measurable_vertexData _).comp
          (measurable_coneConfigData hη hbm n))).aemeasurable
      aemeasurable_right := fun n =>
        ((measurable_localConfig hV).comp ((measurable_vertexData _).comp
          (measurable_zeroConeShiftedData hη₀ hG.1 n))).aemeasurable
      good_left := fun m => (hr m).event_compl_le
      good_right := fun m => calc
        _ ≤ (P.prod zeroConePhase) ({ω | ηL ω ∉ E α R m} ×ˢ (univ : Set ℝ)) :=
            measure_mono fun p hp => ⟨hp, mem_univ _⟩
        _ = P {ω | ηL ω ∉ E α R m} := by rw [Measure.prod_prod, measure_univ, mul_one]
        _ ≤ _ := (hr m).event_compl_le
      recon_left := fun m => (hr m).recon_cone
      recon_right := fun m => (hr m).recon_zeroCone
      ac_left := fun m k => absolutelyContinuous_phaseZero (hout _ hAγ _ _) (hd m).1.1 (hd m).1.2 k
      ac_right := fun m k =>
        absolutelyContinuous_indepUniformPhase (U := zeroConePhase) (hout _ hA0 _ _) (hd m).2.1 (hd m).2.2 k
      mark_left_right := fun m =>
        absolutelyContinuous_map_countOuter (hZ₁ m) (hZ₂ m) (hout _ hAγ _ _)
          (aemeasurable_comp_fst_prod (hout _ hA0 _ _)) (fun _ => rfl) (fun _ => rfl)
          (by rw [hlaw m]; exact (hL m).1)
      mark_right_left := fun m =>
        absolutelyContinuous_map_countOuter (hZ₂ m) (hZ₁ m)
          (aemeasurable_comp_fst_prod (hout _ hA0 _ _)) (hout _ hAγ _ _) (fun _ => rfl) (fun _ => rfl)
          (by rw [hlaw m]; exact (hL m).2) }

end Coupling

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield for every `γ ∈ (0, 2)` and every mating-of-trees coupling**, in the form
of the premise `h33` of the canonical Tutte assembly (`GMS21CanonicalTutteLP.lean`), from the three inputs at
every `γ ∈ (0, 2)`. -/
theorem forall_couplingLocalConfigUMAC_of_lemma33Inputs
    (h1 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeAnnulusAreaLawEquivalence γ)
    (h2 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeOffsetDensity γ)
    (h3 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeConfigReconstruction γ) :
    ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
      {bm : Ω → Path2} (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      CouplingLocalConfigUMAC D hγ := by
  intro γ hγ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D
  exact couplingLocalConfigUMAC_of_lemma33Inputs (h1 γ hγ) (h2 γ hγ) (h3 γ hγ) D hγ

end MatedCRT
