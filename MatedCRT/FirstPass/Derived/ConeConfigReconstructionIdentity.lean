import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideIdentityProof
import MatedCRT.FirstPass.Derived.ZeroConeEdgeCountCodeProof
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepairProofs
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.BlockCellMinInjective
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusForm

/-!
# Almost sure identities of a mating-of-trees coupling

For a mating-of-trees coupling `D` and `γ ∈ (0, 2)`, three almost sure identities used to reconstruct the local
configuration of the cones from the curve.

* `ae_bmEdgeCount_eq_cellSideMult_cone`: almost surely, at every mesh `1/n`, the edge counts of the
  boundary-length pair `bm` (Definition 1.1) are the frontier-side multiplicities of the cells of the
  area-parametrized curve `η` of the `γ`-quantum cone. This is the cell-side identity
  (`matingOfTreesCellSideIdentity`) at the level of the coupling, from Le Gall's theorem on cone points
  (`PlanarBMNoTwoSidedConePoints`) and the triple-point hypothesis on Peanosphere curves
  `CorrelatedBMPeanosphereTriplePointsNoContinuum` (which follows from
  `CorrelatedBMTraversalTriplePointsNoContinuum` by
  `ae_forall_peanosphere_not_containsNondegenerateContinuum`).
* `ae_phaseShiftedEdgeCount_eq_cellSideMult`: the same identity for the zero cone on the shifted lattice
  `n⁻¹ ℤ + n⁻¹ θ`, for almost every phase `θ`, with the unit-mesh multiplicities of the rescaled curve
  `t ↦ η₀((t + θ)/n)`.
* `ae_eq_zero_of_curve_eq_zero`: almost surely the Lebesgue-parametrized curve `ηL` visits the origin only at
  time `0`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRT.GMS310Transfer

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, the fibres of the area-parametrized curve `η` of a coupling are finite. -/
theorem ae_finite_fibres_of_isMatingOfTreesCoupling
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ z, (⇑(η ω) ⁻¹' {z}).Finite := by
  obtain ⟨kv, hkv⟩ := D.visitBound
  filter_upwards [hkv, D.areaParam] with ω hk harea
  obtain ⟨⟨φ, -, hφ⟩, -⟩ := harea
  intro z
  have hset : ⇑(η ω) ⁻¹' {z} = φ ⁻¹' (ηL ω ⁻¹' {z}) := by
    ext t
    show η ω t = z ↔ ηL ω (φ t) = z
    rw [hφ]
  rw [hset]
  exact (Set.encard_lt_top_iff.1 ((hk z).trans_lt (ENat.natCast_lt_top kv))).preimage
    φ.injective.injOn

/-- **The Brownian edge counts of the `γ`-cone are the frontier-side multiplicities of the cells.** Almost
surely, for every mesh `1/n` and all `j, k`, the edge count of the boundary-length pair `bm` equals
`cellSideMult (1/n) (η ω) j k`. The Peanosphere, the finite fibres and the Brownian law of `bm` come from the
coupling; the absence of common local minima from Le Gall's theorem on cone points; the absence of continua of
triple points from `CorrelatedBMPeanosphereTriplePointsNoContinuum`; the descent of both coordinates at the points
`k/n` from the Blumenthal zero-one law; the identity is `bmEdgeCount_eq_cellSideMult`. -/
theorem ae_bmEdgeCount_eq_cellSideMult_cone (hLG : PlanarBMNoTwoSidedConePoints)
    (hT : CorrelatedBMPeanosphereTriplePointsNoContinuum)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ j k : ℤ,
      bmEdgeCount (1 / (n : ℝ)) (fun t => (bm ω t).1) (fun t => (bm ω t).2) j k =
        cellSideMult (1 / (n : ℝ)) (η ω) j k := by
  have hbm : AEMeasurable bm P := D.measurable_curves.2.2.2.aemeasurable
  have hcn := ae_of_ae_map hbm (correlatedBMNoCommonLocalMin hLG γ hγ.1 hγ.2 _ D.boundaryLawBM)
  have htr := ae_of_ae_map hbm
    (hT γ hγ.1 hγ.2 _ D.boundaryLawBM)
  have hd := ae_of_ae_map hbm (ae_all_iff.2 fun n : ℕ => ae_all_iff.2 fun i : Fin 2 =>
    ae_all_iff.2 fun k : ℤ =>
      (ae_forall_exists_lt_right D.boundaryLawBM i (1 / (n : ℝ) * k)).and
        (ae_forall_exists_lt_left D.boundaryLawBM i (1 / (n : ℝ) * k)))
  filter_upwards [ae_peanosphere_of_isMatingOfTreesCoupling D, ae_finite_fibres_of_isMatingOfTreesCoupling D,
    htr, hcn, hd] with ω hPω hfinω htrω hcnω hdω n hn j k
  exact bmEdgeCount_eq_cellSideMult hPω hfinω (htrω _ hPω) (fun u hu => hcnω u hu)
    (one_div_pos.2 (Nat.cast_pos.2 hn)) (fun k => ⟨hdω n 0 k, hdω n 1 k⟩) j k

/-- **The edge counts of the zero cone on the shifted lattice are the unit-mesh frontier-side multiplicities.**
For a measurable version `G` of the boundary-length pair of the zero-cone curve and `n ≥ 1`, for almost every
`(ω, θ)` the edge counts at mesh `1/n` of `t ↦ G ω (t + θ/n)` are `cellSideMult 1` of the curve
`t ↦ η₀ ω ((t + θ)/n)`. The curve `η₀` and the curve `η` of the `γ`-cone are related by the area clock `ψ`; the
cell endpoints `(k + θ)/n` are almost surely visited once by `η₀` (area additivity on disjoint rational
intervals and Fubini in the phase), so both coordinates descend on both sides of them, and the identity is
`bmEdgeCount_eq_cellSideMult` for the Peanosphere `(bm ∘ e, η ∘ e)` with the time change `e t = ψ ((t + θ)/n)`. -/
theorem ae_phaseShiftedEdgeCount_eq_cellSideMult (hLG : PlanarBMNoTwoSidedConePoints)
    (hT : CorrelatedBMPeanosphereTriplePointsNoContinuum)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (G : Ω → Path2) (hG : IsZeroConeBoundaryPair D hγ G) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ p ∂P.prod zeroConePhase, ∀ j k : ℤ,
      phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1) j k =
        cellSideMult 1 (phaseShiftedCurve 1 p.2 (curveMeshRescale n (η₀ p.1))) j k := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨-, hGae⟩ := hG
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hbm : AEMeasurable bm P := D.measurable_curves.2.2.2.aemeasurable
  have hη₀m : Measurable η₀ := D.measurable_curves.2.2.1
  -- almost every time is visited once by the zero-cone curve
  have hMV : ∀ᵐ ω ∂P, volume (multipleVisitWitness ⇑(η₀ ω)) = 0 := by
    filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ, D.areaParam₀]
      with ω hv hpar
    obtain ⟨μ, hμ⟩ := hv
    exact volume_multipleVisitWitness_eq_zero (η₀ ω).continuous hμ.1 (hpar.2 μ hμ)
  -- the phases for which a cell endpoint is visited twice form a null set
  set E : Set (Ω × ℝ) :=
    {p | ∃ k : ℤ, (n : ℝ)⁻¹ * ((k : ℝ) + p.2) ∈ multipleVisitWitness ⇑(η₀ p.1)} with hE
  have hEm : MeasurableSet E := by
    rw [hE, ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_multipleVisitWitness.preimage
      (f := fun p : Ω × ℝ => (η₀ p.1, (n : ℝ)⁻¹ * ((k : ℝ) + p.2))) (by fun_prop)
  have hE0 : (P.prod zeroConePhase) E = 0 := by
    rw [Measure.measure_prod_null hEm]
    filter_upwards [hMV] with ω hω
    have hsub : Prod.mk ω ⁻¹' E ⊆ ⋃ k : ℤ, (fun θ : ℝ => (k : ℝ) + θ) ⁻¹'
        ((fun x : ℝ => (n : ℝ)⁻¹ * x) ⁻¹' multipleVisitWitness ⇑(η₀ ω)) := by
      rintro θ ⟨k, hk⟩
      exact mem_iUnion.2 ⟨k, hk⟩
    have hnull : volume (⋃ k : ℤ, (fun θ : ℝ => (k : ℝ) + θ) ⁻¹'
        ((fun x : ℝ => (n : ℝ)⁻¹ * x) ⁻¹' multipleVisitWitness ⇑(η₀ ω))) = 0 :=
      measure_iUnion_null fun k => by
        rw [measure_preimage_add, Real.volume_preimage_mul_left (inv_ne_zero hn'.ne'), hω, mul_zero]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self (measure_mono_null hsub hnull)
  have hEc : ∀ᵐ p ∂P.prod zeroConePhase, p ∉ E :=
    ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using hE0)
  have hlift : ∀ {Q : Ω → Prop}, (∀ᵐ ω ∂P, Q ω) → ∀ᵐ p ∂P.prod zeroConePhase, Q p.1 :=
    fun h => Measure.quasiMeasurePreserving_fst.ae h
  filter_upwards [hlift (ae_peanosphere_of_isMatingOfTreesCoupling D),
    hlift (LatticeProb.ae_coupled_area_clock D hγ), hlift hGae,
    hlift (ae_finite_fibres_of_isMatingOfTreesCoupling D),
    hlift (ae_of_ae_map hbm
      (hT γ hγ.1 hγ.2 _ D.boundaryLawBM)),
    hlift (ae_of_ae_map hbm (correlatedBMNoCommonLocalMin hLG γ hγ.1 hγ.2 _ D.boundaryLawBM)), hEc]
    with p hPe hclk hGω hfin htr hcn hp
  set ω := p.1
  set θ := p.2
  obtain ⟨ψ, -, hη₀ψ, hψ⟩ := hclk
  -- the cell endpoints are visited once
  have hunique : ∀ k : ℤ, ∀ s, η₀ ω s = η₀ ω ((n : ℝ)⁻¹ * ((k : ℝ) + θ)) →
      s = (n : ℝ)⁻¹ * ((k : ℝ) + θ) :=
    fun k s hs => eq_of_notMem_multipleVisitWitness (fun hk => hp ⟨k, hk⟩) hs
  -- the time change `e t = ψ ((t + θ)/n)`
  have hmono : StrictMono fun t : ℝ => ψ ((n : ℝ)⁻¹ * (t + θ)) :=
    ψ.strictMono.comp fun a b hab => mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 hn')
  have hsurj : Function.Surjective fun t : ℝ => ψ ((n : ℝ)⁻¹ * (t + θ)) := fun y =>
    ⟨(n : ℝ) * ψ.symm y - θ, by
      show ψ ((n : ℝ)⁻¹ * ((n : ℝ) * ψ.symm y - θ + θ)) = y
      rw [sub_add_cancel, inv_mul_cancel_left₀ hn'.ne', ψ.apply_symm_apply]⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ∀ t, e t = ψ ((n : ℝ)⁻¹ * (t + θ)) :=
    ⟨StrictMono.orderIsoOfSurjective _ hmono hsurj, fun t => rfl⟩
  have Pe := hPe.comp_orderIso e
  set w : Path2 := ⟨fun t => bm ω (e t), (bm ω).continuous.comp e.continuous⟩
  -- the hypotheses of the deterministic identity
  have hfin' : ∀ z, ((fun t => η ω (e t)) ⁻¹' {z}).Finite := fun z =>
    (hfin z).preimage (f := ⇑e) e.injective.injOn
  have htr' : ¬ ContainsNondegenerateContinuum (curveTriplePoints fun t => η ω (e t)) := by
    rintro ⟨K, hK, hKc⟩
    exact htr _ hPe ⟨K, hK.trans fun z ⟨t₁, t₂, t₃, h12, h23, h1, h2, h3⟩ =>
      ⟨e t₁, e t₂, e t₃, e.strictMono h12, e.strictMono h23, h1, h2, h3⟩, hKc⟩
  have hmin : ∀ (Y : ℝ → ℝ) (x : ℝ), IsLocalMin (fun t => Y (e t)) x → IsLocalMin Y (e x) := by
    intro Y x hx
    have hx₀ : IsLocalMin (Y ∘ e) (e.symm (e x)) := by
      rw [e.symm_apply_apply]
      exact hx
    have h := hx₀.comp_continuous (e.symm.continuous.continuousAt (x := e x))
    simpa only [Function.comp_def, e.apply_symm_apply] using h
  have hcone' : ∀ u, ¬ (IsLocalMin (RouteM.lCoord w) u ∧ IsLocalMin (RouteM.rCoord w) u) := fun u hu =>
    hcn (e u) ⟨hmin (fun s => lrCoord 0 s (bm ω)) u hu.1, hmin (fun s => lrCoord 1 s (bm ω)) u hu.2⟩
  have hdesc' : ∀ k : ℤ, IsTwoSidedDescent (RouteM.lCoord w) ((1 : ℝ) * k) ∧
      IsTwoSidedDescent (RouteM.rCoord w) ((1 : ℝ) * k) := by
    intro k
    rw [one_mul]
    have hu : ∀ t, η ω t = η ω (e k) → t = e k := by
      intro t ht
      have h1 := hunique k (ψ.symm t) (by rw [hη₀ψ, hη₀ψ, ψ.apply_symm_apply, ht, he])
      rw [he, ← h1, ψ.apply_symm_apply]
    obtain ⟨hl, hr⟩ := isTwoSidedDescent_of_forall_eq hPe hu
    exact ⟨isTwoSidedDescent_comp_orderIso e hl, isTwoSidedDescent_comp_orderIso e hr⟩
  have hcurve : ⇑(phaseShiftedCurve 1 θ (curveMeshRescale n (η₀ ω))) = fun t => η ω (e t) := by
    funext t
    show η₀ ω ((t + 1 * θ) / n) = η ω (e t)
    rw [hη₀ψ, he]
    exact congrArg (fun x => η ω (ψ x)) (by ring)
  have hG' : ∀ t, G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ) = bm ω (e t) := fun t => by
    rw [hGω, hψ, he]
    exact congrArg (fun x => bm ω (ψ x)) (by ring)
  intro j k
  calc phaseShiftedEdgeCount (1 / (n : ℝ)) θ (G ω) j k
      = bmEdgeCount 1 (fun t => (G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ)).1)
          (fun t => (G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ)).2) j k :=
        (bmEdgeCount_comp_mul_left (L := fun t => (G ω (t + 1 / (n : ℝ) * θ)).1)
          (R := fun t => (G ω (t + 1 / (n : ℝ) * θ)).2) (one_div_pos.2 hn') j k).symm
    _ = bmEdgeCount 1 (RouteM.lCoord w) (RouteM.rCoord w) j k := by
        congr 1
        · funext t
          exact congrArg Prod.fst (hG' t)
        · funext t
          exact congrArg Prod.snd (hG' t)
    _ = cellSideMult 1 (fun t => η ω (e t)) j k :=
        bmEdgeCount_eq_cellSideMult Pe hfin' htr' hcone' one_pos hdesc' j k
    _ = cellSideMult 1 ⇑(phaseShiftedCurve 1 θ (curveMeshRescale n (η₀ ω))) j k := by
        rw [hcurve]

/-- A direct relation of a coordinate which descends immediately on both sides of `0` never involves the
time `0`. -/
theorem directRel_ne_zero {X : ℝ → ℝ}
    (hr : ∀ δ > 0, ∃ t, 0 < t ∧ t < 0 + δ ∧ X t < X 0)
    (hl : ∀ δ > 0, ∃ t, 0 - δ < t ∧ t < 0 ∧ X t < X 0) {a b : ℝ} (h : DirectRel X a b) :
    a ≠ 0 ∧ b ≠ 0 := by
  obtain ⟨hab, hX, hmin⟩ := h
  constructor
  · rintro rfl
    obtain ⟨t, ht0, htb, htX⟩ := hr b hab
    exact absurd (hmin t ⟨ht0, by linarith⟩) (not_lt.2 htX.le)
  · rintro rfl
    obtain ⟨t, hta, ht0, htX⟩ := hl (-a) (by linarith)
    refine absurd (hmin t ⟨by linarith, ht0⟩) (not_lt.2 ?_)
    rw [hX]
    exact htX.le

/-- **The Lebesgue-parametrized curve visits the origin only at time `0`.** Almost surely, `ηL ω t = 0`
implies `t = 0`. Write `η = ηL ∘ φ` with `φ 0 = 0`; the curve is rooted at `0` (`ηL 0 = 0`), so `ηL t = 0` with
`t = φ s` gives `η s = η 0`, and the times identified with `0` are the times connected to `0` by direct relations
of the coordinates of `bm`. Both coordinates descend immediately on both sides of `0` almost surely, so no
direct relation involves `0`, and `s = 0`. -/
theorem ae_eq_zero_of_curve_eq_zero
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ηL ω t = 0 → t = 0 := by
  have hbm : AEMeasurable bm P := D.measurable_curves.2.2.2.aemeasurable
  have hd := ae_of_ae_map hbm (ae_all_iff.2 fun i : Fin 2 =>
    (ae_forall_exists_lt_right D.boundaryLawBM i 0).and (ae_forall_exists_lt_left D.boundaryLawBM i 0))
  filter_upwards [D.spaceFilling, D.areaParam, D.onlyMerge, hd] with ω hsp harea honly hdω t ht
  obtain ⟨⟨φ, hφ0, hηeq⟩, -⟩ := harea
  have hrel : ∀ a b : ℝ, (DirectRel (fun u => lrCoord 0 u (bm ω)) a b ∨
      DirectRel (fun u => lrCoord 1 u (bm ω)) a b) → a ≠ 0 ∧ b ≠ 0 := fun a b h =>
    h.elim (directRel_ne_zero (X := fun u => lrCoord 0 u (bm ω)) (hdω 0).1 (hdω 0).2)
      (directRel_ne_zero (X := fun u => lrCoord 1 u (bm ω)) (hdω 1).1 (hdω 1).2)
  have hclass : ∀ a b : ℝ, Relation.EqvGen (fun a c => DirectRel (fun u => lrCoord 0 u (bm ω)) a c ∨
      DirectRel (fun u => lrCoord 1 u (bm ω)) a c) a b → (a = 0 ↔ b = 0) := by
    intro a b h
    induction h with
    | rel x y hxy => exact ⟨fun h => absurd h (hrel x y hxy).1, fun h => absurd h (hrel x y hxy).2⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨s, rfl⟩ := φ.surjective t
  have hs : η ω s = η ω 0 := by
    rw [hηeq, hηeq, hφ0, ht, hsp.2.2.1]
  have h0 := (hclass s 0 (honly s 0 hs)).2 rfl
  rw [h0, hφ0]

end Coupling

end MatedCRT
