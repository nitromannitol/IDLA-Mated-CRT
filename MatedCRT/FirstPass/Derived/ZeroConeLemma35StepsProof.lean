import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepairProofs
import MatedCRT.FirstPass.Derived.GMS21LocalCellConfiguration
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import LatticeProb.Topology.UnboundedRayProjectionBorel

/-!
# The named steps of the annulus form of Lemma 3.5 of Gwynne–Miller–Sheffield for the zero-cone cells

This file proves the named steps of `GMS21ZeroConeAnnulusRepairProofs.lean` and `ZeroConePhaseFactorProof.lean`
following the written answer `notes/fp-gaps/CODEX-MQ-sbl-27.md` (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of
Lemma 3.5 and of Proposition 3.1).

* `weightedErrorSuperlevelBorelProjection` (answer, section "(d) The two Borel sets of witnesses", lines 54-67): the
  strict superlevel sets of the scale supremum of the unit-mesh uniform error and of the mesh-`1/n` uniform error are
  the projections of the Borel sets of witnesses `(s, z, j)`: a scale `0 < s ≤ ε₀` (unit case), a start `z` of the
  annulus in the cell of the label `j`, and an error of the walk from `j` strictly above the threshold. The error of
  a single start is a Borel function of the data and of `(s, z)` (`measurable_walkLPError`): the walk law is a Borel
  kernel in the edge counts and the vertices, the restriction to unbounded paths and the projection to curve classes
  are Borel, Brownian motion is the translate of Brownian motion from `0`, and the Lévy–Prokhorov distance on the
  separable space of curve classes is Borel in the two measures (`measurable_levyProkhorovEDist_of_separable`: below
  `c` exactly when, for some rational `r < c`, the two Prokhorov inequalities at `r` hold on the finite unions of a
  countable basis).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open LatticeProb LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayLocalDistance
  LatticeProb.UnboundedRayCurveSpace LatticeProb.ReparamDistanceIsometry
open ReflectedGMS.StatementIngredients

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _

local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩

attribute [local instance] isProbabilityMeasure_map_complexToEuclideanPath

/-! ### The Lévy–Prokhorov distance on a separable space is Borel -/

/-- **Measurability of the Lévy–Prokhorov distance on a separable space.** For two measurable families of measures on
a separable pseudometric space, `x ↦ d_LP(μ x, ν x)` is measurable. The distance is below `c` exactly when, for some
rational `r` with `r < c`, the two Prokhorov inequalities at `r` hold on the finite unions of a countable basis: they
pass to open sets by increasing unions, and to Borel sets through their open thickenings. -/
theorem measurable_levyProkhorovEDist_of_separable {X E : Type*} [MeasurableSpace X] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E] {μ ν : X → Measure E}
    (hμ : Measurable μ) (hν : Measurable ν) :
    Measurable fun x => levyProkhorovEDist (μ x) (ν x) := by
  classical
  have : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  have hbasis := TopologicalSpace.isBasis_countableBasis E
  set 𝓑 : Set (Set E) := insert ∅ (TopologicalSpace.countableBasis E) with h𝓑def
  have h𝓑c : 𝓑.Countable := (TopologicalSpace.countable_countableBasis E).insert ∅
  have h𝓑o : ∀ b ∈ 𝓑, IsOpen b := by
    intro b hb
    rcases hb with rfl | hb
    · exact isOpen_empty
    · exact hbasis.isOpen hb
  set 𝓤 : Set (Set E) := (fun t : Set (Set E) => ⋃₀ t) '' {t | t.Finite ∧ t ⊆ 𝓑} with h𝓤def
  have h𝓤c : 𝓤.Countable := (Set.countable_ofPred_finite_subset h𝓑c).image _
  have h𝓤o : ∀ U ∈ 𝓤, IsOpen U := by
    rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
    exact isOpen_sUnion fun b hb => h𝓑o b (ht hb)
  -- the Prokhorov inequalities at `r` on the finite unions
  let G : ℝ → Set X := fun r => ⋂ U ∈ 𝓤,
    ({x | μ x U ≤ ν x (thickening r U) + ENNReal.ofReal r} ∩
      {x | ν x U ≤ μ x (thickening r U) + ENNReal.ofReal r})
  have hG : ∀ r : ℝ, MeasurableSet (G r) := by
    intro r
    refine MeasurableSet.biInter h𝓤c fun U hU => ?_
    have hUm : MeasurableSet U := (h𝓤o U hU).measurableSet
    have hTm : MeasurableSet (thickening r U) := isOpen_thickening.measurableSet
    exact (measurableSet_le ((Measure.measurable_coe hUm).comp hμ)
      (((Measure.measurable_coe hTm).comp hν).add_const _)).inter
      (measurableSet_le ((Measure.measurable_coe hUm).comp hν)
        (((Measure.measurable_coe hTm).comp hμ).add_const _))
  -- they pass to every open set
  have hopen : ∀ r : ℝ, ∀ x ∈ G r, ∀ O : Set E, IsOpen O →
      μ x O ≤ ν x (thickening r O) + ENNReal.ofReal r ∧
        ν x O ≤ μ x (thickening r O) + ENNReal.ofReal r := by
    intro r x hx O hO
    have hx' : ∀ U ∈ 𝓤, μ x U ≤ ν x (thickening r U) + ENNReal.ofReal r ∧
        ν x U ≤ μ x (thickening r U) + ENNReal.ofReal r := fun U hU => mem_iInter₂.1 hx U hU
    set S : Set (Set E) := {b ∈ 𝓑 | b ⊆ O} with hSdef
    have hSc : S.Countable := h𝓑c.mono (sep_subset _ _)
    have hSne : S.Nonempty := ⟨∅, mem_insert _ _, empty_subset _⟩
    obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
    have hfS : ∀ n, f n ∈ S := fun n => by rw [hf]; exact mem_range_self n
    have hfO : ⋃ n, f n = O := by
      apply Subset.antisymm
      · exact iUnion_subset fun n => (hfS n).2
      · intro y hy
        obtain ⟨v, hv, hyv, hvO⟩ := hbasis.exists_subset_of_mem_open hy hO
        have hvS : v ∈ S := ⟨mem_insert_of_mem _ hv, hvO⟩
        rw [hf] at hvS
        obtain ⟨n, rfl⟩ := hvS
        exact mem_iUnion.2 ⟨n, hyv⟩
    have hacc : ∀ n, accumulate f n ∈ 𝓤 := by
      intro n
      refine ⟨f '' Iic n, ⟨(finite_Iic n).image f, ?_⟩, ?_⟩
      · rintro _ ⟨k, -, rfl⟩
        exact (hfS k).1
      · show ⋃₀ (f '' Iic n) = accumulate f n
        rw [sUnion_image, accumulate_def]
        rfl
    have haccO : ∀ n, accumulate f n ⊆ O := fun n => by
      rw [← hfO]
      exact accumulate_subset_iUnion n
    have hOeq : O = ⋃ n, accumulate f n := by
      apply Subset.antisymm
      · rw [← hfO]
        exact iUnion_mono fun n => subset_accumulate
      · exact iUnion_subset haccO
    have hmono : Monotone (accumulate f) := monotone_accumulate
    constructor
    · rw [hOeq, hmono.measure_iUnion]
      refine iSup_le fun n => (hx' _ (hacc n)).1.trans ?_
      gcongr
      exact thickening_subset_of_subset r ((haccO n).trans hOeq.subset)
    · rw [hOeq, hmono.measure_iUnion]
      refine iSup_le fun n => (hx' _ (hacc n)).2.trans ?_
      gcongr
      exact thickening_subset_of_subset r ((haccO n).trans hOeq.subset)
  refine measurable_of_Iio fun c => ?_
  have hset : (fun x => levyProkhorovEDist (μ x) (ν x)) ⁻¹' Iio c =
      ⋃ q : ℚ, ({_x : X | 0 < (q : ℝ) ∧ ENNReal.ofReal q < c} ∩ G q) := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨q, hq0, hlt, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
      have hlt' : levyProkhorovEDist (μ x) (ν x) < ENNReal.ofReal q := hlt
      have hq : (0 : ℝ) < q := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hlt')
      refine ⟨q, ⟨hq, hqc⟩, mem_iInter₂.2 fun U hU => ?_⟩
      have hUm : MeasurableSet U := (h𝓤o U hU).measurableSet
      have h1 := left_measure_le_of_levyProkhorovEDist_lt hlt' hUm
      have h2 := right_measure_le_of_levyProkhorovEDist_lt hlt' hUm
      rw [ENNReal.toReal_ofReal hq.le] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨q, ⟨hq, hqc⟩, hx⟩
      refine lt_of_le_of_lt ?_ hqc
      refine levyProkhorovEDist_le_of_forall _ _ _ fun ε B hε hεtop hB => ?_
      have hεr : (q : ℝ) < ε.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hq.le hεtop.ne).1 hε
      have hδ : 0 < ε.toReal - q := sub_pos.2 hεr
      have hBO : B ⊆ thickening (ε.toReal - q) B := self_subset_thickening hδ B
      have hsub : thickening (q : ℝ) (thickening (ε.toReal - q) B) ⊆ thickening ε.toReal B := by
        have h := thickening_thickening_subset (q : ℝ) (ε.toReal - q) B
        rwa [show (q : ℝ) + (ε.toReal - q) = ε.toReal by ring] at h
      obtain ⟨h1, h2⟩ := hopen q x hx _ (isOpen_thickening (δ := ε.toReal - q) (E := B))
      constructor
      · calc μ x B ≤ μ x (thickening (ε.toReal - q) B) := measure_mono hBO
          _ ≤ ν x (thickening (q : ℝ) (thickening (ε.toReal - q) B)) + ENNReal.ofReal q := h1
          _ ≤ ν x (thickening ε.toReal B) + ε := add_le_add (measure_mono hsub) hε.le
      · calc ν x B ≤ ν x (thickening (ε.toReal - q) B) := measure_mono hBO
          _ ≤ μ x (thickening (q : ℝ) (thickening (ε.toReal - q) B)) + ENNReal.ofReal q := h2
          _ ≤ μ x (thickening ε.toReal B) + ε := add_le_add (measure_mono hsub) hε.le
  rw [hset]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hG q)

/-! ### The error of one start as a Borel function -/

/-- Restricting a law on continuous planar paths to the paths with unbounded range and projecting to their curve
classes is a Borel map of laws: the law of a Borel set of classes is the law of the Borel set of its unbounded
representatives. -/
theorem measurable_unboundedCurveLaw : Measurable GMS310.unboundedCurveLaw := by
  have hU : MeasurableSet {f : Path 2 | ¬ Bornology.IsBounded (Set.range f)} :=
    measurableSet_continuousMap_unbounded_range 0
  have hemb : MeasurableEmbedding (Subtype.val : UnboundedRay 2 → Path 2) :=
    MeasurableEmbedding.subtype_coe hU
  have hproj : Measurable (project : UnboundedRay 2 → UnboundedRayCurveSpace 2) :=
    continuous_project.measurable
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : ∀ μ : Measure (Path 2), GMS310.unboundedCurveLaw μ S = μ (Subtype.val '' (project ⁻¹' S)) := by
    intro μ
    unfold GMS310.unboundedCurveLaw
    rw [Measure.map_apply hproj hS, hemb.comap_apply]
  simp_rw [h]
  exact Measure.measurable_coe (hemb.measurableSet_image' (hproj hS))

/-- For a law carried by the paths with unbounded range, the curve law is the restriction to the unbounded paths
followed by the projection. -/
theorem curveLaw_eq_unboundedCurveLaw (μ : Measure (Path 2)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f)) :
    curveLaw μ hμ = GMS310.unboundedCurveLaw μ := by
  have hU : MeasurableSet {f : Path 2 | ¬ Bornology.IsBounded (Set.range f)} :=
    measurableSet_continuousMap_unbounded_range 0
  have hemb : MeasurableEmbedding (Subtype.val : UnboundedRay 2 → Path 2) :=
    MeasurableEmbedding.subtype_coe hU
  have hlift : (μ.comap (Subtype.val : UnboundedRay 2 → Path 2)).map Subtype.val = μ := by
    rw [hemb.map_comap, Subtype.range_coe_subtype]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  exact (map_project_eq_curveLaw μ hμ _ hlift).symm

/-- Planar Brownian motion is a Borel function of its starting point: it is the translate of Brownian motion from
`0`, and the translation of paths is jointly continuous. -/
theorem measurable_planarBrownianMotion_start : Measurable fun z : ℂ => planarBrownianMotion z := by
  have hc : Continuous fun p : ℂ × ContinuousPath ℂ => StopAtExitCmp.translatePath p.1 p.2 := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    change Continuous fun q : (ℂ × ContinuousPath ℂ) × ℝ≥0 => q.1.2 q.2 + q.1.1
    fun_prop
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hset : MeasurableSet {p : ℂ × ContinuousPath ℂ | StopAtExitCmp.translatePath p.1 p.2 ∈ S} :=
    hc.measurable hS
  convert measurable_measure_prodMk_left (ν := planarBrownianMotion 0) hset using 1
  funext z
  exact StopAtExitCmp.planarBrownianMotion_apply_eq_translatePath z S

/-- The Lévy–Prokhorov distance between the law modulo time parametrization of the interpolated walk on the
multigraph `m` with the vertices `v`, started from `j` (restricted to the unbounded paths), and that of planar
Brownian motion from `z`: the term of `uniformLPError` at the start `z` and the vertex `j`. -/
def walkLPError (v : ℤ → ℂ) (m : ℤ → ℤ → ℕ) (z : ℂ) (j : ℤ) : ℝ≥0∞ :=
  levyProkhorovEDist (GMS310.unboundedCurveLaw ((srwLaw m j).map fun ξ =>
      complexToEuclideanPath (interpPathCM v zero_le_one ξ)))
    (curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
      (ae_unbounded_range_map_planarBrownianMotion z))

/-- **The error of one start is a Borel function of the vertices, the edge counts and the start.** -/
theorem measurable_walkLPError {X : Type*} [MeasurableSpace X] {v : X → ℤ → ℂ} (hv : Measurable v)
    {M : X → ℤ → ℤ → ℕ} (hM : Measurable M) {Z : X → ℂ} (hZ : Measurable Z) (j : ℤ) :
    Measurable fun x => walkLPError (v x) (M x) (Z x) j := by
  unfold walkLPError
  refine measurable_levyProkhorovEDist_of_separable ?_ ?_
  · have h1 := measurable_map_srwLaw_interpPathCM hv hM j
    have h2 := (Measure.measurable_map _ continuous_complexToEuclideanPath.measurable).comp h1
    convert measurable_unboundedCurveLaw.comp h2 using 1
    funext x
    show GMS310.unboundedCurveLaw ((srwLaw (M x) j).map fun ξ =>
        complexToEuclideanPath (interpPathCM (v x) zero_le_one ξ)) =
      GMS310.unboundedCurveLaw (((srwLaw (M x) j).map (interpPathCM (v x) zero_le_one)).map
        complexToEuclideanPath)
    rw [Measure.map_map continuous_complexToEuclideanPath.measurable
      (measurable_interpPathCM (v x) zero_le_one)]
    rfl
  · have h2 := (Measure.measurable_map _ continuous_complexToEuclideanPath.measurable).comp
      (measurable_planarBrownianMotion_start.comp hZ)
    convert measurable_unboundedCurveLaw.comp h2 using 1
    funext x
    exact curveLaw_eq_unboundedCurveLaw _ _

/-- The points of a curve segment form a closed set jointly in the curve parameter and the point. -/
theorem isClosed_setOf_mem_image_Icc {Y : Type*} [TopologicalSpace Y] {G : Y × ℝ → ℂ} (hG : Continuous G)
    (a b : ℝ) : IsClosed {q : Y × ℂ | q.2 ∈ (fun u => G (q.1, u)) '' Icc a b} := by
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hcl : IsClosed {r : (Y × ℂ) × Icc a b | G (r.1.1, (r.2 : ℝ)) = r.1.2} :=
    isClosed_eq (hG.comp (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      continuous_fst.snd
  have himg := isClosedMap_fst_of_compactSpace _ hcl
  convert himg using 1
  ext q
  constructor
  · rintro ⟨u, hu, hq⟩
    exact ⟨(q, ⟨u, hu⟩), hq, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.2, r.2.2, hr⟩

/-! ### The two Borel sets of witnesses -/

/-- The strict superlevel set of the scale supremum of the unit-mesh error is the projection of the set of witnesses
`(s, z, j)`: a scale `0 < s ≤ ε₀`, a start `z ∈ A` in the cell of `j` of the curve `s w.1`, and an error strictly above
`t`. -/
theorem setOf_lt_scaleSup_weightedUnitScaleError (A : Set ℂ) (ε₀ : ℝ≥0) (t : ℝ≥0∞) :
    {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | t < scaleSup (weightedUnitScaleError A) ε₀ w} =
      Prod.fst '' {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | 0 < p.2.1 ∧ p.2.1 ≤ ε₀ ∧
        p.2.2.1 ∈ A ∧ p.2.2.1 ∈ MatedCRT.cell 1 (fun u => (p.2.1 : ℂ) * p.1.1 u) p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint 1 (fun u => (p.2.1 : ℂ) * p.1.1 u)) p.1.2 p.2.2.1 p.2.2.2} := by
  ext w
  simp only [mem_ofPred_eq, mem_image, scaleSup, weightedUnitScaleError, unitScaleError, uniformLPError,
    lt_iSup_iff]
  constructor
  · rintro ⟨ε, ⟨hε0, hε1⟩, z, hz, x, hx, hlt⟩
    exact ⟨(w, ((ε : ℝ), z, x)), ⟨NNReal.coe_pos.2 hε0, NNReal.coe_le_coe.2 hε1, hz, hx, hlt⟩, rfl⟩
  · rintro ⟨⟨w', s, z, x⟩, ⟨hs0, hs1, hz, hx, hlt⟩, rfl⟩
    refine ⟨s.toNNReal, ⟨Real.toNNReal_pos.2 hs0, Real.toNNReal_le_iff_le_coe.2 hs1⟩, z, hz, x, ?_, ?_⟩
    · rwa [Real.coe_toNNReal s hs0.le]
    · rwa [Real.coe_toNNReal s hs0.le]

/-- The strict superlevel set of the mesh-`1/n` error is the projection of the set of witnesses `(s, z, j)` (with an
arbitrary `s`): a start `z ∈ A` in the mesh-`1/n` cell of `j` and an error strictly above `t`. -/
theorem setOf_lt_meshUniformError (A : Set ℂ) (n : ℕ) (t : ℝ≥0∞) :
    {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | t < meshUniformError A (1 / (n : ℝ)) w} =
      Prod.fst '' {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | p.2.2.1 ∈ A ∧
        p.2.2.1 ∈ MatedCRT.cell (1 / (n : ℝ)) p.1.1 p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint (1 / (n : ℝ)) p.1.1) p.1.2 p.2.2.1 p.2.2.2} := by
  ext w
  simp only [mem_ofPred_eq, mem_image, meshUniformError, uniformLPError, lt_iSup_iff]
  constructor
  · rintro ⟨z, hz, x, hx, hlt⟩
    exact ⟨(w, (0, z, x)), ⟨hz, hx, hlt⟩, rfl⟩
  · rintro ⟨⟨w', s, z, x⟩, ⟨hz, hx, hlt⟩, rfl⟩
    exact ⟨z, hz, x, hx, hlt⟩

/-- The unit-mesh witnesses form a Borel set. -/
theorem measurableSet_unitWitness {A : Set ℂ} (hA : MeasurableSet A) (ε₀ : ℝ≥0) (t : ℝ≥0∞) :
    MeasurableSet {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | 0 < p.2.1 ∧ p.2.1 ≤ ε₀ ∧
        p.2.2.1 ∈ A ∧ p.2.2.1 ∈ MatedCRT.cell 1 (fun u => (p.2.1 : ℂ) * p.1.1 u) p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint 1 (fun u => (p.2.1 : ℂ) * p.1.1 u)) p.1.2 p.2.2.1 p.2.2.2} := by
  have hsplit : {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | 0 < p.2.1 ∧ p.2.1 ≤ ε₀ ∧
        p.2.2.1 ∈ A ∧ p.2.2.1 ∈ MatedCRT.cell 1 (fun u => (p.2.1 : ℂ) * p.1.1 u) p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint 1 (fun u => (p.2.1 : ℂ) * p.1.1 u)) p.1.2 p.2.2.1 p.2.2.2} =
      ⋃ j : ℤ, ({p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | p.2.2.2 = j} ∩
        ({p | 0 < p.2.1} ∩ ({p | p.2.1 ≤ ε₀} ∩ ({p | p.2.2.1 ∈ A} ∩
          ({p | p.2.2.1 ∈ MatedCRT.cell 1 (fun u => (p.2.1 : ℂ) * p.1.1 u) j} ∩
            {p | t < walkLPError (MatedCRT.vertexPoint 1 (fun u => (p.2.1 : ℂ) * p.1.1 u)) p.1.2
              p.2.2.1 j}))))) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨p.2.2.2, rfl, h⟩
    · rintro ⟨j, rfl, h⟩
      exact h
  rw [hsplit]
  refine MeasurableSet.iUnion fun j => (measurable_snd.snd.snd (measurableSet_singleton j)).inter ?_
  have hS := (isClosed_setOf_mem_image_Icc (G := fun r : (C(ℝ, ℂ) × ℝ) × ℝ => (r.1.2 : ℂ) * r.1.1 r.2)
    (by fun_prop) (1 * ((j : ℝ) - 1)) (1 * (j : ℝ))).measurableSet
  have hmap : Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) => ((p.1.1, p.2.1), p.2.2.1) :=
    (measurable_fst.fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst
  have hcell := hmap hS
  have hv : Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) =>
      MatedCRT.vertexPoint 1 (fun u => (p.2.1 : ℂ) * p.1.1 u) := by
    refine measurable_pi_iff.2 fun k => ?_
    change Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) =>
      ((p.2.1 : ℝ) : ℂ) * p.1.1 (1 * (k : ℝ))
    exact (Complex.measurable_ofReal.comp measurable_snd.fst).mul
      ((continuous_eval_const _).measurable.comp measurable_fst.fst)
  have herr := measurable_walkLPError hv measurable_fst.snd measurable_snd.snd.fst j
  exact (measurableSet_lt measurable_const measurable_snd.fst).inter
    ((measurableSet_le measurable_snd.fst measurable_const).inter
      ((measurable_snd.snd.fst hA).inter (hcell.inter (measurableSet_lt measurable_const herr))))

/-- The mesh-`1/n` witnesses form a Borel set. -/
theorem measurableSet_meshWitness {A : Set ℂ} (hA : MeasurableSet A) (n : ℕ) (t : ℝ≥0∞) :
    MeasurableSet {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | p.2.2.1 ∈ A ∧
        p.2.2.1 ∈ MatedCRT.cell (1 / (n : ℝ)) p.1.1 p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint (1 / (n : ℝ)) p.1.1) p.1.2 p.2.2.1 p.2.2.2} := by
  have hsplit : {p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | p.2.2.1 ∈ A ∧
        p.2.2.1 ∈ MatedCRT.cell (1 / (n : ℝ)) p.1.1 p.2.2.2 ∧
        t < walkLPError (MatedCRT.vertexPoint (1 / (n : ℝ)) p.1.1) p.1.2 p.2.2.1 p.2.2.2} =
      ⋃ j : ℤ, ({p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) | p.2.2.2 = j} ∩
        ({p | p.2.2.1 ∈ A} ∩ ({p | p.2.2.1 ∈ MatedCRT.cell (1 / (n : ℝ)) p.1.1 j} ∩
          {p | t < walkLPError (MatedCRT.vertexPoint (1 / (n : ℝ)) p.1.1) p.1.2 p.2.2.1 j}))) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨p.2.2.2, rfl, h⟩
    · rintro ⟨j, rfl, h⟩
      exact h
  rw [hsplit]
  refine MeasurableSet.iUnion fun j => (measurable_snd.snd.snd (measurableSet_singleton j)).inter ?_
  have hS := (isClosed_setOf_mem_image_Icc (G := fun r : C(ℝ, ℂ) × ℝ => r.1 r.2) (by fun_prop)
    (1 / (n : ℝ) * ((j : ℝ) - 1)) (1 / (n : ℝ) * (j : ℝ))).measurableSet
  have hmap : Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) => (p.1.1, p.2.2.1) :=
    measurable_fst.fst.prodMk measurable_snd.snd.fst
  have hcell := hmap hS
  have hv : Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) =>
      MatedCRT.vertexPoint (1 / (n : ℝ)) p.1.1 := by
    refine measurable_pi_iff.2 fun k => ?_
    change Measurable fun p : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℝ × ℂ × ℤ) => p.1.1 (1 / (n : ℝ) * (k : ℝ))
    exact (continuous_eval_const _).measurable.comp measurable_fst.fst
  have herr := measurable_walkLPError hv measurable_fst.snd measurable_snd.snd.fst j
  exact (measurable_snd.snd.fst hA).inter (hcell.inter (measurableSet_lt measurable_const herr))

/-- **The strict superlevel events of the uniform errors are projections of Borel events** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-27.md`, section "(d) The two Borel sets of witnesses", lines 54-67). -/
theorem weightedErrorSuperlevelBorelProjection : WeightedErrorSuperlevelBorelProjection := by
  intro b ρ
  have hA : MeasurableSet (closedBall (0 : ℂ) ρ \ ball 0 b) := measurableSet_closedBall.diff measurableSet_ball
  exact ⟨fun ε₀ t => ⟨_, measurableSet_unitWitness hA ε₀ t,
      setOf_lt_scaleSup_weightedUnitScaleError _ ε₀ t⟩,
    fun n _ t => ⟨_, measurableSet_meshWitness hA n t, setOf_lt_meshUniformError _ n t⟩⟩

end MatedCRT.GMS310Transfer
