import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1ConeTail
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Rotation
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Sectors

/-!
# The eight sectors of the circle-average zero cone have infinite area almost surely

For the proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A; written answer
58, section 3, first paragraph), this file proves `ae_a1Sector_eq_top`: if the circle-average
embedding `h` of the `0`-quantum cone has an area measure of infinite total mass which is finite on
compacts, then almost surely the area measure of `h` of each of the eight open sectors `a1Sector j`
is infinite.

The event `E j` that the sector `a1Sector j` has infinite area is almost surely equal, for every
`k`, to the event that the area of the sector outside the disc of radius `k + 2` is infinite
(finiteness on compacts), which is measurable for the exterior σ-algebra `extSigma (k + 1)` through
the decoder of the exterior area. The exterior tail of the cone is trivial
(`isTrivialSigma_zeroCone_extTail`), so `E j` has probability zero or one. The rotation by `2π/8`
preserves the law of the cone and rotates its area measure, so it maps the sector `j` to the sector
`j + 1`: the eight probabilities are equal. They cannot all vanish, since the eight sectors and the
origin cover the plane, which has infinite area and a finite area at the origin.

## Main statement

* `ae_a1Sector_eq_top`: almost surely every sector `a1Sector j` has infinite area.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4O
open scoped NNReal ENNReal

/-! ### Geometry of the sectors -/

/-- The sector `j + 1` is the preimage of the sector `j` under the rotation by `-2π/8`. -/
theorem preimage_p48oRot_a1Sector (j : Fin 8) :
    p48oRot (-(2 * Real.pi / 8)) ⁻¹' a1Sector j = a1Sector (j + 1) := by
  have hexp : Complex.exp (-(2 * Real.pi * (((j + 1 : Fin 8) : ℕ) : ℝ) / 8) * Complex.I) =
      Complex.exp (-(2 * Real.pi / 8) * Complex.I) *
        Complex.exp (-(2 * Real.pi * ((j : ℕ) : ℝ) / 8) * Complex.I) := by
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    have hv : (((j + 1 : Fin 8) : ℕ) : ℝ) =
        ((j : ℕ) : ℝ) + 1 - 8 * (if (j : ℕ) = 7 then 1 else 0) := by
      have h7 := j.isLt
      by_cases hj : (j : ℕ) = 7
      · have : ((j + 1 : Fin 8) : ℕ) = 0 := by
          rw [Fin.val_add]; simp [hj]
        rw [this, ite_eq_left hj, hj]; norm_num
      · have : ((j + 1 : Fin 8) : ℕ) = (j : ℕ) + 1 := by
          rw [Fin.val_add]; simp; omega
        rw [this, ite_eq_right hj]; push_cast; ring
    refine ⟨if (j : ℕ) = 7 then 1 else 0, ?_⟩
    rw [hv]
    push_cast
    split_ifs <;> simp <;> ring
  ext w
  simp only [a1Sector, mem_preimage, mem_ofPred_eq, p48oRot_apply]
  rw [hexp]
  have hmul : Complex.exp (((-(2 * Real.pi / 8) : ℝ) : ℂ) * Complex.I) * w *
      Complex.exp (-(2 * Real.pi * ((j : ℕ) : ℝ) / 8) * Complex.I) =
      w * (Complex.exp (-(2 * Real.pi / 8) * Complex.I) *
        Complex.exp (-(2 * Real.pi * ((j : ℕ) : ℝ) / 8) * Complex.I)) := by
    push_cast; ring
  rw [hmul]
  simp [Complex.exp_ne_zero]

theorem measurableSet_a1Sector (j : Fin 8) : MeasurableSet (a1Sector j) :=
  (isOpen_a1Sector j).measurableSet

/-- The eight sectors and the origin cover the plane. -/
theorem univ_subset_singleton_union_a1Sector :
    (univ : Set ℂ) ⊆ {0} ∪ ⋃ j : Fin 8, a1Sector j := by
  intro w _
  by_cases hw : w = 0
  · exact Or.inl hw
  · obtain ⟨j, hj⟩ := exists_axis_arg_le hw
    exact Or.inr (mem_iUnion.2 ⟨j, hw, lt_of_le_of_lt hj (by linarith [Real.pi_pos])⟩)

/-- If the sectors have finite area and the origin has finite area, the whole plane has finite area.
-/
theorem measure_univ_lt_top_of_sectors {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν]
    (h : ∀ j : Fin 8, ν (a1Sector j) ≠ ⊤) : ν univ < ⊤ := by
  calc ν univ ≤ ν ({0} ∪ ⋃ j : Fin 8, a1Sector j) :=
        measure_mono univ_subset_singleton_union_a1Sector
    _ ≤ ν {0} + ν (⋃ j : Fin 8, a1Sector j) := measure_union_le _ _
    _ ≤ ν {0} + ∑ j : Fin 8, ν (a1Sector j) := by gcongr; exact measure_iUnion_fintype_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨isCompact_singleton.measure_lt_top,
        ENNReal.sum_lt_top.2 fun j _ => lt_top_iff_ne_top.2 (h j)⟩

/-- A set has infinite measure if and only if its part outside a closed disc has infinite measure,
for a measure finite on compacts. -/
theorem measure_inter_extOpen_eq_top_iff {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (S : Set ℂ)
    (ρ : ℝ) :
    ν (S ∩ (extOpen ρ : Set ℂ)) = ⊤ ↔ ν S = ⊤ := by
  refine ⟨fun h => eq_top_mono (measure_mono inter_subset_left) h, fun h => ?_⟩
  by_contra hne
  have hsub : S ⊆ Metric.closedBall (0 : ℂ) ρ ∪ (S ∩ (extOpen ρ : Set ℂ)) := fun x hx => by
    by_cases hxρ : ‖x‖ ≤ ρ
    · exact Or.inl (by simpa using hxρ)
    · exact Or.inr ⟨hx, lt_of_not_ge hxρ⟩
  have hlt : ν S < ⊤ :=
    lt_of_le_of_lt ((measure_mono hsub).trans (measure_union_le _ _))
      (ENNReal.add_lt_top.2 ⟨measure_closedBall_lt_top, lt_top_iff_ne_top.2 hne⟩)
  exact hlt.ne h

/-! ### Exterior versions of the infinite-area events -/

/-- **A set of infinite area has an exterior version.** If the area measure of a field of the good
set outside the disc of radius `k + 1` is decoded measurably from the restriction of the field to
`{|w| > k}`, then, for a law of fields whose area measure is almost surely finite on compacts, the
event `areaMap h S = ⊤` is almost surely equal to a set measurable for the exterior σ-algebra
`extSigma (k + 1)`. -/
theorem exists_extSigma_version_areaMap_eq_top {γ : ℝ} {μ : Measure Field}
    (hgood : ∀ᵐ h ∂μ, h ∈ ConeAreaCovariance.goodSet γ)
    (hfin : ∀ᵐ h ∂μ, IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ h))
    (hD : ∀ k : ℕ, ∃ D : LQGMetric.DistOn (extOpen (k : ℝ)) → Measure ℂ, Measurable D ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ,
        D (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (ConeAreaCovariance.areaMap γ h).restrict (extOpen ((k : ℝ) + 1)))
    {S : Set ℂ} (hS : MeasurableSet S) (k : ℕ) :
    ∃ A : Set Field, MeasurableSet[extSigma ((k : ℝ) + 1)] A ∧
      ∀ᵐ h ∂μ, (h ∈ A ↔ ConeAreaCovariance.areaMap γ h S = ⊤) := by
  obtain ⟨D, hDm, hDe⟩ := hD (k + 1)
  have hr : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_succ k
  have hm : Measurable[extSigma ((k + 1 : ℕ) : ℝ)]
      fun h : Field => D (LQGMetric.restrictTo (extOpen ((k + 1 : ℕ) : ℝ)) h) S :=
    ((Measure.measurable_coe hS).comp hDm).comp
      (comap_measurable (fun h : Field => LQGMetric.restrictTo (extOpen ((k + 1 : ℕ) : ℝ)) h))
  obtain ⟨A, hA, hAe⟩ : ∃ A : Set Field, MeasurableSet[extSigma ((k + 1 : ℕ) : ℝ)] A ∧
      ∀ᵐ h ∂μ, (h ∈ A ↔ ConeAreaCovariance.areaMap γ h S = ⊤) := by
    refine ⟨_, hm (measurableSet_singleton ⊤), ?_⟩
    filter_upwards [hgood, hfin] with h hg hf
    have := hf
    simp only [mem_preimage, mem_singleton_iff]
    rw [hDe h hg, Measure.restrict_apply hS]
    exact measure_inter_extOpen_eq_top_iff S _
  rw [hr] at hA
  exact ⟨A, hA, hAe⟩

/-- **Zero-one law for the infinite area of a set.** Under a trivial exterior tail, a measurable set
has almost surely infinite area or almost surely finite area. -/
theorem ae_areaMap_eq_top_or_ne_top {γ : ℝ} {μ : Measure Field} [IsProbabilityMeasure μ]
    (htail : LatticeProb.IsTrivialSigma (⨅ k : ℕ, extSigma ((k : ℝ) + 1)) μ)
    (hgood : ∀ᵐ h ∂μ, h ∈ ConeAreaCovariance.goodSet γ)
    (hfin : ∀ᵐ h ∂μ, IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ h))
    (hD : ∀ k : ℕ, ∃ D : LQGMetric.DistOn (extOpen (k : ℝ)) → Measure ℂ, Measurable D ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ,
        D (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (ConeAreaCovariance.areaMap γ h).restrict (extOpen ((k : ℝ) + 1)))
    {S : Set ℂ} (hS : MeasurableSet S) :
    (∀ᵐ h ∂μ, ConeAreaCovariance.areaMap γ h S = ⊤) ∨
      (∀ᵐ h ∂μ, ConeAreaCovariance.areaMap γ h S ≠ ⊤) := by
  classical
  obtain ⟨c, hc⟩ := exists_const_of_forall_extVersion (μ := μ)
    (F := fun h => if ConeAreaCovariance.areaMap γ h S = ⊤ then (1 : ℝ) else 0) htail fun k => by
    obtain ⟨A, hA, hAe⟩ := exists_extSigma_version_areaMap_eq_top hgood hfin hD hS k
    refine ⟨A.indicator fun _ => (1 : ℝ), ?_, ?_⟩
    · exact (Measurable.indicator measurable_const hA :
        Measurable[extSigma ((k : ℝ) + 1)] _).stronglyMeasurable
    · filter_upwards [hAe] with h hh
      by_cases h1 : ConeAreaCovariance.areaMap γ h S = ⊤
      · simp [h1, indicator_of_mem (hh.2 h1)]
      · simp [h1, indicator_of_notMem (fun hA' => h1 (hh.1 hA'))]
  by_cases hc1 : c = 1
  · left
    filter_upwards [hc] with h hh
    by_contra hne
    simp [hne] at hh
    exact absurd (hh.trans hc1) (by norm_num)
  · right
    filter_upwards [hc] with h hh hE
    simp [hE] at hh
    exact hc1 hh.symm

/-! ### Rotation of the sectors -/

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X₀ : Ω → Field}
  {b b' : ℝ≥0 → Ω → ℝ}

/-- **The rotation by `2π/8` carries the infinite area of a sector to the next sector.** -/
theorem ae_areaMap_a1Sector_succ_eq_top [IsProbabilityMeasure P] (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hX : LQGMetric.IsWholePlaneGFF X₀ P) (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (hXB : IndepFun X₀ (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P)
    (hbb : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P) (j : Fin 8)
    (hj : ∀ᵐ h ∂(P.map (zeroConeFieldOf γ X₀ b b')),
      ConeAreaCovariance.areaMap γ h (a1Sector j) = ⊤) :
    ∀ᵐ h ∂(P.map (zeroConeFieldOf γ X₀ b b')),
      ConeAreaCovariance.areaMap γ h (a1Sector (j + 1)) = ⊤ := by
  have hmp : MeasurePreserving (MoTPort.rotateField (2 * Real.pi / 8))
      (P.map (zeroConeFieldOf γ X₀ b b')) (P.map (zeroConeFieldOf γ X₀ b b')) :=
    ⟨MoTPort.measurable_rotateField _, map_rotateField_zeroConeFieldOf _ hγ hX hb hb' hXB hbb⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hj,
    ae_areaMap_rotateField (2 * Real.pi / 8) hγ hX hb hb' hXB hbb] with h h1 h2
  rwa [h2, Measure.map_apply (measurable_p48oRot _) (measurableSet_a1Sector j),
    preimage_p48oRot_a1Sector] at h1

end ZeroCone

/-- **The eight sectors have infinite area almost surely** (answer 58, section 3, first paragraph).
For the circle-average embedding `h = zeroConeFieldOf γ X₀' b b'` of the `0`-quantum cone, given the
tail triviality of the whole-plane GFF and the measurable decoder `hD` of the exterior area
(`exists_extArea_decoder`), if the area measure of `h` almost surely has infinite total mass and is
finite on compacts, then almost surely `areaMap γ h` gives infinite mass to each of the eight open
sectors `a1Sector j`. -/
theorem ae_a1Sector_eq_top (hT1a : WholePlaneGFFExteriorTailTrivial) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : LQGMetric.IsWholePlaneGFF X₀' P')
    (hb : IsBrownianReal b P') (hb' : IsBrownianReal b' P')
    (hi1 : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hi2 : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P')
    (hD : ∀ k : ℕ, ∃ D : LQGMetric.DistOn (extOpen (k : ℝ)) → Measure ℂ, Measurable D ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ,
        D (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (ConeAreaCovariance.areaMap γ h).restrict (extOpen ((k : ℝ) + 1)))
    (hinf : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      ConeAreaCovariance.areaMap γ h univ = ⊤)
    (hfin : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ h)) :
    ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), ∀ j : Fin 8,
      ConeAreaCovariance.areaMap γ h (a1Sector j) = ⊤ := by
  have hQ : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ.1
  have hfm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ConeAreaCovariance.aemeasurable_coneField_alpha hQ hX hb hb'
  have := hP
  have hgood : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hfm (ConeAreaCovariance.measurableSet_goodSet γ)).2
      (ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb')
  have htail := isTrivialSigma_zeroCone_extTail hT1a hγ P' X₀' b b' hP hX hb hb' hi1 hi2
  have hdich := fun j : Fin 8 =>
    ae_areaMap_eq_top_or_ne_top htail hgood hfin hD (measurableSet_a1Sector j)
  have hshift := fun j : Fin 8 => ae_areaMap_a1Sector_succ_eq_top hγ hX hb hb' hi1 hi2 j
  have hiter : ∀ j : Fin 8, (∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      ConeAreaCovariance.areaMap γ h (a1Sector j) = ⊤) → ∀ n : ℕ,
      ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
        ConeAreaCovariance.areaMap γ h (a1Sector ((fun x : Fin 8 => x + 1)^[n] j)) = ⊤ := by
    intro j hj n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hshift _ ih
  have hcover : ∀ j i : Fin 8, ∃ n : Fin 8, (fun x : Fin 8 => x + 1)^[(n : ℕ)] j = i := by decide
  by_cases hex : ∃ j : Fin 8, ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      ConeAreaCovariance.areaMap γ h (a1Sector j) = ⊤
  · obtain ⟨j, hj⟩ := hex
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨n, hn⟩ := hcover j i
    have := hiter j hj n
    rwa [hn] at this
  · exfalso
    have hne : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), ∀ j : Fin 8,
        ConeAreaCovariance.areaMap γ h (a1Sector j) ≠ ⊤ :=
      ae_all_iff.2 fun j => (hdich j).resolve_left fun hj => hex ⟨j, hj⟩
    have hfalse : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), False := by
      filter_upwards [hinf, hfin, hne] with h h1 h2 h3
      have := h2
      exact (measure_univ_lt_top_of_sectors h3).ne h1
    obtain ⟨h, hh⟩ := hfalse.exists
    exact hh

end MatedCRT
