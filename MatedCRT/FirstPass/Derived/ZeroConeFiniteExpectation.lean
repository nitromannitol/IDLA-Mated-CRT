import MatedCRT.FirstPass.Derived.GMSConditionTwoImpliesFive
import MatedCRT.FirstPass.Derived.ZeroConeRootFiniteExpectation
import LatticeProb.Prob.CellConfigRootedMomentMap
import LatticeProb.Prob.CellConfigRootedEnumeration
import LatticeProb.Prob.CorrelatedBMContourFiber
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The hypotheses of the invariance principle for the shifted zero-cone cell configuration

Gwynne, Miller and Sheffield (*The Tutte embedding of the mated-CRT map converges to Liouville
quantum gravity*, arXiv:1705.11161, Proposition 3.1) verify the hypotheses of the invariance
principle of arXiv:1807.07515 (Theorem 1.16) for the cell configuration (3.1): the unit-mass cells
`η₀([x - 1 + θ, x + θ])`, `x ∈ ℤ`, of the space-filling curve of the zero cone, with a uniform
phase `θ ∈ [0, 1]` and the contour edge counts as conductances.

This file proves the finite-expectation hypothesis (1.5) of arXiv:1807.07515 for the law of every
realization of the configuration in the GMS space: almost surely `η₀` visits `0 = η₀(0)` only at
time `0` and `θ ∈ (0, 1)`, so the only cell containing the origin is the root cell `η₀([θ - 1, θ])`,
whose conductances are at most `2` and nonzero only for cells meeting it; the bound
`diam(H₀)² / area(H₀) · π(H₀) ≤ 2 diamAreaSup(η₀) (degInner η₀ + degOuter η₀)` and the moment
bounds of arXiv:1705.11161, Propositions 4.4 and 4.6 (`ZeroConeRoot.lintegral_diamAreaSup_mul_deg_lt_top`)
give the finite expectation. Together with the mass-transport principle, the ergodicity modulo
scaling and the connectedness along lines, this gives the four hypotheses of Theorem 1.16 for the
law of every realization (`exists_zeroCone_config_gmsHypotheses`), from the spatial-average
invariance and the tail triviality of the zero cone and Appendix B's Condition 2 ⇒ Condition 5.
-/

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal NNReal

section Deterministic

open MatedCRTHarmonic.MatedCRT (degInner degOuter diamAreaSup)

/-- The `k`-th unit-mass cell of a curve shifted in time by `θ` is `c([k - 1 + θ, k + θ])`. -/
theorem cell_one_timeShift (c : ℝ → ℂ) (θ : ℝ) (k : ℤ) :
    cell 1 (fun t => c (t + 1 * θ)) k = c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) := by
  unfold cell
  rw [show (fun t => c (t + 1 * θ)) = c ∘ (fun t => t + θ) from funext fun t => by simp,
    Set.image_comp, Set.image_add_const_Icc]
  have e1 : 1 * ((k : ℝ) - 1) + θ = (k : ℝ) - 1 + θ := by ring
  have e2 : 1 * (k : ℝ) + θ = (k : ℝ) - 1 + θ + 1 := by ring
  rw [e1, e2]

/-- The rooted area ratio of a curve cell is at most `diam² / area` of the cell in `ℂ`. -/
theorem originAreaRatio_euclideanCell_le_diam_sq_div {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ}
    (hε : 0 < ε) (k : ℤ) :
    originAreaRatio (euclideanCell ε η hη hε k) ≤
      ENNReal.ofReal (Metric.diam (cell ε η k) ^ 2) / volume (cell ε η k) := by
  let K := euclideanCell ε η hη hε k
  have hd : Metric.diam (K : Set ReflectedGMS.Plane) = Metric.diam (cell ε η k) := by
    change Metric.diam (Complex.orthonormalBasisOneI.repr '' cell ε η k) = _
    exact Complex.orthonormalBasisOneI.repr.isometry.diam_image _
  have hv : volume (K : Set ReflectedGMS.Plane) = volume (cell ε η k) := by
    change volume (Complex.orthonormalBasisOneI.repr.toLinearEquiv.toEquiv '' cell ε η k) = _
    rw [Equiv.image_eq_preimage_symm]
    change volume (Complex.orthonormalBasisOneI.repr.symm ⁻¹' cell ε η k) = _
    exact Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
      ((isCompact_Icc.image hη).isClosed.measurableSet.nullMeasurableSet)
  have hfin : volume (cell ε η k) ≠ ∞ := (isCompact_Icc.image hη).measure_ne_top
  have hquot : ENNReal.ofReal (Metric.diam (cell ε η k) ^ 2 / (volume (cell ε η k)).toReal) ≤
      ENNReal.ofReal (Metric.diam (cell ε η k) ^ 2) / volume (cell ε η k) := by
    by_cases hz : volume (cell ε η k) = 0
    · simp [hz]
    · rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hz hfin), ENNReal.ofReal_toReal hfin]
  unfold originAreaRatio
  by_cases hz : (0 : ReflectedGMS.Plane) ∈ (K : Set ReflectedGMS.Plane)
  · rw [Set.indicator_of_mem (show K ∈ {K : Cell | (0 : ReflectedGMS.Plane) ∈
        (K : Set ReflectedGMS.Plane)} from hz)]
    change ENNReal.ofReal (Metric.diam (K : Set ReflectedGMS.Plane) ^ 2 /
      (volume (K : Set ReflectedGMS.Plane)).toReal) ≤ _
    rw [hd, hv]
    exact hquot
  · rw [Set.indicator_of_notMem (show K ∉ {K : Cell | (0 : ReflectedGMS.Plane) ∈
        (K : Set ReflectedGMS.Plane)} from hz)]
    exact bot_le

/-- The conductances of the shifted area cells are `0` or at least `1`. -/
theorem shiftedAreaCellConfig_conductance_eq_zero_or_one_le {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ) (A B : Cell) :
    (shiftedAreaCellConfig h hε θ m).c A B = 0 ∨ 1 ≤ (shiftedAreaCellConfig h hε θ m).c A B := by
  classical
  unfold shiftedAreaCellConfig
  dsimp only
  split_ifs with ha hb
  · by_cases hz : m ((shiftedEuclideanCellEquiv h hε θ).symm ⟨A, ha⟩)
        ((shiftedEuclideanCellEquiv h hε θ).symm ⟨B, hb⟩) = 0
    · left
      rw [hz, Nat.cast_zero]
    · right
      exact Nat.one_le_cast_iff_ne_zero.mpr hz
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- The contour edge counts are at most `2`. -/
theorem bmEdgeCount_le_two (ε : ℝ) (L R : ℝ → ℝ) (j k : ℤ) : bmEdgeCount ε L R j k ≤ 2 := by
  simp only [bmEdgeCount]
  split_ifs <;> norm_num

/-- The rooted row sum of a shifted area-cell configuration, indexed by the integer labels of the
cells. -/
theorem originRowSum_eq_shiftedAreaCell_tsum {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ) (H : GMSSpace)
    (hH : H.1 = shiftedAreaCellConfig h hε θ m) :
    originRowSum id H = ∑' k : ℤ, originAreaRatio (shiftedEuclideanCellEquiv h hε θ k : Cell) *
      ENNReal.ofReal (∑' b : ℤ, (m k b : ℝ)) := by
  cases H with
  | mk C hC =>
    cases hH
    change originRowSum id ⟨shiftedAreaCellConfig h hε θ m, hC⟩ = _
    rw [originRowSum_eq_tsum_cells ⟨shiftedAreaCellConfig h hε θ m, hC⟩
      (shiftedEuclideanCellEquiv h hε θ)]
    refine tsum_congr fun k => ?_
    change originAreaRatio (shiftedEuclideanCellEquiv h hε θ k : Cell) *
      ENNReal.ofReal ((shiftedAreaCellConfig h hε θ m).pi (shiftedEuclideanCellEquiv h hε θ k)) = _
    congr 2
    unfold CellConfig.pi
    calc
      _ = ∑' b : ℤ, (shiftedAreaCellConfig h hε θ m).c
          (shiftedEuclideanCellEquiv h hε θ k) (shiftedEuclideanCellEquiv h hε θ b) :=
        ((shiftedEuclideanCellEquiv h hε θ).tsum_eq _).symm
      _ = _ := tsum_congr (shiftedAreaCellConfig_conductance h hε θ m k)

/-- **The root cell bound.** For a curve `c` with `c 0 = 0` visiting `0` only at time `0`, a phase
`θ ∈ (0, 1)` and conductances `m 0 b ≤ 2` from the root cell, the rooted row sum of the shifted
unit-mass cell configuration is at most `2 diamAreaSup(c) (degInner c + degOuter c)`: only the root
cell `c([θ - 1, θ])` contains the origin. -/
theorem originRowSum_shiftedAreaCell_le {μ : Measure ℂ} {c : C(ℝ, ℂ)} (h : IsAreaParametrized μ c)
    (hc0 : c 0 = 0) (hfib : ∀ t, c t = c 0 → t = 0) (hD : 0 < Metric.diam (c '' Icc (-1) 1))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (m : ℤ → ℤ → ℕ) (hm2 : ∀ b, m 0 b ≤ 2) (H : GMSSpace)
    (hH : H.1 = shiftedAreaCellConfig h one_pos θ m) :
    originRowSum id H ≤ 2 * (diamAreaSup c * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞))) := by
  have hcell : ∀ k : ℤ, ((shiftedEuclideanCellEquiv h one_pos θ k : Cell) : Set ReflectedGMS.Plane) =
      Complex.orthonormalBasisOneI.repr '' cell 1 (fun t => c (t + 1 * θ)) k := fun _ => rfl
  have e1 : ((0 : ℤ) : ℝ) - 1 + θ = θ - 1 := by rw [Int.cast_zero]; ring
  have e2 : ((0 : ℤ) : ℝ) - 1 + θ + 1 = θ := by rw [Int.cast_zero]; ring
  have hzero : ∀ k : ℤ, (0 : ReflectedGMS.Plane) ∈
      ((shiftedEuclideanCellEquiv h one_pos θ k : Cell) : Set ReflectedGMS.Plane) → k = 0 := by
    intro k hk
    rw [hcell k, cell_one_timeShift c θ k] at hk
    obtain ⟨x, ⟨t, ht, rfl⟩, hx⟩ := hk
    have hct : c t = 0 :=
      Complex.orthonormalBasisOneI.repr.injective (hx.trans (map_zero _).symm)
    have ht0 : t = 0 := hfib t (hct.trans hc0.symm)
    subst ht0
    obtain ⟨h1, h2⟩ := ht
    have hk1 : (k : ℝ) < 1 := by linarith [hθ.1]
    have hk2 : (-1 : ℝ) < k := by linarith [hθ.2]
    have hk1' : k < 1 := by exact_mod_cast hk1
    have hk2' : -1 < k := by exact_mod_cast hk2
    omega
  have hratio : originAreaRatio (shiftedEuclideanCellEquiv h one_pos θ 0 : Cell) ≤ diamAreaSup c := by
    refine (originAreaRatio_euclideanCell_le_diam_sq_div (η := fun t => c (t + 1 * θ))
      (h.1.comp (continuous_id.add continuous_const)) one_pos 0).trans ?_
    rw [cell_one_timeShift c θ 0, e2, e1]
    exact le_iSup₂ (f := fun s (_ : s ∈ Icc (0 : ℝ) 1) =>
      ENNReal.ofReal (Metric.diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)) θ
      ⟨hθ.1.le, hθ.2.le⟩
  have hsupp : ∀ b, m 0 b ≠ 0 →
      (c '' Icc ((b : ℝ) - 1 + θ) ((b : ℝ) - 1 + θ + 1) ∩ c '' Icc (θ - 1) θ).Nonempty := by
    intro b hb
    have hadj : H.1.Adj (shiftedEuclideanCellEquiv h one_pos θ 0 : Cell)
        (shiftedEuclideanCellEquiv h one_pos θ b : Cell) := by
      show 0 < H.1.c _ _
      rw [hH, shiftedAreaCellConfig_conductance]
      exact_mod_cast Nat.pos_of_ne_zero hb
    obtain ⟨x, hx0, hxb⟩ := H.2.adj_inter _ _ hadj
    rw [hcell 0, cell_one_timeShift c θ 0, e2, e1] at hx0
    rw [hcell b, cell_one_timeShift c θ b] at hxb
    obtain ⟨y, hy, rfl⟩ := hx0
    obtain ⟨y', hy', hyy⟩ := hxb
    rw [Complex.orthonormalBasisOneI.repr.injective hyy] at hy'
    exact ⟨y, hy', hy⟩
  have hrow : ENNReal.ofReal (∑' b : ℤ, (m 0 b : ℝ)) ≤ ∑' b, (m 0 b : ℝ≥0∞) := by
    by_cases hs : Summable (fun b : ℤ => (m 0 b : ℝ))
    · rw [ENNReal.ofReal_tsum_of_nonneg (fun b => Nat.cast_nonneg _) hs]
      exact le_of_eq (tsum_congr fun b => ENNReal.ofReal_natCast _)
    · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
      exact zero_le
  have hsingle : ∑' k : ℤ, originAreaRatio (shiftedEuclideanCellEquiv h one_pos θ k : Cell) *
      ENNReal.ofReal (∑' b : ℤ, (m k b : ℝ)) =
      originAreaRatio (shiftedEuclideanCellEquiv h one_pos θ 0 : Cell) *
        ENNReal.ofReal (∑' b : ℤ, (m 0 b : ℝ)) := by
    refine tsum_eq_single 0 fun k hk => ?_
    have h0 : originAreaRatio (shiftedEuclideanCellEquiv h one_pos θ k : Cell) = 0 := by
      unfold originAreaRatio
      rw [Set.indicator_of_notMem]
      exact fun h0 => hk (hzero k h0)
    rw [h0, zero_mul]
  rw [originRowSum_eq_shiftedAreaCell_tsum h one_pos θ m H hH, hsingle]
  calc originAreaRatio (shiftedEuclideanCellEquiv h one_pos θ 0 : Cell) *
        ENNReal.ofReal (∑' b : ℤ, (m 0 b : ℝ))
      ≤ diamAreaSup c * (2 * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞))) :=
        mul_le_mul' hratio (hrow.trans (ZeroConeRoot.tsum_le_two_mul_degInner_add_degOuter hc0 hD
          hθ.1.le hθ.2.le (m 0) hm2 hsupp))
    _ = 2 * (diamAreaSup c * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞))) := by ring

end Deterministic

section ZeroCone

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- On a mating-of-trees coupling, almost surely the zero-cone curve visits `η₀(0)` only at time `0`
(the same holds for the `γ`-cone curve by the contour relation of its boundary-length pair, and both
curves are increasing reparametrizations, fixing time `0`, of the same space-filling curve). -/
theorem ae_zeroCone_singleton_fiber
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ t, η₀ ω t = η₀ ω 0 → t = 0 := by
  have hf : ∀ᵐ ω ∂P, ∀ t, η ω t = η ω 0 → t = 0 := by
    apply LatticeProb.CorrelatedBM.ae_singleton_fiber_of_contour_relation
      D.measurable_curves.2.2.2.aemeasurable D.boundaryLawBM 0
    filter_upwards [D.onlyMerge] with ω hω t ht
    exact hω 0 t ht.symm
  filter_upwards [hf, D.areaParam, D.areaParam₀] with ω hfω hA hA₀ t ht
  obtain ⟨⟨φ, hφ0, hφ⟩, -⟩ := hA
  obtain ⟨⟨φ₀, hφ₀0, hφ₀⟩, -⟩ := hA₀
  have h1 : ηL ω (φ₀ t) = ηL ω 0 := by
    have h0 := hφ₀ 0
    rw [hφ₀0] at h0
    rw [← hφ₀ t, ht, h0]
  have h2 : η ω (φ.symm (φ₀ t)) = η ω 0 := by
    rw [hφ, hφ, φ.apply_symm_apply, hφ0, h1]
  have h3 : φ.symm (φ₀ t) = 0 := hfω _ h2
  have h4 : φ₀ t = 0 := by
    calc φ₀ t = φ (φ.symm (φ₀ t)) := (φ.apply_symm_apply _).symm
      _ = 0 := by rw [h3, hφ0]
  exact φ₀.injective (h4.trans hφ₀0.symm)

/-- **The finite-expectation hypothesis for the shifted zero-cone configuration** (hypothesis (1.5)
of Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16, as verified in arXiv:1705.11161,
Proposition 3.1, from Propositions 4.4 and 4.6 there): the law of every realization of the
configuration (3.1) in the GMS space satisfies `FiniteExpectation`. -/
theorem finiteExpectation_map_of_zeroConeConfigRealization
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} {F : Ω × ℝ → GMSSpace} (hF : IsZeroConeConfigRealization D hγ G F) :
    FiniteExpectation ((P.prod zeroConePhase).map F) := by
  have := D.isProbabilityMeasure
  apply finiteExpectation_map_of_originRowSum (P.prod zeroConePhase) F hF.2.2.1
  · filter_upwards [hF.2.2.2] with p hp K K'
    obtain ⟨h, hFp⟩ := hp
    rw [hFp]
    exact shiftedAreaCellConfig_conductance_eq_zero_or_one_le h one_pos p.2 _ K K'
  · have hphase : ∀ᵐ θ ∂zeroConePhase, θ ∈ Ioo (0 : ℝ) 1 := by
      have hQ : zeroConePhase ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
      filter_upwards [ae_restrict_mem measurableSet_Icc, hQ.ae_le (Measure.ae_ne volume 0),
        hQ.ae_le (Measure.ae_ne volume 1)] with θ hθ h0 h1
      exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 h1⟩
    have hω : ∀ᵐ ω ∂P, (η₀ ω 0 = 0 ∧ 0 < Metric.diam (η₀ ω '' Icc (-1) 1)) ∧
        ∀ t, η₀ ω t = η₀ ω 0 → t = 0 :=
      D.ae_zeroCone_root_regular.and (ae_zeroCone_singleton_fiber D)
    have hbound : ∀ᵐ p ∂P.prod zeroConePhase, originRowSum id (F p) ≤
        2 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) + (degOuter (η₀ p.1) : ℝ≥0∞))) := by
      filter_upwards [hF.2.2.2, (Measure.quasiMeasurePreserving_fst (μ := P) (ν := zeroConePhase)).ae hω,
        (Measure.quasiMeasurePreserving_snd (μ := P) (ν := zeroConePhase)).ae hphase]
        with p hp hreg hθ
      obtain ⟨h, hFp⟩ := hp
      obtain ⟨⟨h0, hD⟩, hfib⟩ := hreg
      have hm2 : ∀ b, bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1)
          (fun t => (G p.1 (t + 1 * p.2)).2) 0 b ≤ 2 := fun b => bmEdgeCount_le_two _ _ _ _ b
      exact originRowSum_shiftedAreaCell_le h h0 hfib hD hθ _ hm2 (F p) hFp
    calc ∫⁻ p, originRowSum id (F p) ∂(P.prod zeroConePhase)
        ≤ ∫⁻ p, 2 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) +
            (degOuter (η₀ p.1) : ℝ≥0∞))) ∂(P.prod zeroConePhase) := lintegral_mono_ae hbound
      _ ≤ ∫⁻ ω, ∫⁻ _ : ℝ, 2 * (diamAreaSup (η₀ ω) * ((degInner (η₀ ω) : ℝ≥0∞) +
            (degOuter (η₀ ω) : ℝ≥0∞))) ∂zeroConePhase ∂P := lintegral_prod_le _
      _ = 2 * ∫⁻ ω, diamAreaSup (η₀ ω) * ((degInner (η₀ ω) : ℝ≥0∞) + (degOuter (η₀ ω) : ℝ≥0∞)) ∂P := by
        simp only [lintegral_const, measure_univ, mul_one]
        exact lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top
        (ZeroConeRoot.lintegral_diamAreaSup_mul_deg_lt_top hγ.1 hγ.2 D.measurable_curves.2.2.1
          D.cellMoments)

/-- **The hypotheses of the invariance principle for the shifted zero-cone configuration**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Proposition 3.1; hypotheses of arXiv:1807.07515,
Theorem 1.16). Let `0 < γ < 2` and let the field of the `γ`-cone be almost measurable. The
configuration (3.1) of arXiv:1705.11161 (unit-area cells `η₀([x - 1 + θ, x + θ])` of the zero-cone
curve, contour edge counts of the transported boundary-length pair `G = bm ∘ ψ`, phase `θ` uniform on
`[0, 1]`) is almost surely a cell configuration with an almost measurable code, and, under the
spatial-average invariance and the tail triviality of the zero cone and Appendix B's Condition 2 ⇒
Condition 5 of arXiv:1807.07515, the law of every realization in the GMS space satisfies the
mass-transport principle, is ergodic modulo scaling, satisfies the finite-expectation hypothesis and
is connected along lines. -/
theorem exists_zeroCone_config_gmsHypotheses
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hT : ZeroConeTailTriviality D hγ) :
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
          ConnectedAlongLines ((P.prod zeroConePhase).map F) := by
  obtain ⟨G, H, hH, hcode, hall⟩ :=
    exists_zeroCone_config_ergodicModuloScaling_connectedAlongLines D hγ hf
  refine ⟨G, H, hH, hcode, fun F hFm hFeq => ?_⟩
  obtain ⟨hreal, hconn, herg⟩ := hall F hFm hFeq
  exact ⟨hreal, massTransport_map_of_zeroConeSpatialAverageInvariance D hγ hI h25 hreal, herg hT,
    finiteExpectation_map_of_zeroConeConfigRealization D hγ hreal, hconn⟩

end ZeroCone

end MatedCRT
