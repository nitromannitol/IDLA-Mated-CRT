import MatedCRT.FirstPass.Derived.CellDiamUniform
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import LatticeProb.Prob.LawKernelTightness
import LatticeProb.Prob.PathModulusContinuity

/-!
# Scales uniform in the mesh index

For the tightness of the interpolated quenched walk laws we need scales that work for **all** mesh
sizes `ε_n`, not only for large `n`.  Both events below (large cell diameters in a ball, and a
vertex of the ball whose walk path law has a large modulus failure) are null-measurable, increase
with the scale, have exactly empty intersection over the positive scales for every `n` (finitely
many vertices in a ball for a proper onto curve; uniform continuity of a path on `[0, L]`), and are
eventually small; the passage from large indices to all indices
(`LatticeProb.exists_scale_forall_of_eventually`) gives one scale.

* `exists_cellDiam_scale_forall`: one threshold `D ≥ 1` with
  `P(diam^{ε_n}_R > D) ≤ c` for every `n`;
* `vertexPathFailure`, `exists_vertexPathFailure_scale_forall`: one scale `δ > 0` with
  `P(∃ vertex in B_{R+1}, Q^{ε_n}(vertex)(modulus failure of level L at scale δ) > a) ≤ a` for
  every `n`, from the same bound for large `n`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Cell diameters, uniformly in the mesh index.**  For every `R` and `c > 0` there is a
threshold `D ≥ 1` such that the largest diameter of the cells meeting `B_R` exceeds `D` with
probability at most `c`, for every mesh size `ε_n`. -/
theorem exists_cellDiam_scale_forall {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0)) (R : ℝ) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ n, S.P {ω | ENNReal.ofReal D < maxCellDiam (eps n) (⇑(η' ω)) R} ≤ c := by
  have hprop := ae_mem_properCurveSet hS hae
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨δ, hδ, hall⟩ := exists_scale_forall_of_eventually (fun _ : ℕ => S.P)
    (fun n δ => cellDiamBig η' (eps n) R δ)
    (fun n δ => nullMeasurableSet_cellDiamBig hη' hprop (eps n) R δ)
    (fun n δ δ' h => cellDiamBig_mono η' (eps n) R h)
    (fun n => iInter_cellDiamBig_eq_empty η' (hε0 n) R) hc
    ⟨1, one_pos, eventually_prob_cellDiamBig_le hS hae hε0 hε R hc⟩
  refine ⟨max δ⁻¹ 1, le_max_right _ _, fun n => ?_⟩
  refine le_trans (measure_mono_ae (t := cellDiamBig η' (eps n) R δ) ?_) (hall n)
  filter_upwards [hprop] with ω hω hlt
  refine And.intro hω (lt_of_le_of_lt ?_ hlt)
  rw [← ENNReal.ofReal_inv_of_pos hδ]
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- The event that the quenched interpolated walk law started from some vertex in the ball
`B_{R+1}` charges the modulus failure of level `L` at scale `δ` with probability above `a`. -/
def vertexPathFailure (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε R L a : ℝ) (δ : ℝ≥0) : Set Ω :=
  {ω | ∃ j : ℤ, vertexPoint ε (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
    ENNReal.ofReal a <
      ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (pathModulusFailure (E := ℂ) L δ)}

theorem measurableSet_vertexPathFailure {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (ε R L a : ℝ) (δ : ℝ≥0) :
    MeasurableSet (vertexPathFailure S η' ε R L a δ) := by
  have h : vertexPathFailure S η' ε R L a δ = ⋃ j : ℤ,
      {ω | vertexPoint ε (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1)} ∩
      {ω | ENNReal.ofReal a <
        ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω :
          ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
          (pathModulusFailure (E := ℂ) L δ)} := by
    ext ω
    simp [vertexPathFailure]
  rw [h]
  refine MeasurableSet.iUnion fun j => MeasurableSet.inter ?_ ?_
  · exact ((measurable_pi_apply j).comp (measurable_vertexPoint_curve hη' ε)) measurableSet_ball
  · have hm : Measurable fun ω =>
        ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω :
          ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
          (pathModulusFailure (E := ℂ) L δ) :=
      (Measure.measurable_coe (isOpen_pathModulusFailure L δ).measurableSet).comp
        (measurable_subtype_coe.comp
          (measurable_walkPathLaw hS (measurable_vertexPoint_curve hη' ε) (S.mε_nonneg ε) ε j))
    exact measurableSet_lt measurable_const hm

theorem vertexPathFailure_mono (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε R L a : ℝ)
    {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    vertexPathFailure S η' ε R L a δ ⊆ vertexPathFailure S η' ε R L a δ' := by
  rintro ω ⟨j, hj, hlt⟩
  exact ⟨j, hj, lt_of_lt_of_le hlt (measure_mono (pathModulusFailure_mono_scale L h))⟩

/-- On a proper onto curve, the vertex path failures have empty intersection over the positive
scales: finitely many vertices lie in the ball and each path law has no failure at small scales. -/
theorem iInter_vertexPathFailure_eq_empty (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ}
    (hε : 0 < ε) (R : ℝ) {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    (⋂ δ > (0 : ℝ), (properCurveSet η' ∩ vertexPathFailure S η' ε R L a δ.toNNReal)) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
  simp only [mem_iInter] at hω
  have hprop : ω ∈ properCurveSet η' := (hω 1 one_pos).1
  have hfin := finite_vertices_in_ball hε hprop.1 hprop.2 (R + 1)
  obtain ⟨δ, hδ, hlt⟩ := exists_scale_lt_of_finite hfin
    (fun j δ => ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (pathModulusFailure (E := ℂ) L δ.toNNReal))
    (fun j _ => tendsto_measure_pathModulusFailure _ hL) (a := ENNReal.ofReal a)
    (ENNReal.ofReal_pos.2 ha)
  obtain ⟨j, hj, hgt⟩ := (hω δ hδ).2
  exact absurd (hlt j hj) (not_lt.2 hgt.le)

/-- **Vertex path failures, uniformly in the mesh index.**  If at some scale the failure event has
probability at most `ofReal a` for all large `n`, then at some (possibly smaller) positive scale it
has probability at most `ofReal a` for every `n`. -/
theorem exists_vertexPathFailure_scale_forall {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (R : ℝ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a)
    (hev : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ᶠ n in atTop, S.P (vertexPathFailure S η' (eps n) R L a δ) ≤ ENNReal.ofReal a) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ n, S.P (vertexPathFailure S η' (eps n) R L a δ) ≤ ENNReal.ofReal a := by
  have hprop := ae_mem_properCurveSet hS hae
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨δ₀, hδ₀, hev'⟩ := hev
  obtain ⟨d, hd, hall⟩ := exists_scale_forall_of_eventually (fun _ : ℕ => S.P)
    (fun n d => properCurveSet η' ∩ vertexPathFailure S η' (eps n) R L a d.toNNReal)
    (fun n d => (nullMeasurableSet_properCurveSet hprop).inter
      (measurableSet_vertexPathFailure hS hη' _ _ _ _ _).nullMeasurableSet)
    (fun n d d' h => inter_subset_inter_right _
      (vertexPathFailure_mono S η' (eps n) R L a (Real.toNNReal_le_toNNReal h)))
    (fun n => iInter_vertexPathFailure_eq_empty S η' (hε0 n) R hL ha)
    (c := ENNReal.ofReal a) (ENNReal.ofReal_pos.2 ha)
    ⟨(δ₀ : ℝ), by exact_mod_cast hδ₀, hev'.mono fun n hn => by
      show S.P (properCurveSet η' ∩ vertexPathFailure S η' (eps n) R L a (δ₀ : ℝ).toNNReal) ≤ _
      rw [Real.toNNReal_coe]
      exact le_trans (measure_mono Set.inter_subset_right) hn⟩
  refine ⟨d.toNNReal, Real.toNNReal_pos.2 hd, fun n => ?_⟩
  refine le_trans (measure_mono_ae
    (t := properCurveSet η' ∩ vertexPathFailure S η' (eps n) R L a d.toNNReal) ?_) (hall n)
  filter_upwards [hprop] with ω hω h
  exact And.intro hω h

end MatedCRT.FirstPass.Derived
