import MatedCRT.FirstPass.Derived.NormalizedGFFIndependentTrace
import LatticeProb.LQG.NormalizedSpliceArea

/-! # Independent traces and normalized radial splices -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic MatedCRTHarmonic.GMCFacts
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace MatedCRT

/-- A cone area does not charge the unit-disk part of a planar-null trace
jointly independent of the normalized replacement field and its radial path. -/
theorem ae_coneArea_range_eq_zero_of_normalized_splice
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXB : IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P)
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hWp : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g)
    (hind : IndepFun (fun ω => (replField X
      (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω,
      W ω)) g P)
    (hnull : ∀ᵐ ω ∂P, volume (range (g ω)) = 0) :
    ∀ᵐ ω ∂P, lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
      (fun t => B' t ω)) (range (g ω) ∩ ball (0 : ℂ) 1) = 0 := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  let Y : Ω → DistC := replField X (fun ω => twoSided (W ω)
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)
  have hY : IsNormalizedWPGFF Y P :=
    LatticeProb.LQG.IsWholePlaneGFF.normalized_replField_twoSided hX hRm hR hWm hWp hXW
  have hi : IndepFun g Y P := (hind.comp measurable_fst measurable_id).symm
  have hl := LatticeProb.LQG.ae_normalized_splice_area_and_cone_restrict hγ hγ2 hX hB hB' hBB' hXB
    hRm hR hWm hWp hXW hW
  have heach : ∀ n : ℕ, ∀ᵐ ω ∂P,
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))
        ((g ω '' Icc (-(n : ℝ)) n) ∩ ball (0 : ℂ) 1) = 0 := by
    intro n
    have ht := ae_normalizedGFF_insertedArea_trace_eq_zero (T := Icc (-(n : ℝ)) n) hY hγ hγ2
      (lt_lqgQ hγ hγ2) hgm hi isCompact_Icc
      (hnull.mono fun ω hω => measure_mono_null (image_subset_range _ _) hω)
    filter_upwards [ht, hl] with ω htω hlω
    have hm : MeasurableSet (g ω '' Icc (-(n : ℝ)) n) :=
      (isCompact_Icc.image (g ω).continuous).isClosed.measurableSet
    have heq := congrArg (fun μ : Measure ℂ => μ (g ω '' Icc (-(n : ℝ)) n))
      (hlω.2 (ballO (0 : ℂ) 1) (Subset.rfl))
    rw [Measure.restrict_apply hm, Measure.restrict_apply hm] at heq
    exact heq.trans htω
  filter_upwards [ae_all_iff.mpr heach] with ω hω
  have hrange : range (g ω) = ⋃ n : ℕ, g ω '' Icc (-(n : ℝ)) n := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt |t|
      refine mem_iUnion.mpr ⟨n, t, ⟨?_, ?_⟩, rfl⟩
      · linarith [neg_abs_le t]
      · linarith [le_abs_self t]
    · intro hz
      obtain ⟨n, t, ht, rfl⟩ := mem_iUnion.mp hz
      exact ⟨t, rfl⟩
  rw [hrange, iUnion_inter]
  exact measure_iUnion_null hω

end MatedCRT
