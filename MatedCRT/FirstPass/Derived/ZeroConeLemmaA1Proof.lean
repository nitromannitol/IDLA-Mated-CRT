import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Local
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Average
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Exterior
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1SectorMass
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1PosProof

/-!
# Lemma A.1 of Gwynne–Miller–Sheffield for the circle-average zero cone, from Lemma A.4

`zeroConeCircleAverageLemmaA1_of_lemmaA4_of_tail` proves `ZeroConeCircleAverageLemmaA1` (arXiv:1705.11161,
Lemma A.1: a bounded, non-negative, measurable functional of the circle-average embedding of the `0`-quantum cone which
is almost surely invariant under all the coordinate changes `h ↦ h(C · + z) + Q log C` is almost surely constant)
from Lemma A.4 (`ZeroConeUniformRootLemmaA4`, the uniform root) and the tail triviality at infinity of the whole-plane
GFF modulo constants (`WholePlaneGFFExteriorTailTrivial`; Miller–Sheffield, Imaginary geometry IV, §2.2.1), following
the written answer 58:

* the exterior tail of the zero cone is trivial (`isTrivialSigma_zeroCone_extTail`, section 1, the instance of GMS
  Lemma A.3 used there);
* `F` is close in `L¹` to the average `A_m` of a local observation over the capped square `S_m` at every level `m`
  (`exists_rootObs_approx`, `integral_abs_sub_rootAverage_le`, section 2, from Lemma A.4);
* the eight sectors of the plane have infinite area (`ae_a1Sector_eq_top`), so far observations only see the field
  outside a fixed disc, and Cesàro averages of the exterior versions of `A_m` over the levels give, for every `k`, an
  approximation of `F` measurable with respect to the field outside the disc of radius `k + 1`
  (`exists_extVersion_approx`, section 3);
* hence `F` has a version measurable with respect to every exterior σ-algebra
  (`exists_stronglyMeasurable_version_of_approx`) and is almost surely constant
  (`exists_const_of_forall_extVersion`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-- **Lemma A.1 of Gwynne–Miller–Sheffield for the circle-average zero cone**, from Lemma A.4 and the tail triviality
at infinity of the whole-plane GFF modulo constants. -/
theorem zeroConeCircleAverageLemmaA1_of_lemmaA4_of_tail (hT1a : WholePlaneGFFExteriorTailTrivial) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) : ZeroConeCircleAverageLemmaA1 γ hγ := by
  intro Ω' mΩ' P' X₀' b b' hP hX hb hb' hXbb hbb' F hFm hFb hF0 hinv
  obtain ⟨K, hFK⟩ := hFb
  have hHm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ZeroConeRoot.aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hQ : (0 : ℝ) < MatedCRTHarmonic.CellScaling.lqgQ γ := MatedCRTHarmonic.LQGCoord.lqgQ_pos hγ.1
  have hgoodω : ∀ᵐ ω ∂P', zeroConeFieldOf γ X₀' b b' ω ∈ ConeAreaCovariance.goodSet γ :=
    ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb'
  have hgood : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hHm (ConeAreaCovariance.measurableSet_goodSet γ)).2 hgoodω
  have hMv := hgood.mono fun h hh => (ConeAreaCovariance.areaMap_spec hγ.1.ne' hh).1
  obtain ⟨hA2, -⟩ := hA4 P' X₀' b b' hP hX hb hb' hXbb hbb' (ConeAreaCovariance.areaMap γ)
    (ConeAreaCovariance.measurable_areaMap γ) hMv
  have hloc := hMv.mono fun _ hh => hh.1
  have hfin : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ h) :=
    hloc.mono fun _ hh => ⟨fun K hK => hh K hK⟩
  have hinf : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), ConeAreaCovariance.areaMap γ h univ = ⊤ :=
    (ae_mass_facts hloc hA2).mono fun _ hh => hh.2
  have hsec := ae_a1Sector_eq_top hT1a hγ P' X₀' b b' hP hX hb hb' hXbb hbb'
    (fun k => exists_extArea_decoder γ hγ.1.ne' k) hinf hfin
  have htail := isTrivialSigma_zeroCone_extTail hT1a hγ P' X₀' b b' hP hX hb hb' hXbb hbb'
  have hver : ∀ k : ℕ, ∃ g : Field → ℝ, StronglyMeasurable[extSigma ((k : ℝ) + 1)] g ∧
      F =ᵐ[P'.map (zeroConeFieldOf γ X₀' b b')] g := by
    intro k
    refine exists_stronglyMeasurable_version_of_approx (extSigma_le _) hFm.aemeasurable fun ε hε => ?_
    obtain ⟨a, f, b₀, hb₀, hfm, hf0, hfK, happrox⟩ := exists_rootObs_approx γ hγ P' X₀' b b' hP hX hb hb'
      hXbb hbb' hA4 hFm hF0 hFK hinv (half_pos hε)
    have hR3 := integral_abs_sub_rootAverage_le γ hγ P' X₀' b b' hP hX hb hb' hXbb hbb' hA4 hFm hF0 hFK
      hinv hfm hf0 hfK happrox
    obtain ⟨g, hgm, hgi⟩ := exists_extVersion_approx γ hFm hF0 hFK hfm hf0 hfK hgood hsec hfin hA2 hR3
      (k + 1) (exists_extArea_decoder γ hγ.1.ne' (k + 1))
      (exists_rootObs_extVersion γ hγ.1.ne' hfm hb₀ (k + 1)) (half_pos hε)
    have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    refine ⟨g, ?_, ?_⟩
    · rw [← hk]
      exact hgm
    · simpa only [add_halves] using hgi
  obtain ⟨c, hc⟩ := exists_const_of_forall_extVersion htail hver
  have hc' : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), F h = c := hc
  exact ⟨c, (ae_map_iff hHm (measurableSet_eq_fun hFm measurable_const)).1 hc'⟩

end MatedCRT
