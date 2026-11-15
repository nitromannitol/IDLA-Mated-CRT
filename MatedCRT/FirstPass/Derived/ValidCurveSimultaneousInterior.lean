import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.ProperAreaCurveFrontier

/-! # Simultaneous interior visits of valid curves -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- In a valid environment, almost every time visits the interior of every
segment strictly containing that time. The exceptional time set is common to
all such segments and may depend on the environment. -/
theorem MatedCRTEnv.IsValid.ae_simultaneous_interior_visits
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ u ∂volume, ∀ a b : ℝ, a < u → u < b →
      S.η ω u ∈ interior (S.η ω '' Icc a b) := by
  obtain ⟨η, _, hη⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  filter_upwards [hη] with ω hω
  rcases hω with ⟨heq, hp, hs, hm, hmap⟩
  have hrat : ∀ᵐ u ∂volume, ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      u ∈ Icc (p : ℝ) (q : ℝ) → η ω u ∈ interior (η ω '' Icc (p : ℝ) (q : ℝ)) := by
    apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    by_cases hpq : (p : ℝ) < (q : ℝ)
    · have hfront := LatticeProb.measure_frontier_image_Icc_eq_zero_of_proper
        (η ω) (S.μ ω) (η ω).continuous hp hs (fun a b hab => hm a b hab.le) hpq
      have hae := interior_ae_eq_of_null_frontier hfront
      rw [hmap] at hae
      have hae' := ae_of_ae_map (η ω).continuous.measurable.aemeasurable hae
      filter_upwards [hae'] with u hu _ hui
      exact hu.mpr ⟨u, hui, rfl⟩
    · exact Filter.Eventually.of_forall fun _ h _ => (hpq h).elim
  filter_upwards [hrat] with u hu a b hau hub
  obtain ⟨p, hap, hpu⟩ := exists_rat_btwn hau
  obtain ⟨q, huq, hqb⟩ := exists_rat_btwn hub
  have hsub : Icc (p : ℝ) (q : ℝ) ⊆ Icc a b := Icc_subset_Icc hap.le hqb.le
  have h := interior_mono (image_mono hsub) (hu p q (hpu.trans huq) ⟨hpu.le, huq.le⟩)
  simpa only [heq] using h

end MatedCRT.FirstPass.Derived
