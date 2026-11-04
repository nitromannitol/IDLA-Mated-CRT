import MatedCRT.Proofs.Sec5.LLowerBound.ModulusProb

/-! Uniform positive local mass in probability from area parametrization. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Uniformly over a bounded region, the LQG mass of a fixed-radius ball is
larger than a deterministic threshold with probability tending to one as
the threshold decreases to zero. -/
theorem MatedCRTEnv.IsValid.tendsto_measure_small_ball_mass {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ρ d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => S.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      (S.μ ω (ball z d)).toReal < 1 / ((n : ℝ) + 1)}) atTop (𝓝 0) := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨T, hT⟩ := (ENNReal.tendsto_nhds_zero.1
    (hS.tendsto_measure_curve_escape (ρ + 1)) (e / 2) he2).exists
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1
    (hS.tendsto_measure_curve_modulus ((T : ℝ) + 1) (d / 2) (by linarith))
      (e / 2) he2).exists
  let E : Set Ω := {ω | ∃ t : ℝ, (T : ℝ) ≤ |t| ∧ ‖S.η ω t‖ < ρ + 1}
  let F : Set Ω := {ω | ∃ s ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
    ∃ t ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
    dist s t ≤ 1 / ((N : ℝ) + 1) ∧ d / 2 < dist (S.η ω s) (S.η ω t)}
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  have hbound : S.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      (S.μ ω (ball z d)).toReal < 1 / ((n : ℝ) + 1)} ≤ S.P (E ∪ F) := by
    apply measure_mono_ae
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hη hp
    intro hbad
    by_contra hgood
    have hE : ω ∉ E := fun h => hgood (Or.inl h)
    have hF : ω ∉ F := fun h => hgood (Or.inr h)
    have hescape : ∀ t : ℝ, (T : ℝ) ≤ |t| → ρ + 1 ≤ ‖S.η ω t‖ := by
      intro t ht
      exact le_of_not_gt (fun hh => hE ⟨t, ht, hh⟩)
    have hmod : ∀ s ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
        ∀ t ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
          dist s t ≤ 1 / ((N : ℝ) + 1) → dist (S.η ω s) (S.η ω t) ≤ d / 2 := by
      intro s hs t ht hst
      exact le_of_not_gt (fun hh => hF ⟨s, hs, t, ht, hst, hh⟩)
    obtain ⟨z, hz, hsmall⟩ := hbad
    have hδ : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have hδ1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      linarith
    have hmass := ball_mass_lower_of_curve_modulus hη hδ hδ1 hd hescape hmod hz
    have hfinite := ball_mass_lt_top_of_proper hη hp z d
    have hm : 1 / ((N : ℝ) + 1) ≤ (S.μ ω (ball z d)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).1 hmass
    linarith
  calc
    _ ≤ S.P (E ∪ F) := hbound
    _ ≤ S.P E + S.P F := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hT hN
    _ = e := ENNReal.add_halves e

/-- A positive power of the cell area is bounded by any positive multiple of
the fixed-radius ball mass, uniformly over a bounded region, with probability
tending to one. -/
theorem MatedCRTEnv.IsValid.probTendsToOne_ball_mass_rpow {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ρ d α q : ℝ) (hd : 0 < d) (hα : 0 < α) (hq : 0 < q) :
    ProbTendsToOne S.P fun ε => {ω | ∀ z ∈ ball (0 : ℂ) ρ,
      ε ^ α ≤ q * (S.μ ω (ball z d)).toReal} := by
  unfold ProbTendsToOne
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1
    (hS.tendsto_measure_small_ball_mass ρ d hd) e he).exists
  have hδ : 0 < q * (1 / ((N : ℝ) + 1)) := by positivity
  filter_upwards [(tendsto_rpow_nhdsGT_zero hα).eventually (Iio_mem_nhds hδ)] with ε hε
  calc
    _ ≤ S.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        (S.μ ω (ball z d)).toReal < 1 / ((N : ℝ) + 1)} := by
      apply measure_mono
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨z, hz, hbad⟩ := hω
      refine ⟨z, hz, ?_⟩
      nlinarith
    _ ≤ e := hN

end MatedCRT
