import MatedCRT.Proofs.Sec5.LLowerBound.MassProb

/-! Uniform smallness of cells on bounded regions in probability. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- An escape cutoff and a compact-interval modulus bound control every cell
which meets the given ball. -/
theorem cell_diam_le_of_escape_modulus {η : ℝ → ℂ} {ρ T δ d ε : ℝ}
    (_hε : 0 < ε) (hε1 : ε ≤ 1) (hεδ : ε ≤ δ)
    (hescape : ∀ t : ℝ, T ≤ |t| → ρ + 1 ≤ ‖η t‖)
    (hmod : ∀ s ∈ Icc (-(T + 1)) (T + 1), ∀ t ∈ Icc (-(T + 1)) (T + 1),
      dist s t ≤ δ → dist (η s) (η t) ≤ d)
    (hd : 0 ≤ d) {k : ℤ} (hk : k ∈ cellVertices ε η (ball 0 ρ)) :
    diam (cell ε η k) ≤ d := by
  obtain ⟨w, ⟨t, ht, rfl⟩, hw⟩ := hk
  have htρ : ‖η t‖ < ρ := by simpa [mem_ball, dist_zero_right] using hw
  have htT : |t| < T := by
    by_contra h
    have := hescape t (le_of_not_gt h)
    linarith
  have htime : ∀ s ∈ Icc (ε * (k - 1)) (ε * k), s ∈ Icc (-(T + 1)) (T + 1) := by
    intro s hs
    obtain ⟨htl, htr⟩ := ht
    obtain ⟨hsl, hsr⟩ := hs
    obtain ⟨htlo, hthi⟩ := abs_lt.1 htT
    constructor <;> nlinarith
  apply Metric.diam_le_of_forall_dist_le hd
  rintro _ ⟨s, hs, rfl⟩ _ ⟨u, hu, rfl⟩
  apply hmod s (htime s hs) u (htime u hu)
  rw [Real.dist_eq, abs_le]
  obtain ⟨hsl, hsr⟩ := hs
  obtain ⟨hul, hur⟩ := hu
  constructor <;> nlinarith

/-- The cells meeting a fixed bounded region have uniformly small diameter
with probability tending to one as their quantum area tends to zero. -/
theorem MatedCRTEnv.IsValid.probTendsToOne_small_cells {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ρ d : ℝ) (hd : 0 < d) :
    ProbTendsToOne S.P fun ε => {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      diam (cell ε (S.η ω) k) ≤ d} := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  unfold ProbTendsToOne
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨T, hT⟩ := (ENNReal.tendsto_nhds_zero.1
    (hS.tendsto_measure_curve_escape (ρ + 1)) (e / 2) he2).exists
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1
    (hS.tendsto_measure_curve_modulus ((T : ℝ) + 1) d hd) (e / 2) he2).exists
  let E : Set Ω := {ω | ∃ t : ℝ, (T : ℝ) ≤ |t| ∧ ‖S.η ω t‖ < ρ + 1}
  let F : Set Ω := {ω | ∃ s ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
    ∃ t ∈ Icc (-((T : ℝ) + 1)) ((T : ℝ) + 1),
    dist s t ≤ 1 / ((N : ℝ) + 1) ∧ d < dist (S.η ω s) (S.η ω t)}
  have hδ : 0 < 1 / ((N : ℝ) + 1) := by positivity
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hε1 hεδ
  have hbound : S.P {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      diam (cell ε (S.η ω) k) ≤ d}ᶜ ≤ S.P (E ∪ F) := by
    apply measure_mono_ae
    filter_upwards [] with ω
    intro hbad
    by_contra hgood
    have hE : ω ∉ E := fun h => hgood (Or.inl h)
    have hF : ω ∉ F := fun h => hgood (Or.inr h)
    apply hbad
    intro k hk
    apply cell_diam_le_of_escape_modulus (T := (T : ℝ)) hε hε1.le hεδ.le ?_ ?_ hd.le hk
    · intro t ht
      exact le_of_not_gt (fun hh => hE ⟨t, ht, hh⟩)
    · intro s hs t ht hst
      exact le_of_not_gt (fun hh => hF ⟨s, hs, t, ht, hst, hh⟩)
  calc
    _ ≤ S.P (E ∪ F) := hbound
    _ ≤ S.P E + S.P F := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hT hN
    _ = e := ENNReal.add_halves e

end MatedCRT
