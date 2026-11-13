import MatedCRT.FirstPass.Derived.GmcGreenApproxGFF

/-!
# Finiteness of the Green-weighted chaos measure away from the pole

For a disc `D = B_r(z)` and a pole `y ∈ D`, the Green-weighted cut-off GMC limit
`gmcGreenMeasure γ ρ ρ₂ z y r ψ = 2 · 1_D G_D(y, ·) · gmcLimit γ ρ ρ₂ ψ` is finite on every compact set `K` that avoids
`y`: the Green function `G_D(y, ·)` is continuous off the pole, hence bounded on `K`, and the vague limit
`gmcLimit γ ρ ρ₂ ψ` is finite on compact sets. For the whole-plane GFF field `h^ℂ - γ log |·|` this holds almost surely,
simultaneously for all discs, poles and compact sets.

This is the local-finiteness hypothesis needed to identify the limiting clock occupation measure with the
Green-weighted chaos measure on `D ∖ {0, y}` from countably many test-function identities.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- On a compact set `K` avoiding the pole `y ∈ B_r(z)`, the occupation density `1_D · 2 G_D(y, ·)` is bounded by a
finite constant. -/
lemma exists_bound_greenOccupationDensity {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) {K : Set ℂ}
    (hK : IsCompact K) (hyK : y ∉ K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x ∈ K, greenOccupationDensity z y r x ≤ C := by
  have hKy : K ⊆ ({y}ᶜ : Set ℂ) := fun x hx hxy => hyK (Set.mem_singleton_iff.1 hxy ▸ hx)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((MatedCRT.GreenEnvironment.continuousOn_greenFunction_ball_compl hy).mono hKy)
  refine ⟨2 * ENNReal.ofReal C, ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top, fun x hx => ?_⟩
  by_cases hxD : x ∈ ball z r
  · rw [greenOccupationDensity_of_mem hxD]
    have hCx := hC x hx
    rw [Real.norm_eq_abs] at hCx
    gcongr
    exact (le_abs_self _).trans hCx
  · rw [greenOccupationDensity_of_notMem hxD]
    exact zero_le

/-- A measure that is finite on a compact set `K` avoiding the pole `y ∈ B_r(z)` stays finite on `K` after weighting
by the occupation density `1_D · 2 G_D(y, ·)`. -/
theorem withDensity_greenOccupationDensity_lt_top {μ : Measure ℂ} {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    {K : Set ℂ} (hK : IsCompact K) (hyK : y ∉ K) (hμK : μ K < ∞) :
    μ.withDensity (greenOccupationDensity z y r) K < ∞ := by
  obtain ⟨C, hC, hCK⟩ := exists_bound_greenOccupationDensity hy hK hyK
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, greenOccupationDensity z y r x ∂μ ≤ ∫⁻ _ in K, C ∂μ :=
        setLIntegral_mono' hK.measurableSet hCK
    _ = C * μ K := setLIntegral_const K C
    _ < ∞ := ENNReal.mul_lt_top hC hμK

/-- **Finiteness of the Green-weighted chaos measure.** If `gmcLimit γ ρ ρ₂ ψ` is the vague limit on `ℂ` of the
cut-off approximations, then `gmcGreenMeasure γ ρ ρ₂ z y r ψ` is finite on every compact set avoiding the pole
`y ∈ B_r(z)`. -/
theorem gmcGreenMeasure_lt_top_of_isVagueLimitOn {γ ρ ρ₂ : ℝ} {ψ : UnitDiskCircleIndex → ℝ}
    (hlim : QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k ψ) (gmcLimit γ ρ ρ₂ ψ))
    {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) {K : Set ℂ} (hK : IsCompact K) (hyK : y ∉ K) :
    gmcGreenMeasure γ ρ ρ₂ z y r ψ K < ∞ :=
  withDensity_greenOccupationDensity_lt_top hy hK hyK (hlim.2.1 K hK (subset_univ K))

/-- **GFF instance.** For a whole-plane GFF `h^ℂ`, `0 < γ < 2` and `ρ < ρ₂ < 1`, almost surely the Green-weighted
cut-off GMC limit of the circle averages of `h^ℂ - γ log |·|` is, for every disc `B_r(z)` and pole `y ∈ B_r(z)`,
finite on every compact set avoiding `y`. -/
theorem ae_gmcGreenMeasure_lt_top_gff {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω' ∂P', ∀ (z y : ℂ) (r : ℝ), y ∈ ball z r → ∀ K : Set ℂ, IsCompact K → y ∉ K →
      gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') K < ∞ := by
  filter_upwards [ae_gmcApproxCut_finite_and_isVagueLimitOn_gff hG hγ hγ2 hρρ₂ hρ₂]
    with ω' hω z y r hy K hK hyK
  exact gmcGreenMeasure_lt_top_of_isVagueLimitOn hω.2 hy hK hyK

end MatedCRT.KilledOccupation
