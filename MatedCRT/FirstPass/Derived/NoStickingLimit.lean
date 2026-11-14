import MatedCRT.FirstPass.Derived.StickyWindowLimitAll
import MatedCRT.FirstPass.Derived.NoStickingAllRadii

/-!
# No sticking for a subsequential limit of the quenched walk laws

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Proposition 6.1, last claim: if `ν` is a subsequential limit in law of `(D n, P̃^{ε_n})`
then `ν`-almost surely, for every starting point `z`, the limit kernel `P_z` gives mass zero to the paths that
are constant on some interval of positive length.

The window estimate at radius `1/2` (`NoStickingEvent.limLimSmall_noSticking`) is carried to every radius
`R = 1, 2, ...` by `NoStickingAllRadii.limLimSmall_windowBad_allRadii` (the cone scaling of Section 6.4), then to
a statement about the limit kernel at each radius, for all window lengths and horizons, by
`StickyWindowLimitAll.ae_forall_apply_stickySet_eq_zero_of_tendsto_law`.  A path that is constant on `[s, t]`
with `s < t` lies, for `R > sup_{u ≤ t} |f u|`, in `stickySet (B(0, R)) (1 / (k + 1)) N` for `1 / (k + 1) ≤ t - s`
and `N ≥ s`, which gives the countable union.
-/

set_option autoImplicit false

namespace MatedCRT
namespace NoStickingLimit

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel MatedCRT.NoStickingAllRadii

/-- A path that is constant on a non-degenerate interval lies in `stickySet (B(0, R)) a T` for some natural
`R`, rational window length `a = 1 / (k + 1)` and natural horizon `T = N`. -/
theorem constantOnInterval_subset_iUnion :
    {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} ⊆
      ⋃ r : ℕ × ℕ × ℕ, stickySet (ball (0 : ℂ) ((r.1 : ℝ) + 1)) (((r.2.1 : ℝ≥0) + 1)⁻¹) (r.2.2 : ℝ≥0) := by
  rintro f ⟨s, t, hst, hconst⟩
  have hpos : 0 < t - s := tsub_pos_of_lt hst
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ((t - s : ℝ≥0) : ℝ) from hpos)
  obtain ⟨N, hN⟩ := exists_nat_ge s
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  obtain ⟨R, hR⟩ := exists_nat_gt M
  have hka : (((k : ℝ≥0) + 1)⁻¹ : ℝ≥0) ≤ t - s := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [← one_div]
    exact hk.le
  refine mem_iUnion.2 ⟨(R, k, N), ?_⟩
  refine ⟨s, hN, fun u hu => ?_, fun u h1 h2 => ?_⟩
  · have hut : u ≤ t := by
      refine hu.trans ?_
      calc s + ((k : ℝ≥0) + 1)⁻¹ ≤ s + (t - s) := add_le_add le_rfl hka
        _ = t := add_tsub_cancel_of_le hst.le
    rw [mem_ball_zero_iff]
    have := hM u ⟨zero_le, hut⟩
    calc ‖f u‖ ≤ M := this
      _ < R := hR
      _ ≤ (R : ℝ) + 1 := by linarith
  · refine hconst u h1 ?_
    calc u ≤ s + ((k : ℝ≥0) + 1)⁻¹ := h2
      _ ≤ s + (t - s) := add_le_add le_rfl hka
      _ = t := add_tsub_cancel_of_le hst.le

/-- **No sticking for a subsequential limit** (Berestycki-Gwynne, Proposition 6.1, last claim).  `hLL` is the
window estimate at radius `1/2` of `NoStickingEvent.limLimSmall_noSticking` and `hmε` the lower bound
`ε m_ε ≥ c₀ > 0` of the speed; `hEnvS` is the cone scaling of valid environments. -/
theorem ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν)))
    {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ}
    (hψ : (∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0))
    (hLL : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
        srwLaw (S.mult ε ω) x (windowBad ε (S.η ω) (1 / 2) δ q) ≤ ENNReal.ofReal (ψ δ)}))
    (hmε : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε) :
    ∀ᵐ p ∂ν, ∀ z : ℂ,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0 := by
  have hR : ∀ R : ℕ, ∀ᵐ p ∂ν, ∀ z : ℂ, ∀ a : ℝ≥0, 0 < a → ∀ T : ℝ≥0,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (stickySet (ball (0 : ℂ) ((R : ℝ) + 1)) a T) = 0 := fun R => by
    obtain ⟨ψ', hψ', hLL'⟩ := limLimSmall_windowBad_allRadii hEnvS hγ hγ2 hq hψ hLL
      (ρ := (R : ℝ) + 1) (by positivity)
    exact StickyWindowLimitAll.ae_forall_apply_stickySet_eq_zero_of_tendsto_law hS hη' hae hε0 hε hD hlaw
      (q := q / 2) (by positivity) hψ' (hLL' Ω S hS) hmε
  filter_upwards [ae_all_iff.2 hR] with p hp z
  refine measure_mono_null constantOnInterval_subset_iUnion (measure_iUnion_null fun r => ?_)
  exact hp r.1 z _ (by positivity) _

end NoStickingLimit
end MatedCRT
