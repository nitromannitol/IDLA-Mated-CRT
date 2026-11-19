import MatedCRT.FirstPass.Derived.ExitTailInterpWalkLaw
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.MarkovTimeChange
import LatticeProb.Prob.StickyPathLimit

/-!
# A subsequential limit of the interpolated walk laws never stays in a ball forever

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4 and Lemma 7.4: the passage to the limit in the exit-time tail estimate.

Let the laws of the interpolated quenched walk laws `P̃^{ε_n}(ω)` (`ω ~ S.P`) converge weakly, as random elements
of the space of continuous families `ℂ → 𝒫(C(ℝ≥0, ℂ))`, to a probability measure `ν₂`.  By
`ExitTailInterpWalkLaw.exitTail_interpWalkLaw`, for every `r, θ > 0` there is `N` such that, outside an event of
probability at most `2 θ`, every `P̃^ε(ω)(z)` gives mass at most `θ` to the open set `stayOpen r N`.  Since
`P ↦ sup_z P(z)(stayOpen r N)` is lower semicontinuous, the portmanteau theorem gives the same for `ν₂`, and
`ν₂`-almost surely `P(z)` gives no mass to the paths that stay in `B_r` for all times.

* `ae_apply_stayForever_eq_zero_of_tendsto_law`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel MatedCRT.ExitTailInterpWalkLaw

namespace MatedCRT
namespace ExitTailLimit

/-- The continuous paths that stay in the open ball `B(0, r)` for all times. -/
def stayForever (r : ℝ) : Set (ContinuousPath ℂ) := {f | ∀ t : ℝ≥0, f t ∈ ball (0 : ℂ) r}

theorem stayForever_subset_stayOpen (r : ℝ) (T : ℝ≥0) : stayForever r ⊆ stayOpen r T :=
  fun _ hf t _ => hf t

/-- **A subsequential limit of the interpolated walk laws does not stay in a ball forever** (Berestycki-Gwynne,
Lemma 7.4, finite exit).  `hc0` is the lower bound `ε m_ε ≥ c₀ > 0` of the speed. -/
theorem ae_apply_stayForever_eq_zero_of_tendsto_law {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hc0 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) {ν₂ : Measure PathLawFamily}
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂)))
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ P ∂ν₂, ∀ z : ℂ,
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) (stayForever r) = 0 := by
  have hPS : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hW : ∀ n, AEMeasurable (interpWalkLaw S η' (ε n)) S.P := fun n =>
    aemeasurable_interpWalkLaw hS hη' hae (hε0 n)
  have hνprob : IsProbabilityMeasure ν₂ := by
    have h1 := hlaw (BoundedContinuousFunction.const _ 1)
    have h3 : ∀ n, ∫ ω, (BoundedContinuousFunction.const PathLawFamily (1 : ℝ))
        (interpWalkLaw S η' (ε n) ω) ∂S.P = 1 := fun n => by simp
    have h4 : Tendsto (fun n => ∫ ω, (BoundedContinuousFunction.const PathLawFamily (1 : ℝ))
        (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 1) := by
      simp_rw [h3]
      exact tendsto_const_nhds
    have h5 := tendsto_nhds_unique h1 h4
    simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one] at h5
    exact isProbabilityMeasure_iff_real.2 h5
  let μs : ℕ → ProbabilityMeasure PathLawFamily := fun n =>
    ⟨S.P.map (interpWalkLaw S η' (ε n)), inferInstance⟩
  let μ : ProbabilityMeasure PathLawFamily := ⟨ν₂, hνprob⟩
  have hlim : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    exact (hlaw F).congr fun n => (integral_map (hW n) F.continuous.aestronglyMeasurable).symm
  have hsmall : ∀ r' c : ℝ≥0, 0 < r' → 0 < c → ∃ N : ℕ, ∀ᶠ n in atTop,
      ((μs n : ProbabilityMeasure PathLawFamily) : Measure PathLawFamily)
      {p | (r' : ℝ≥0∞) < ⨆ z : (Set.univ : Set ℂ), ((p z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)) (stayOpen r N)} ≤ c := by
    intro r' c hr' hc
    have hr'0 : (0 : ℝ) < r' := by exact_mod_cast hr'
    have hc0' : (0 : ℝ) < c := by exact_mod_cast hc
    set θ : ℝ := min (r' : ℝ) ((c : ℝ) / 2) with hθdef
    have hθ : 0 < θ := lt_min hr'0 (by positivity)
    have hθr : θ ≤ r' := min_le_left _ _
    have hθc : 2 * θ ≤ c := by have := min_le_right (r' : ℝ) ((c : ℝ) / 2); linarith
    obtain ⟨N, ε₂, hε₂, hbound⟩ := exitTail_interpWalkLaw hEnvS h214 h217 hγ hγ2 hθ hr S hS η' hae hc0
    refine ⟨N, ?_⟩
    filter_upwards [hε.eventually (gt_mem_nhds hε₂)] with n hn
    have hlsc := lowerSemicontinuous_iSup_apply (P := fun p : PathLawFamily => p) continuous_id
      (Set.univ : Set ℂ) (isOpen_stayOpen r N)
    have hmeasSet : MeasurableSet {p : PathLawFamily |
        (r' : ℝ≥0∞) < ⨆ z : (Set.univ : Set ℂ), ((p z : ProbabilityMeasure (ContinuousPath ℂ)) :
          Measure (ContinuousPath ℂ)) (stayOpen r N)} :=
      (lowerSemicontinuous_iff_isOpen_preimage.1 hlsc (r' : ℝ≥0∞)).measurableSet
    change S.P.map (interpWalkLaw S η' (ε n)) _ ≤ _
    rw [Measure.map_apply_of_aemeasurable (hW n) hmeasSet]
    refine le_trans (measure_mono ?_) (le_trans (hbound (ε n) (hε0 n) hn) ?_)
    · intro ω hω
      have hω' : (r' : ℝ≥0∞) < ⨆ z : (Set.univ : Set ℂ),
          ((interpWalkLaw S η' (ε n) ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
            Measure (ContinuousPath ℂ)) (stayOpen r N) := hω
      obtain ⟨z, hz⟩ := lt_iSup_iff.1 hω'
      refine ⟨z.1, lt_of_le_of_lt ?_ hz⟩
      calc ENNReal.ofReal θ ≤ ENNReal.ofReal r' := ENNReal.ofReal_le_ofReal hθr
        _ = r' := ENNReal.ofReal_coe_nnreal
    · calc ENNReal.ofReal (2 * θ) ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hθc
        _ = c := ENNReal.ofReal_coe_nnreal
  have hmain := ae_forall_apply_eq_zero_of_tendsto (K := Set.univ) (P := fun p : PathLawFamily => p)
    hlim continuous_id (fun N => isOpen_stayOpen r N) (F := stayForever r)
    (fun N => stayForever_subset_stayOpen r N) hsmall
  filter_upwards [hmain] with p hp z
  exact hp z (Set.mem_univ z)

end ExitTailLimit
end MatedCRT
