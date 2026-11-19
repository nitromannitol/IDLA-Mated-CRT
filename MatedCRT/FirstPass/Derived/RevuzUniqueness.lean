import MatedCRT.FirstPass.Derived.RevuzUniquenessTaylor

/-!
# Uniqueness of a positive continuous additive functional with a given Revuz measure

Two positive continuous additive functionals `A`, `A'` of planar Brownian motion with the same `σ`-finite Revuz
measure `μ` are indistinguishable under `P_z` for Lebesgue-almost every starting point `z`
(`revuzUniquenessInput_derived : RevuzUniquenessInput`; Fukushima–Oshima–Takeda (2011), Theorem 5.1.4,
uniqueness part).

Assembly: choose localizers `0 ≤ h_j ≤ 1` of `μ`, of finite `μ`-integral and increasing to `1`
(`exists_localizer_of_sigmaFinite`). For Lebesgue-almost every `z` all expected window integrals
`E_z[A^{h_j}_r]`, `E_z[A'^{h_j}_r]` are finite (`ae_lintegral_clockWindowIntegral_lt_top`), so by
`ae_clockWindowIntegral_eq_of_revuz_eq`, `P_z`-almost surely `A^{h_j}_q = A'^{h_j}_q` for all `j` and all rational
`q`. Monotone convergence in `j` gives `Ā_q - Ā_0 = Ā'_q - Ā'_0`, and along almost every path both clocks start
at `0`, are continuous and nondecreasing, so they agree with their regularizations, at every rational time, and
by continuity at every time.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- Monotone convergence for window integrals: the window integral of an increasing supremum of Borel integrands is
the supremum of the window integrals. -/
theorem clockWindowIntegral_iSup (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) {g : ℕ → ℂ → ℝ≥0∞}
    (hg : ∀ j, Measurable (g j)) (hmono : ∀ y, Monotone fun j => g j y) (r : ℝ) (ω : ContinuousPath ℂ) :
    clockWindowIntegral A (fun y => ⨆ j, g j y) r ω = ⨆ j, clockWindowIntegral A (g j) r ω := by
  unfold clockWindowIntegral
  exact lintegral_iSup (fun j => (hg j).comp (ω.continuous.comp continuous_real_toNNReal).measurable)
    (fun _ _ hij s => hmono _ hij)

/-- Along a path on which the clock starts at `0` and is continuous and nondecreasing, the window integral of the
constant `1` over `(0, t]` is the clock at time `t`. -/
theorem clockWindowIntegral_one_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0)
    (hc : Continuous fun t => A t ω) (hm : Monotone fun t => A t ω) (t : ℝ≥0) :
    clockWindowIntegral A 1 (t : ℝ) ω = (A t ω : ℝ≥0∞) := by
  have hreg : (fun u => regularize A u ω) = fun u => A u ω :=
    funext (regularize_eq_of_continuous_monotone hc hm)
  unfold clockWindowIntegral
  rw [hreg]
  simp only [Pi.one_apply]
  rw [lintegral_one, Measure.restrict_apply_univ, stieltjesOfNNReal_measure_Ioc hm hc]
  simp [h0]

/-- **Uniqueness of a PCAF with a given σ-finite Revuz measure** (Fukushima–Oshima–Takeda (2011), Theorem 5.1.4,
uniqueness part): `RevuzUniquenessInput` holds. -/
theorem revuzUniquenessInput_derived : RevuzUniquenessInput := by
  intro A A' hA hA' hσ hμ
  obtain ⟨h, hhm, hle, hfin, hmono, hev⟩ := exists_localizer_of_sigmaFinite (revuz planarLaw A)
  have hfinA : ∀ j, ∫⁻ y, h j y ∂revuz planarLaw A ≠ ∞ := fun j => (hfin j).ne
  have hfinA' : ∀ j, ∫⁻ y, h j y ∂revuz planarLaw A' ≠ ∞ := fun j => by rw [← hμ]; exact hfinA j
  have hsup1 : (fun y => ⨆ j, h j y) = 1 := funext fun y => le_antisymm (iSup_le fun j => hle j y) (by
    obtain ⟨j, hj⟩ := (hev y).exists
    exact hj.symm.le.trans (le_iSup (fun j => h j y) j))
  have hz : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j : ℕ, ∀ r : ℝ,
      ∫⁻ ω, clockWindowIntegral A (h j) r ω ∂planarLaw z < ∞ ∧
        ∫⁻ ω, clockWindowIntegral A' (h j) r ω ∂planarLaw z < ∞ := by
    rw [ae_all_iff]
    intro j
    filter_upwards [ae_lintegral_clockWindowIntegral_lt_top hA (hhm j) (hfinA j),
      ae_lintegral_clockWindowIntegral_lt_top hA' (hhm j) (hfinA' j)] with z h1 h2 r
    exact ⟨h1 r, h2 r⟩
  filter_upwards [hz] with z hz
  have hω : ∀ᵐ ω ∂planarLaw z, ∀ j : ℕ, ∀ q : ℚ≥0,
      clockWindowIntegral A (h j) ((q : ℝ≥0) : ℝ) ω = clockWindowIntegral A' (h j) ((q : ℝ≥0) : ℝ) ω := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro q
    exact ae_clockWindowIntegral_eq_of_revuz_eq hA hA' hμ (hhm j) (hfinA j) q
      (hz j ((q : ℝ≥0) : ℝ)).1.ne (hz j ((q : ℝ≥0) : ℝ)).2.ne
  filter_upwards [hω, hA.path z, hA'.path z] with ω hω h1 h2
  have hq : ∀ q : ℚ≥0, A q ω = A' q ω := fun q => by
    have hsup : clockWindowIntegral A 1 ((q : ℝ≥0) : ℝ) ω = clockWindowIntegral A' 1 ((q : ℝ≥0) : ℝ) ω := by
      rw [← hsup1, clockWindowIntegral_iSup A hhm hmono, clockWindowIntegral_iSup A' hhm hmono]
      exact iSup_congr fun j => hω j q
    rw [clockWindowIntegral_one_eq h1.1 h1.2.1 h1.2.2, clockWindowIntegral_one_eq h2.1 h2.2.1 h2.2.2] at hsup
    exact ENNReal.coe_inj.1 hsup
  have hAA' := eq_of_continuous_of_eq_nnrat h1.2.1 h2.2.1 hq
  exact fun t => congrFun hAA' t

end MatedCRT
