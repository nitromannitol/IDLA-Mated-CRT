import MatedCRT.FirstPass.Derived.ExitTimeMedianStrictAssembly
import MatedCRT.FirstPass.Derived.ExitTimeSplitVersion

/-!
# The annealed exit-time law of Liouville Brownian motion from `B_{1/2}`: positivity and strict median bound

Let `S` be a valid environment with `0 < γ < 2` and let `τ = τ^{LBM}_{B_{1/2}}` be the exit time of Liouville
Brownian motion started at `0` from the disc of radius `1/2`. The annealed distribution function is
`G s = ∫ P^0[τ ≤ s] dP`, and `m₀ = S.m₀` is its lower median (eq:mo).

* (hpos) `MatedCRTEnv.IsValid.lintegral_exitTime_mem_Ioc_pos`: the annealed law of `τ` charges every interval
  `(a, c]` with `0 < a < c`; `MatedCRTEnv.IsValid.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime` is the same
  statement for every jointly measurable version of `τ` under `S.P ⊗ P^0`.
* (hstrict) `MatedCRTEnv.IsValid.half_lt_lintegral_exitTime_le_of_m₀_lt`: `G s > 1/2` for every `s > m₀`;
  `MatedCRTEnv.IsValid.half_lt_measure_prod_le_of_medianOf_lt` is the same statement for every jointly measurable
  version of `τ`.

The proofs combine the factorisation `τ = e^{γ B_{t₀}} Ψ(X, (B_{t₀ + u} - B_{t₀})_u, b)`, `t₀ = log (5/3)`, of
`MatedCRTEnv.IsValid.exists_matingOfTrees_exitTime_version_eq_exp_mul` (the radial value `B_{t₀}` of the
circle-average process is Gaussian and independent of the lateral field, of the later radial increments and of the
Brownian path) with the conditional statements of `ExitTimeMedianStrictAssembly`.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- **(hpos) The annealed exit-time law of Liouville Brownian motion from `B_{1/2}` charges every interval.** For a
valid environment and `0 < γ < 2`, `∫ P^0[τ^{LBM}_{B_{1/2}} ∈ (a, c]] dP > 0` for all `0 < a < c`. -/
theorem MatedCRTEnv.IsValid.lintegral_exitTime_mem_Ioc_pos {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)}
      ∂S.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcpl, _, _, hTm, hT, hΨ, hsplit⟩ :=
    hS.exists_matingOfTrees_exitTime_version_eq_exp_mul hγ hγ2
  exact hS.lintegral_exitTime_mem_Ioc_pos_of_split hγ hcpl hTm hT hΨ hsplit ha hac

/-- **(hpos) Every jointly measurable version of the exit time charges every interval.** For a valid environment and
`0 < γ < 2`, every measurable `V` on `Ω × ContinuousPath ℂ` with `V(ω, ·) = τ^{LBM}_{B_{1/2}}` `P^0`-a.s. for
`S.P`-a.e. `ω` satisfies `(S.P ⊗ P^0) {V ∈ (a, c]} > 0` for all `0 < a < c`. -/
theorem MatedCRTEnv.IsValid.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {V : Ω × ContinuousPath ℂ → ℝ≥0∞} (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      V (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < (S.P.prod (planarBrownianMotion 0))
      {p | V p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)} := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcpl, _, _, hTm, hT, hΨ, hsplit⟩ :=
    hS.exists_matingOfTrees_exitTime_version_eq_exp_mul hγ hγ2
  exact hS.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime_of_split hγ hcpl hTm hT hΨ hsplit hVm hV ha hac

/-- **(hstrict) Strict median bound for every jointly measurable version of the exit time.** For a valid
environment and `0 < γ < 2`, every measurable `V` on `Ω × ContinuousPath ℂ` with `V(ω, ·) = τ^{LBM}_{B_{1/2}}`
`P^0`-a.s. for `S.P`-a.e. `ω` has a distribution function under `S.P ⊗ P^0` strictly above `1/2` to the right of its
lower median. -/
theorem MatedCRTEnv.IsValid.half_lt_measure_prod_le_of_medianOf_lt {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {V : Ω × ContinuousPath ℂ → ℝ≥0∞} (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      V (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) {s : ℝ}
    (hs : medianOf (fun r => (S.P.prod (planarBrownianMotion 0)) {p | V p ≤ ENNReal.ofReal r}) < s) :
    (1 / 2 : ℝ≥0∞) < (S.P.prod (planarBrownianMotion 0)) {p | V p ≤ ENNReal.ofReal s} := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcpl, _, _, hTm, hT, hΨ, hsplit⟩ :=
    hS.exists_matingOfTrees_exitTime_version_eq_exp_mul hγ hγ2
  exact hS.half_lt_measure_prod_le_of_medianOf_lt_of_split hγ hcpl hTm hT hΨ hsplit hVm hV hs

/-- **(hstrict) Strict median bound for the annealed exit-time law of Liouville Brownian motion from `B_{1/2}`.** For
a valid environment and `0 < γ < 2`, the annealed distribution function `G s = ∫ P^0[τ^{LBM}_{B_{1/2}} ≤ s] dP`
exceeds `1/2` for every `s` strictly larger than its lower median `m₀ = S.m₀` (eq:mo). -/
theorem MatedCRTEnv.IsValid.half_lt_lintegral_exitTime_le_of_m₀_lt {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (s : ℝ) (hs : S.m₀ < s) :
    (1 / 2 : ℝ≥0∞) < ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s} ∂S.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcpl, _, _, hTm, hT, hΨ, hsplit⟩ :=
    hS.exists_matingOfTrees_exitTime_version_eq_exp_mul hγ hγ2
  exact hS.half_lt_lintegral_exitTime_le_of_m₀_lt_of_split hγ hcpl hTm hT hΨ hsplit s hs

end MatedCRT
