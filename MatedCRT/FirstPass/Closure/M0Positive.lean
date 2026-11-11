import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit

/-!
# Positivity of the annealed exit-time median `m₀`

`MatedCRTEnv.m₀` is the lower median of the annealed exit time of Liouville Brownian motion
started at `0` from the ball `B_{1/2}` (Bou-Rabee and Gwynne, arXiv:2211.04891, eq:mo; the
appendix occupation estimate, thm:occ-main, asserts `0 < m₀ < ∞`).

The positivity is proved in `MatedCRTEnv.IsValid.m₀_pos` (`HarmonicPathExit.lean`) from the
validity of the environment alone. The annealed exit distribution function at a level `δ` is
bounded by the annealed law of the LQG clock at a fixed time plus the probability that planar
Brownian motion leaves `B_{1/2}` before that time (`MatedCRTEnv.IsValid.annealedExitCDF_le_clock_add_brownian`,
`Proofs/Sec4/ConvergenceDivisible/ExitCDF.lean`). Its small-level and large-level bounds
(`exists_small_annealedExitCDF`, `exists_large_annealedExitCDF`) give the positivity of the
scaling constant `c₀ = 2 / m₀` (`matedCRTScalingConstantPositive`), hence `0 < m₀`.
This file restates the positivity at the level of `MatedCRTEnv`.
-/

namespace MatedCRT

/-- The median `m₀` of the annealed exit time of Liouville Brownian motion from `B_{1/2}` is
strictly positive for every valid mated-CRT environment with `0 < γ < 2`. -/
theorem MatedCRTEnv.m₀_pos {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    0 < S.m₀ :=
  hS.m₀_pos hγ hγ2

end MatedCRT
