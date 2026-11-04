import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-!
# Removing the singularity in Lemma 3.7

The following deterministic squeeze is the final identification once the
truncated Green integrals converge and the small-ball contribution vanishes.
-/

namespace MatedCRT

open Filter Topology

/-- A limit identified away from a singularity is the full limit when the
discarded contribution has a bound tending to zero. -/
theorem eq_of_truncated_approximation {q I : ℝ} {a b : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 I)) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n, |q - a n| ≤ b n) : q = I := by
  have hlo : I ≤ q := by
    have hlim : Tendsto (fun n => a n - b n) atTop (𝓝 I) := by
      simpa using ha.sub hb
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => by
      have h := (abs_le.mp (hbound n)).1
      linarith
  have hhi : q ≤ I := by
    have hlim : Tendsto (fun n => a n + b n) atTop (𝓝 I) := by
      simpa using ha.add hb
    apply ge_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => by
      have h := (abs_le.mp (hbound n)).2
      linarith
  exact le_antisymm hhi hlo

end MatedCRT
