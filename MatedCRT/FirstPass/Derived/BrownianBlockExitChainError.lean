import MatedCRT.FirstPass.Derived.BrownianBlockExitChain

/-!
# Closed form of the accumulated error in the block-exit chain comparison

The chain comparison `prokhorovLE_chainSeqLaw_gridRectBlockExit` bounds the one-sided Prokhorov
distance between the walk history law and the frozen Brownian block-exit history law after `N`
fresh exits, at radius `(N + 1) ε`, by the accumulated error
`∑_{m < N} (ε + 24 (m + 1) ε / s + m · 144 (m + 1) ε / s)`: per exit, the kernel error `ε`, the
continuity error `η_m = 24 R_m / s` and the frozen mass `ρ_m = m · 144 R_m / s` near the lattice,
with step radii `R_m = (m + 1) ε`.

## Main results

* `sum_blockExitChainError_eq`: the accumulated error equals
  `N ε + 12 N (N + 1) ε / s + 48 (N - 1) N (N + 1) ε / s`.
* `sum_blockExitChainError_le`: for `ε ≥ 0` and `s > 0` it is at most `N ε + 60 N³ ε / s`.
* `tendsto_sum_blockExitChainError`: for a fixed number `N` of exits and a fixed block scale `s`,
  the accumulated error tends to `0` as `ε → 0`.
* `prokhorovLE_chainSeqLaw_gridRectBlockExit_cubic`: the chain comparison with the error
  `N ε + 60 N³ ε / s`.
* `prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable_cubic`: the same for the kernel frozen
  on a measurable grid-line stable set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- **Closed form of the accumulated error.** After `N` exits,
`∑_{m < N} (ε + 24 (m + 1) ε / s + m · 144 (m + 1) ε / s)
  = N ε + 12 N (N + 1) ε / s + 48 (N - 1) N (N + 1) ε / s`. -/
theorem sum_blockExitChainError_eq (N : ℕ) (ε s : ℝ) :
    ∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        m * (144 * (((m : ℝ) + 1) * ε) / s)) =
      N * ε + 12 * ((N : ℝ) * (N + 1)) * ε / s + 48 * (((N : ℝ) - 1) * N * (N + 1)) * ε / s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Cubic bound on the accumulated error.** For `ε ≥ 0` and `s > 0`, the accumulated error after
`N` exits is at most `N ε + 60 N³ ε / s`. -/
theorem sum_blockExitChainError_le (N : ℕ) {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) :
    ∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        m * (144 * (((m : ℝ) + 1) * ε) / s)) ≤
      N * ε + 60 * (N : ℝ) ^ 3 * ε / s := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact pow_le_pow_right₀ (by exact_mod_cast h) (by norm_num)
  have hpoly : 12 * ((N : ℝ) * (N + 1)) + 48 * (((N : ℝ) - 1) * N * (N + 1)) =
      48 * (N : ℝ) ^ 3 + 12 * (N : ℝ) ^ 2 - 36 * N := by ring
  have key : 12 * ((N : ℝ) * (N + 1)) + 48 * (((N : ℝ) - 1) * N * (N + 1)) ≤
      60 * (N : ℝ) ^ 3 := by
    rw [hpoly]
    linarith
  rw [sum_blockExitChainError_eq]
  have hsplit : (N : ℝ) * ε + 12 * ((N : ℝ) * (N + 1)) * ε / s +
      48 * (((N : ℝ) - 1) * N * (N + 1)) * ε / s =
      N * ε + (12 * ((N : ℝ) * (N + 1)) + 48 * (((N : ℝ) - 1) * N * (N + 1))) * ε / s := by
    ring
  rw [hsplit]
  have hdiv : (12 * ((N : ℝ) * (N + 1)) + 48 * (((N : ℝ) - 1) * N * (N + 1))) * ε / s ≤
      60 * (N : ℝ) ^ 3 * ε / s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right key hε) hs.le
  linarith

/-- **The accumulated error vanishes with the kernel error.** For a fixed number `N` of exits and
a fixed block scale `s`, the accumulated error tends to `0` as `ε → 0`. -/
theorem tendsto_sum_blockExitChainError (N : ℕ) (s : ℝ) :
    Tendsto (fun ε : ℝ => ∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        m * (144 * (((m : ℝ) + 1) * ε) / s))) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => ∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
      m * (144 * (((m : ℝ) + 1) * ε) / s))) := by
    fun_prop
  simpa using hc.tendsto 0

/-- **The chain comparison with a cubic error.** Under the hypotheses of
`prokhorovLE_chainSeqLaw_gridRectBlockExit`, the walk history law after `N` exits is within
radius `(N + 1) ε` and error `N ε + 60 N³ ε / s`, in the one-sided Prokhorov sense, of the frozen
Brownian block-exit history law. -/
theorem prokhorovLE_chainSeqLaw_gridRectBlockExit_cubic {s : ℝ} (hs : 0 < s) (a₁ a₂ c₁ c₂ : ℤ)
    {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : z ∈ gridRectOpen s a₁ a₂ c₁ c₂) {ε : ℝ} (hε : 0 < ε)
    (hεs : ((N : ℝ) + 1) * ε ≤ s / 4)
    {p : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ} (hp : ∀ n, Measurable (p n))
    [∀ n g, IsProbabilityMeasure (p n g)]
    (hpΓ : ∀ n < N, ∀ g, (g (Fin.last N) = z ∨ g (Fin.last N) ∈ gridLines s) →
      p n g (gridLines s)ᶜ = 0)
    (hK : ∀ n < N, ∀ g, ProkhorovLE (p n g)
      (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) ε ε) :
    ProkhorovLE (chainSeqLaw (fun m => paddedHistoryKernel m (p m)) (Measure.dirac fun _ => z) N)
      (chainSeqLaw (fun m => paddedHistoryKernel m
          (fun g => gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))))
        (Measure.dirac fun _ => z) N)
      (((N : ℝ) + 1) * ε) (N * ε + 60 * (N : ℝ) ^ 3 * ε / s) := by
  have hP := prokhorovLE_chainSeqLaw_gridRectBlockExit hs a₁ a₂ c₁ c₂ hN hz hε hεs hp hpΓ hK
  have hb := sum_blockExitChainError_le N hε.le hs
  intro A hA
  exact (hP A hA).trans (add_le_add_right (ENNReal.ofReal_le_ofReal hb) _)

/-- **The chain comparison with a cubic error, frozen off a grid-line stable set.** Under the
hypotheses of `prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable`, the walk history law
after `N` exits is within radius `(N + 1) ε` and error `N ε + 60 N³ ε / s`, in the one-sided
Prokhorov sense, of the frozen Brownian block-exit history law. -/
theorem prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable_cubic {s : ℝ} (hs : 0 < s)
    {F : Set ℂ} (hF : MeasurableSet F) (hFs : GridLineStable s F)
    {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : z ∉ F) {ε : ℝ} (hε : 0 < ε)
    (hεs : ((N : ℝ) + 1) * ε ≤ s / 4)
    {p : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ} (hp : ∀ n, Measurable (p n))
    [∀ n g, IsProbabilityMeasure (p n g)]
    (hpΓ : ∀ n < N, ∀ g, (g (Fin.last N) = z ∨ g (Fin.last N) ∈ gridLines s) →
      p n g (gridLines s)ᶜ = 0)
    (hK : ∀ n < N, ∀ g, ProkhorovLE (p n g)
      (frozenBlockExitKernel s hF (g (Fin.last N))) ε ε) :
    ProkhorovLE (chainSeqLaw (fun m => paddedHistoryKernel m (p m)) (Measure.dirac fun _ => z) N)
      (chainSeqLaw (fun m => paddedHistoryKernel m
          (fun g => frozenBlockExitKernel s hF (g (Fin.last N))))
        (Measure.dirac fun _ => z) N)
      (((N : ℝ) + 1) * ε) (N * ε + 60 * (N : ℝ) ^ 3 * ε / s) := by
  have hP :=
    prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable hs hF hFs hN hz hε hεs hp hpΓ hK
  have hb := sum_blockExitChainError_le N hε.le hs
  intro A hA
  exact (hP A hA).trans (add_le_add_right (ENNReal.ofReal_le_ofReal hb) _)

end BlockExit

end MatedCRT
