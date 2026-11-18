import MatedCRT.FirstPass.Derived.BrownianBlockExitFrozenHit
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# The interpolated walk leaves every bounded set

Let `m` be a locally finite multigraph on `ℤ` whose consecutive vertices are adjacent, `ε > 0`, and
`η` a continuous curve with `η(t) → ∞` as `|t| → ∞`. Only finitely many vertices have their
position `η(ε k)` in a closed disc, and simple random walk on `m` leaves every finite set of
vertices almost surely. Hence the linear interpolation, at any speed `c > 0`, of the embedded walk
almost surely has unbounded range. Along such a path every block exit is a genuine exit
(`BrownianBlockExitFrozenHit`), so off the frozen set consecutive block-exit positions of the
walk are more than `s / 2` apart, and the event that the first `N` block-exit positions avoid the
frozen set while staying in `K` lies, up to a null set, in the separated histories.

## Main results

* `interpPathCM_natCast_div`: at time `k / c` the interpolated walk is at the `k`-th embedded vertex.
* `ae_not_isBounded_range_interpPathCM`: almost surely the interpolated walk has unbounded range.
* `ae_half_lt_norm_blockExit_step_interpPathCM`: almost surely, whenever the `n`-th block-exit
  position of the interpolated walk lies off `F`, the next one is more than `s / 2` away.
* `srwLaw_blockExit_avoid_le_separatedHistories`: the walk probability that the first `N`
  block-exit positions avoid `F` and lie in `K` is at most the probability that the block-exit
  history is `s / 2`-separated with its first `N` entries in `K`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess Filter
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- At time `k / c` the interpolation at speed `c > 0` of a vertex sequence sits at the `k`-th
vertex. -/
theorem interpPathCM_natCast_div {v : ℤ → ℂ} {c : ℝ} (hc : 0 < c) (x : ℕ → ℤ) (k : ℕ) :
    interpPathCM v hc.le x ((k : ℝ≥0) / c.toNNReal) = v (x k) := by
  have hmt : c * (((k : ℝ≥0) / c.toNNReal : ℝ≥0) : ℝ) = k := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ hc.le, NNReal.coe_natCast, mul_div_cancel₀ _ hc.ne']
  rw [interpPathCM_apply, interpPathFn, hmt]
  simp [linInterp]

/-- For a continuous proper curve and `ε > 0`, finitely many vertices have their position in a
closed disc. -/
theorem vertexPoint_preimage_closedBall_finite {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (R : ℝ) :
    (vertexPoint ε η ⁻¹' closedBall (0 : ℂ) R).Finite :=
  (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (0 : ℂ) R)).subset fun k hk =>
    ⟨vertexPoint ε η k, ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩, hk⟩

/-- **The interpolated walk has unbounded range.** For a locally finite multigraph whose
consecutive vertices are adjacent, `ε > 0`, a continuous proper curve `η` and a speed `c > 0`,
almost surely the linear interpolation of the embedded simple random walk has unbounded range. -/
theorem ae_not_isBounded_range_interpPathCM {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a,
      ¬ Bornology.IsBounded (range (interpPathCM (vertexPoint ε η) hc.le x)) := by
  have hnull : ∀ R : ℕ, ∀ᵐ x ∂srwLaw m a,
      ∃ n, x n ∉ vertexPoint ε η ⁻¹' closedBall (0 : ℂ) R := by
    intro R
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_)
      (ExitNull68.exit_null_of_finite hlf hcons
        (vertexPoint_preimage_closedBall_finite hε hη hp R) a)
    have hx' : ¬ ∃ n, x n ∉ vertexPoint ε η ⁻¹' closedBall (0 : ℂ) R := hx
    show vExitTime _ x = ⊤
    unfold vExitTime
    simp only [hx', ↓reduceDIte]
  filter_upwards [ae_all_iff.2 hnull] with x hx hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨n, hn⟩ := hx N
  apply hn
  have hmem := hR (mem_range_self ((n : ℝ≥0) / c.toNNReal))
  rw [interpPathCM_natCast_div hc] at hmem
  exact closedBall_subset_closedBall hN hmem

/-- **Walk block exits are genuine steps.** Almost surely, along the interpolated walk, whenever
the `n`-th block-exit position lies off the frozen set `F`, the next block-exit position is more
than `s / 2` away from it. -/
theorem ae_half_lt_norm_blockExit_step_interpPathCM {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 < s) (F : Set ℂ) :
    ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ,
      interpPathCM (vertexPoint ε η) hc.le x
          (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F →
        s / 2 < ‖interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)) -
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x))‖ := by
  filter_upwards [ae_not_isBounded_range_interpPathCM hlf hcons hε hη hp hc a] with x hx n hn
  exact half_lt_norm_blockExit_step hs hx n hn

/-- **The walk's block-exit chain avoiding the frozen set is separated.** The probability that the
first `N` block-exit positions of the interpolated walk avoid `F` and lie in `K` is at most the
probability that its block-exit history of length `N + 1` is `s / 2`-separated with its first `N`
entries in `K`. -/
theorem srwLaw_blockExit_avoid_le_separatedHistories {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 < s) (F K : Set ℂ) (N : ℕ) :
    srwLaw m a {x | ∀ n < N,
        interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F ∧
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∈ K} ≤
      srwLaw m a ((fun x => blockExitPositions s F N (interpPathCM (vertexPoint ε η) hc.le x)) ⁻¹'
        separatedHistories N (s / 2) K) := by
  refine measure_mono_ae ?_
  filter_upwards [ae_half_lt_norm_blockExit_step_interpPathCM hlf hcons hε hη hp hc a hs F]
    with x hx hmem
  intro n
  beta_reduce
  rw [blockExitPositions_apply, blockExitPositions_apply]
  exact ⟨(hx n (hmem n n.isLt).1).le, (hmem n n.isLt).2⟩

end BlockExit

end MatedCRT
