import MatedCRT.FirstPass.Derived.BlockExitWalkJointLaw
import MatedCRT.FirstPass.Derived.BlockExitWalkUnbounded

/-!
# Every block exit of the interpolated walk is attained

Along a path with unbounded range every block exit is attained: at each block-exit time the
shifted path still has unbounded range, so it leaves the (bounded) open block around its current
grid cell in finite time. The linear interpolation of the simple random walk on a locally finite
multigraph embedded by a continuous proper curve has almost surely unbounded range, so almost
surely the step index `τ_n` just after the `n`-th block exit is finite for every `n`.

Consequently the joint law of the block-exit position history `(Y_0, …, Y_n)` and the next
block-exit position `Y_{n+1}` of the interpolated walk is given by a single integral over the
history event, with the walk restarted from its position `x_{τ_n}`:
`P^a((Y_0, …, Y_n) ∈ B, Y_{n+1} ∈ A) = ∫_{(Y_0, …, Y_n) ∈ B} P^{x_{τ_n}}(walkNextBlockExit (Y_n) · ∈ A) dP^a`.

## Main results

* `blockExitsAttained_of_not_isBounded`: along a path with unbounded range all block exits are
  attained.
* `ae_walkBlockExitStepTime_ne_top`: almost surely every step index `τ_n` is finite.
* `measurableSet_blockExitPositions_mem_inter_stepTime_eq`: for every set `B` of position
  histories, `{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}` is a walk event.
* `srwLaw_blockExitPositions_succ_mem_eq_setLIntegral`: the joint law as one integral over the
  history event.
* `srwLaw_blockExitPositions_succ_mem_of_proper`: the same identity for the walk embedded by a
  continuous proper curve, with the finiteness of `τ_n` proved.
-/

open MeasureTheory Set Metric MarkovProcess Filter
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **Block exits along a path with unbounded range are attained.** At each block-exit time the
shifted path has unbounded range, so it leaves the bounded open block around its grid cell. -/
theorem blockExitsAttained_of_not_isBounded {s : ℝ} {F : Set ℂ} {ω : ContinuousPath ℂ}
    (hω : ¬ Bornology.IsBounded (range ω)) (n : ℕ) : BlockExitsAttained s F n ω :=
  fun j _ => Or.inr (exitTime_lt_top_of_not_isBounded
    (not_isBounded_range_shift hω (blockExitTimes s F j ω)) (isBounded_openBlock _ _ _))

/-- If the interpolated walk has unbounded range, the step index just after its `n`-th block exit
is finite. -/
theorem walkBlockExitStepTime_ne_top_of_not_isBounded (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) {s : ℝ}
    {F : Set ℂ} {x : ℕ → ℤ} (hx : ¬ Bornology.IsBounded (range (interpPathCM v hc x)))
    (n : ℕ) : walkBlockExitStepTime v hc s F n x ≠ ⊤ := by
  unfold walkBlockExitStepTime
  simp only [blockExitsAttained_of_not_isBounded hx n, ↓reduceIte]
  exact ENat.natCast_ne_top _

/-- **Almost surely every block exit of the interpolated walk is attained.** For a locally finite
multigraph whose consecutive vertices are adjacent, `ε > 0`, a continuous proper curve `η` and a
speed `c > 0`, almost surely the step index `τ_n` just after the `n`-th block exit of the
interpolated walk is finite for every `n`. -/
theorem ae_walkBlockExitStepTime_ne_top {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (a : ℤ) (s : ℝ)
    (F : Set ℂ) :
    ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ, walkBlockExitStepTime (vertexPoint ε η) hc.le s F n x ≠ ⊤ := by
  filter_upwards [ae_not_isBounded_range_interpPathCM hlf hcons hε hη hp hc a] with x hx n
  exact walkBlockExitStepTime_ne_top_of_not_isBounded _ hc.le hx n

/-- For every set `B` of block-exit position histories (no measurability needed),
`{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}` is a measurable set of walk paths: it is determined by the
first `k` steps. -/
theorem measurableSet_blockExitPositions_mem_inter_stepTime_eq (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c)
    (s : ℝ) (F : Set ℂ) (n : ℕ) (B : Set (Fin (n + 1) → ℂ)) (k : ℕ) :
    MeasurableSet ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
      {x | walkBlockExitStepTime v hc.le s F n x = k}) := by
  obtain ⟨G, hG, h⟩ := walkBlockExitStepTime_history v hc s F n B k
  rw [h]
  exact measurable_pathHist k hG

/-- **Joint law of a position history and the next block-exit position, integral form.** Under
the hypotheses of `srwLaw_blockExitPositions_succ_mem`, for every set `B` of position histories
and measurable `A`,
`P^a((Y_0, …, Y_n) ∈ B, Y_{n+1} ∈ A) =
  ∫_{(Y_0, …, Y_n) ∈ B} P^{x_{τ_n}}(walkNextBlockExit (Y_n) · ∈ A) dP^a`. -/
theorem srwLaw_blockExitPositions_succ_mem_eq_setLIntegral (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ)
    {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 < s) (F : Set ℂ)
    (hE : ExitEdgesShort m v hc.le s F (s / 2))
    (n : ℕ) (B : Set (Fin (n + 1) → ℂ)) {A : Set ℂ} (hA : MeasurableSet A)
    (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc.le s F n x ≠ ⊤) :
    srwLaw m a ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) ∈ A}) =
      ∫⁻ x in {x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B},
        srwLaw m (x (walkBlockExitStepTime v hc.le s F n x).toNat) {x' | walkNextBlockExit v hc.le
          s F (interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x))) x' ∈ A}
          ∂srwLaw m a := by
  rw [srwLaw_blockExitPositions_succ_mem m a v hc hs F hE n B hA hτ]
  have hSm := measurableSet_blockExitPositions_mem_inter_stepTime_eq v hc s F n B
  have hSd : Pairwise (Disjoint on fun k : ℕ =>
      ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | walkBlockExitStepTime v hc.le s F n x = k})) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj => hij ?_
    have hi' : walkBlockExitStepTime v hc.le s F n x = i := hi.2
    have hj' : walkBlockExitStepTime v hc.le s F n x = j := hj.2
    have hij' : (i : ℕ∞) = (j : ℕ∞) := hi'.symm.trans hj'
    exact_mod_cast hij'
  have hU : ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} :
      Set (ℕ → ℤ)) =ᵐ[srwLaw m a]
      (⋃ k : ℕ, ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | walkBlockExitStepTime v hc.le s F n x = k}) : Set (ℕ → ℤ)) := by
    filter_upwards [hτ] with x hx
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hx
    apply propext
    constructor
    · intro hB
      exact mem_iUnion.2 ⟨k, hB, hk.symm⟩
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact hj.1
  rw [setLIntegral_congr hU, lintegral_iUnion hSm hSd]
  refine tsum_congr fun k => setLIntegral_congr_fun (hSm k) fun x hx => ?_
  have hk : walkBlockExitStepTime v hc.le s F n x = k := hx.2
  simp only [hk, ENat.toNat_natCast]

/-- **Joint law of a position history and the next block-exit position for the walk embedded by
a proper curve.** For a locally finite multigraph whose consecutive vertices are adjacent, a
continuous proper curve `η`, `ε > 0`, speed `c > 0` and block size `s > 0`, if every walk step
carrying a block-exit position off `F` has length at most `s / 2`, then for every set `B` of position
histories and every measurable `A`,
`P^a((Y_0, …, Y_n) ∈ B, Y_{n+1} ∈ A) =
  ∫_{(Y_0, …, Y_n) ∈ B} P^{x_{τ_n}}(walkNextBlockExit (Y_n) · ∈ A) dP^a`. -/
theorem srwLaw_blockExitPositions_succ_mem_of_proper {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 < s) (F : Set ℂ)
    (hE : ExitEdgesShort m (vertexPoint ε η) hc.le s F (s / 2))
    (n : ℕ) (B : Set (Fin (n + 1) → ℂ)) {A : Set ℂ} (hA : MeasurableSet A) :
    srwLaw m a ({x : ℕ → ℤ |
          blockExitPositions s F n (interpPathCM (vertexPoint ε η) hc.le x) ∈ B} ∩
        {x | interpPathCM (vertexPoint ε η) hc.le x
          (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)) ∈ A}) =
      ∫⁻ x in {x : ℕ → ℤ |
          blockExitPositions s F n (interpPathCM (vertexPoint ε η) hc.le x) ∈ B},
        srwLaw m (x (walkBlockExitStepTime (vertexPoint ε η) hc.le s F n x).toNat)
          {x' | walkNextBlockExit (vertexPoint ε η) hc.le s F
            (interpPathCM (vertexPoint ε η) hc.le x
              (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x))) x' ∈ A}
          ∂srwLaw m a :=
  srwLaw_blockExitPositions_succ_mem_eq_setLIntegral m a (vertexPoint ε η) hc hs F hE n B hA
    ((ae_walkBlockExitStepTime_ne_top hlf hcons hε hη hp hc a s F).mono fun _ hx => hx n)

end BlockExit

end MatedCRT
