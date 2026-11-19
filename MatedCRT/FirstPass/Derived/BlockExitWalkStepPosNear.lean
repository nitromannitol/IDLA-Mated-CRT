import MatedCRT.FirstPass.Derived.BlockExitWalkCompProd

/-!
# The walk position after a block exit is within one edge of the exit point

For the linear interpolation at speed `c` of a walk on the multigraph `m` embedded by `v`, the
`n`-th block-exit position `Y_n = X(σ_n)` lies on the edge segment traversed between the steps
`⌊c σ_n⌋` and `τ_n = ⌊c σ_n⌋ + 1`. If every edge whose segment meets `Fᶜ` has length at most
`s / 2`, then off the frozen set `F` the walk position `U_n = x_{τ_n}` is within `s / 2` of
`Y_n`. We prove this pathwise, almost surely under the walk law, and for the regular conditional
distribution of `U_n` given the history `H_n = (Y_0, …, Y_n)`: for almost every history `g` with
`g_n ∉ F`, the conditional law of `U_n` is carried by the vertices within `s / 2` of `g_n`.
We also record the one-step kernel `κ_n` as the mixture, over this conditional law, of the
next-block-exit kernels.
-/

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **Pathwise: the walk position after the `n`-th block exit is within one edge of `Y_n`.** If
`τ_n < ∞`, every step of `x` is a loop or an edge of `m`, `Y_n ∉ F`, and every edge whose segment
meets `Fᶜ` has length at most `s / 2`, then `dist (v x_{τ_n}) Y_n ≤ s / 2`. -/
theorem dist_walkBlockExitStepPos_le (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) {s : ℝ}
    (hs : 0 ≤ s) {F : Set ℂ}
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ s / 2)
    (n : ℕ) {x : ℕ → ℤ} (hτ : walkBlockExitStepTime v hc s F n x ≠ ⊤)
    (hadj : ∀ k : ℕ, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0)
    (hYF : walkBlockExitHistory v hc s F n x (Fin.last n) ∉ F) :
    dist (v (walkBlockExitStepPos v hc s F n x)) (walkBlockExitHistory v hc s F n x (Fin.last n))
      ≤ s / 2 := by
  have hA : BlockExitsAttained s F n (interpPathCM v hc x) := by
    by_contra h
    exact hτ (by simp only [walkBlockExitStepTime, h, ↓reduceIte])
  have hpos : walkBlockExitStepPos v hc s F n x =
      x (⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊ + 1) := by
    simp only [walkBlockExitStepPos, walkBlockExitStepTime, hA, ↓reduceIte, ENat.toNat_natCast]
  have hY : walkBlockExitHistory v hc s F n x (Fin.last n) =
      interpPathCM v hc x (blockExitTimes s F n (interpPathCM v hc x)) := by
    simp only [walkBlockExitHistory, blockExitPositions_apply, Fin.val_last]
  rw [hpos, hY]
  rw [hY] at hYF
  have hnn : 0 ≤ c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ) :=
    mul_nonneg hc (NNReal.coe_nonneg _)
  have hseg := interpPathCM_mem_segment v hc x (Nat.floor_le hnn) (Nat.lt_floor_add_one _).le
  rcases hadj ⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊ with heq | hm
  · rw [heq, segment_same, mem_singleton_iff] at hseg
    rw [heq, hseg, dist_self]
    exact div_nonneg hs zero_le_two
  · have hlen := hM _ _ hm ⟨_, hseg, hYF⟩
    have hball := segment_subset_closedBall_of_mem hseg (right_mem_segment ℝ _ _)
    rw [mem_closedBall] at hball
    exact hball.trans hlen

/-- **Almost surely the walk position after the `n`-th block exit is within one edge of `Y_n`**,
off the frozen set `F`, provided `τ_n` is almost surely finite. -/
theorem ae_dist_walkBlockExitStepPos_le (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) {s : ℝ} (hs : 0 ≤ s) {F : Set ℂ}
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ s / 2)
    (n : ℕ) (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc s F n x ≠ ⊤) :
    ∀ᵐ x ∂srwLaw m a, walkBlockExitHistory v hc s F n x (Fin.last n) ∉ F →
      dist (v (walkBlockExitStepPos v hc s F n x))
        (walkBlockExitHistory v hc s F n x (Fin.last n)) ≤ s / 2 := by
  have hadj : ∀ᵐ x ∂srwLaw m a, ∀ k : ℕ, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0 :=
    ae_all_iff.2 fun k => ae_iff.2 (WalkSteps.srwLaw_nonadjacent_null m k a)
  filter_upwards [hτ, hadj] with x hx hx' hYF
  exact dist_walkBlockExitStepPos_le m v hc hs hM n hx hx' hYF

/-- **The conditional law of `U_n` given the history is carried near `g_n`.** For almost every
block-exit history `g` (under the walk law from `a`) with `g_n ∉ F`, the regular conditional
distribution of the walk position `U_n = x_{τ_n}` given `H_n = g` is carried by the vertices `u`
with `dist (v u) g_n ≤ s / 2`. -/
theorem ae_condDistrib_walkBlockExitStepPos_near (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ s / 2)
    (n : ℕ) (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc.le s F n x ≠ ⊤) :
    ∀ᵐ g ∂(srwLaw m a).map (walkBlockExitHistory v hc.le s F n), g (Fin.last n) ∉ F →
      ∀ᵐ u ∂condDistrib (walkBlockExitStepPos v hc.le s F n)
        (walkBlockExitHistory v hc.le s F n) (srwLaw m a) g,
        dist (v u) (g (Fin.last n)) ≤ s / 2 := by
  have hH := measurable_walkBlockExitHistory v hc.le s hF n
  have hU := measurable_walkBlockExitStepPos v hc s F n
  have hlast : Measurable fun p : (Fin (n + 1) → ℂ) × ℤ => p.1 (Fin.last n) :=
    (measurable_pi_apply (Fin.last n)).comp measurable_fst
  have hd : Measurable fun p : (Fin (n + 1) → ℂ) × ℤ => dist (v p.2) (p.1 (Fin.last n)) :=
    ((measurable_of_countable v).comp measurable_snd).dist hlast
  have hS : MeasurableSet ({p : (Fin (n + 1) → ℂ) × ℤ | p.1 (Fin.last n) ∈ F} ∪
      {p | dist (v p.2) (p.1 (Fin.last n)) ≤ s / 2}) :=
    (hlast hF).union (measurableSet_le hd measurable_const)
  have h1 : ∀ᵐ p ∂(srwLaw m a).map (fun x => (walkBlockExitHistory v hc.le s F n x,
      walkBlockExitStepPos v hc.le s F n x)),
      p ∈ ({p : (Fin (n + 1) → ℂ) × ℤ | p.1 (Fin.last n) ∈ F} ∪
        {p | dist (v p.2) (p.1 (Fin.last n)) ≤ s / 2}) := by
    refine (ae_map_iff (hH.prodMk hU).aemeasurable hS).2 ?_
    filter_upwards [ae_dist_walkBlockExitStepPos_le m a v hc.le hs hM n hτ] with x hx
    by_cases hxF : walkBlockExitHistory v hc.le s F n x (Fin.last n) ∈ F
    · exact Or.inl hxF
    · exact Or.inr (hx hxF)
  rw [← compProd_map_condDistrib hH.aemeasurable hU.aemeasurable] at h1
  filter_upwards [Measure.ae_ae_of_ae_compProd h1] with g hg hgF
  filter_upwards [hg] with u hu
  rcases hu with hu | hu
  · exact absurd hu hgF
  · exact hu

/-- The same for the walk embedded by a continuous proper curve, with `τ_n < ∞` proved. -/
theorem ae_condDistrib_walkBlockExitStepPos_near_of_proper {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 ≤ s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (n : ℕ) :
    ∀ᵐ g ∂(srwLaw m a).map (walkBlockExitHistory (vertexPoint ε η) hc.le s F n),
      g (Fin.last n) ∉ F →
      ∀ᵐ u ∂condDistrib (walkBlockExitStepPos (vertexPoint ε η) hc.le s F n)
        (walkBlockExitHistory (vertexPoint ε η) hc.le s F n) (srwLaw m a) g,
        dist (vertexPoint ε η u) (g (Fin.last n)) ≤ s / 2 :=
  ae_condDistrib_walkBlockExitStepPos_near m a (vertexPoint ε η) hc hs hF hM n
    ((ae_walkBlockExitStepTime_ne_top hlf hcons hε hη hp hc a s F).mono fun _ hx => hx n)

/-- **The one-step kernel is a mixture of next-block-exit kernels**: `κ_n g` is the average,
over the conditional law of `U_n` given `H_n = g`, of the law of the next block-exit position
from `g_n` under the walk restarted at `U_n`. -/
theorem walkBlockExitStepKernel_apply (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (n : ℕ) (g : Fin (n + 1) → ℂ)
    {A : Set ℂ} (hA : MeasurableSet A) :
    walkBlockExitStepKernel m a v hc s F n g A =
      ∫⁻ u, walkNextBlockExitKernel m v hc s F (g (Fin.last n), u) A
        ∂condDistrib (walkBlockExitStepPos v hc s F n) (walkBlockExitHistory v hc s F n)
          (srwLaw m a) g := by
  have := isMarkovKernel_walkNextBlockExitKernel m v hc s hF
  rw [walkBlockExitStepKernel, Kernel.snd_apply' _ _ hA, Kernel.compProd_apply (measurable_snd hA)]
  rfl

end BlockExit

end MatedCRT
