import MatedCRT.FirstPass.Derived.BlockExitWalkStepPosNear
import MatedCRT.FirstPass.Derived.BrownianBlockExitChain

/-!
# Closeness of the walk's one-step block-exit kernel from per-vertex closeness

The one-step kernel `κ_n g` of the block-exit history of the interpolated walk is the mixture,
over the regular conditional law of the walk position `U_n` given `H_n = g`, of the laws of the
next block-exit position from `g_n` under the walk restarted at `U_n`. We show:

* a one-sided Prokhorov bound `ProkhorovLE (κ_n g) ν r e` follows from the same bound for
  almost every mixture component;
* in the frozen set `F` the next-exit law of the walk is within any positive radius of the Dirac
  mass at the current position;
* hence, if every next-exit law of the walk started at a vertex within `s / 2` of a point `y ∉ F`
  is `ProkhorovLE`-close to a reference kernel `L y` which is the Dirac mass on `F`, then
  `ProkhorovLE (κ_n g) (L g_n) r e` holds for almost every block-exit history `g`.

The last statement is specialized to the Brownian block-exit kernel frozen off an open grid
rectangle, for the walk embedded by a continuous proper curve.
-/

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **Mixture step.** If almost every next-exit law in the mixture defining `κ_n g` satisfies
`ProkhorovLE · ν r e`, so does `κ_n g`. -/
theorem prokhorovLE_walkBlockExitStepKernel_of_ae (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (n : ℕ) (g : Fin (n + 1) → ℂ)
    (ν : Measure ℂ) {r e : ℝ}
    (h : ∀ᵐ u ∂condDistrib (walkBlockExitStepPos v hc s F n) (walkBlockExitHistory v hc s F n)
      (srwLaw m a) g,
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (g (Fin.last n), u)) ν r e) :
    LatticeProb.ProkhorovLE (walkBlockExitStepKernel m a v hc s F n g) ν r e := by
  intro A hA
  rw [walkBlockExitStepKernel_apply m a v hc s hF n g hA]
  refine (lintegral_mono_ae (h.mono fun u hu => hu A hA)).trans ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- **Frozen positions.** From a position `y ∈ F` the next-exit law of the walk restarted at any
vertex is `ProkhorovLE`-below the Dirac mass at `y`, for every positive radius. -/
theorem prokhorovLE_walkNextBlockExitKernel_of_mem (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) {y : ℂ} (hy : y ∈ F) (u : ℤ)
    {r e : ℝ} (hr : 0 < r) :
    LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (y, u)) (Measure.dirac y) r e := by
  have := isMarkovKernel_walkNextBlockExitKernel m v hc s hF
  intro A hA
  by_cases hyA : y ∈ A
  · rw [Measure.dirac_apply_of_mem (self_subset_thickening hr A hyA)]
    exact prob_le_one.trans le_self_add
  · have hW : ∀ x : ℕ → ℤ, walkNextBlockExit v hc s F y x = y := fun x => by
      simp only [walkNextBlockExit, hy, not_true_eq_false, false_and, ↓reduceIte]
    have h0 : walkNextBlockExitKernel m v hc s F (y, u) A = 0 := by
      rw [walkNextBlockExitKernel_apply m v hc s hF y u hA]
      simp [hW, hyA]
    rw [h0]
    exact bot_le

/-- **The one-step kernel is close to a reference kernel for almost every history.** Let `L`
be a reference family of laws equal to the Dirac mass on `F`. If, for every `y ∉ F` and every
vertex `u` with `dist (v u) y ≤ s / 2`, the next-exit law of the walk restarted at `u` from the
position `y` satisfies `ProkhorovLE · (L y) r e` with `r > 0`, then for almost every block-exit
history `g` (under the walk law from `a`), `ProkhorovLE (κ_n g) (L g_n) r e`. -/
theorem ae_prokhorovLE_walkBlockExitStepKernel (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ s / 2)
    (n : ℕ) (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc.le s F n x ≠ ⊤)
    (L : ℂ → Measure ℂ) {r e : ℝ} (hr : 0 < r) (hfrozen : ∀ y ∈ F, L y = Measure.dirac y)
    (hclose : ∀ y, y ∉ F → ∀ u : ℤ, dist (v u) y ≤ s / 2 →
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc.le s F (y, u)) (L y) r e) :
    ∀ᵐ g ∂(srwLaw m a).map (walkBlockExitHistory v hc.le s F n),
      LatticeProb.ProkhorovLE (walkBlockExitStepKernel m a v hc.le s F n g)
        (L (g (Fin.last n))) r e := by
  filter_upwards [ae_condDistrib_walkBlockExitStepPos_near m a v hc hs hF hM n hτ] with g hg
  refine prokhorovLE_walkBlockExitStepKernel_of_ae m a v hc.le s hF n g _ ?_
  by_cases hgF : g (Fin.last n) ∈ F
  · rw [hfrozen _ hgF]
    exact Eventually.of_forall fun u =>
      prokhorovLE_walkNextBlockExitKernel_of_mem m v hc.le s hF hgF u hr
  · exact (hg hgF).mono fun u hu => hclose _ hgF u hu

/-- **Grid-rectangle form for the walk embedded by a continuous proper curve.** With `F` the
complement of the open grid rectangle and the reference kernel the Brownian block-exit kernel
frozen off that rectangle: per-vertex closeness for the vertices within `s / 2` of points of the
rectangle gives `ProkhorovLE (κ_n g) (gridRectBlockExitKernel … g_n) r e` for almost every
block-exit history `g`. -/
theorem ae_prokhorovLE_walkBlockExitStepKernel_gridRect_of_proper {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 ≤ s) (a₁ a₂ c₁ c₂ : ℤ)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
        z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (n : ℕ) {r e : ℝ} (hr : 0 < r)
    (hclose : ∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      LatticeProb.ProkhorovLE
        (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ (y, u))
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) r e) :
    ∀ᵐ g ∂(srwLaw m a).map
        (walkBlockExitHistory (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ n),
      LatticeProb.ProkhorovLE
        (walkBlockExitStepKernel m a (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ n g)
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last n))) r e :=
  ae_prokhorovLE_walkBlockExitStepKernel m a (vertexPoint ε η) hc hs
    (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl hM n
    ((ae_walkBlockExitStepTime_ne_top hlf hcons hε hη hp hc a s _).mono fun _ hx => hx n)
    (fun y => gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) hr
    (fun _ hy => frozenBlockExitKernel_of_mem s _ hy)
    (fun y hy u hu => hclose y (by simpa using hy) u hu)

end BlockExit

end MatedCRT
