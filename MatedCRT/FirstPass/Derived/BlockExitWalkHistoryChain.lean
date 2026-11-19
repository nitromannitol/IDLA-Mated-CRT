import MatedCRT.FirstPass.Derived.BlockExitWalkGridLines
import LatticeProb.Prob.PaddedHistoryLaw
import LatticeProb.Prob.DependentKernelMap

/-!
# The block-exit history of the interpolated walk as a chain on padded histories

The law of the first `N + 1` block-exit positions `(Y_0, …, Y_N)` of the linear interpolation of
the simple random walk started at `x₀` is the `N`-th law of a chain on the histories
`Fin (N + 1) → ℂ`, started from the constant history at the embedded start `vertexPoint ε η x₀`,
whose step `n` samples the next position from the kernel `κ_n` of the walk read on the first
`n + 1` entries of the history (`walkPaddedStepKernel`).

The history `H_n = (Y_0, …, Y_n)` is embedded into `Fin (N + 1) → ℂ` by repeating its last entry
(`historyEmbed`), which the restriction `historyRestrict` inverts for `n ≤ N`, so the
composition-product identity `P^{x₀} ∘ (H_n, Y_{n+1})⁻¹ = (P^{x₀} ∘ H_n⁻¹) ⊗ₘ κ_n` transfers to the
padded histories. The walk starts at `x₀` only almost surely; the position sequence
`walkBlockExitPos` reads the position at time `0` as `vertexPoint ε η x₀` for every path, and agrees
almost surely with the block-exit positions.

## Main definitions

* `walkBlockExitPos`: the block-exit positions, with the position at time `0` fixed.
* `historyEmbed`, `historyRestrict`: padding a history of length `n + 1` and its inverse.
* `walkPaddedStepKernel`: the one-step kernel `κ_n` read on padded histories.

## Main results

* `map_walkPaddedHistory_next_eq_compProd`: the composition-product identity on padded histories.
* `map_blockExitPositions_eq_chainSeqLaw`: the block-exit history law is the padded history chain.
-/

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- The block-exit positions `Y_n` of the interpolated walk, with the position at time `0` read as
the embedded start `v x₀` for every path. -/
noncomputable def walkBlockExitPos (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (x₀ : ℤ) : ℕ → (ℕ → ℤ) → ℂ
  | 0 => fun _ => v x₀
  | n + 1 => fun x => interpPathCM v hc x (blockExitTimes s F (n + 1) (interpPathCM v hc x))

theorem walkBlockExitPos_eq (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ) {x₀ : ℤ}
    {x : ℕ → ℤ} (hx : x 0 = x₀) :
    ∀ k : ℕ, walkBlockExitPos v hc s F x₀ k x =
      interpPathCM v hc x (blockExitTimes s F k (interpPathCM v hc x))
  | 0 => by
    show v x₀ = _
    rw [blockExitTimes_zero, interpPathCM_apply_zero, hx]
  | _ + 1 => rfl

theorem measurable_walkBlockExitPos (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ}
    (hF : MeasurableSet F) (x₀ : ℤ) : ∀ n, Measurable (walkBlockExitPos v hc s F x₀ n)
  | 0 => measurable_const
  | n + 1 => by
    have heq : walkBlockExitPos v hc s F x₀ (n + 1) =
        fun x => blockExitPositions s F (n + 1) (interpPathCM v hc x) (Fin.last (n + 1)) := by
      funext x
      rw [blockExitPositions_apply, Fin.val_last]
      rfl
    rw [heq]
    exact (measurable_pi_apply _).comp
      ((measurable_blockExitPositions s hF (n + 1)).comp (measurable_interpPathCM _ hc))

/-- A history of length `n + 1` as a history of length `N + 1`, padded by its last entry. -/
def historyEmbed (n N : ℕ) (g : Fin (n + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => g ⟨min (i : ℕ) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The first `n + 1` entries of a history of length `N + 1` (the last entry repeated if
`n > N`). -/
def historyRestrict (n N : ℕ) (h : Fin (N + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun j => h ⟨min (j : ℕ) N, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem measurable_historyEmbed (n N : ℕ) : Measurable (historyEmbed n N) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_historyRestrict (n N : ℕ) : Measurable (historyRestrict n N) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem historyRestrict_historyEmbed {n N : ℕ} (hn : n ≤ N) (g : Fin (n + 1) → ℂ) :
    historyRestrict n N (historyEmbed n N g) = g := by
  funext j
  apply congrArg g
  apply Fin.ext
  show min (min (j : ℕ) N) n = j
  have := j.is_lt
  omega

/-- The one-step kernel `κ_n` of the walk's block-exit history, read on the first `n + 1` entries
of a history of length `N + 1`. -/
noncomputable def walkPaddedStepKernel (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ) (N n : ℕ) : Kernel (Fin (N + 1) → ℂ) ℂ :=
  (walkBlockExitStepKernel m a v hc s F n).comap (historyRestrict n N)
    (measurable_historyRestrict n N)

theorem isMarkovKernel_walkPaddedStepKernel (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (N n : ℕ) :
    IsMarkovKernel (walkPaddedStepKernel m a v hc s F N n) := by
  have := isMarkovKernel_walkBlockExitStepKernel m a v hc s hF n
  unfold walkPaddedStepKernel
  infer_instance

theorem walkPaddedStepKernel_historyEmbed (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ) {N n : ℕ} (hn : n ≤ N) (g : Fin (n + 1) → ℂ) :
    walkPaddedStepKernel m a v hc s F N n (historyEmbed n N g) =
      walkBlockExitStepKernel m a v hc s F n g := by
  rw [walkPaddedStepKernel, Kernel.comap_apply, historyRestrict_historyEmbed hn]

/-- On paths started at `x₀`, the padded history of the positions `walkBlockExitPos` after `n`
steps is the padding of the block-exit history `H_n`. -/
theorem paddedHistory_walkBlockExitPos_eq (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    {x₀ : ℤ} {x : ℕ → ℤ} (hx : x 0 = x₀) (N n : ℕ) :
    (paddedHistory (walkBlockExitPos v hc s F x₀) n x : Fin (N + 1) → ℂ) =
      historyEmbed n N (walkBlockExitHistory v hc s F n x) := by
  funext i
  simp only [paddedHistory, historyEmbed, walkBlockExitHistory]
  rw [blockExitPositions_apply, walkBlockExitPos_eq v hc s F hx]

/-- **The composition-product identity on padded histories.** Under the hypotheses of
`map_walkBlockExitHistory_next_eq_compProd_of_proper`, for `n ≤ N` the joint law of the padded
history after `n` steps and of the next block-exit position is the composition-product of the law
of the padded history with `walkPaddedStepKernel`. -/
theorem map_walkPaddedHistory_next_eq_compProd {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (x₀ : ℤ) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    {N n : ℕ} (hn : n ≤ N) :
    (srwLaw m x₀).map (fun x =>
        ((paddedHistory (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n x :
          Fin (N + 1) → ℂ), walkBlockExitPos (vertexPoint ε η) hc.le s F x₀ (n + 1) x)) =
      (srwLaw m x₀).map
          (paddedHistory (N := N) (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n) ⊗ₘ
        walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n := by
  have := isMarkovKernel_walkBlockExitStepKernel m x₀ (vertexPoint ε η) hc.le s hF n
  have hH : Measurable (walkBlockExitHistory (vertexPoint ε η) hc.le s F n) :=
    measurable_walkBlockExitHistory _ hc.le s hF n
  have hY : Measurable fun x : ℕ → ℤ => interpPathCM (vertexPoint ε η) hc.le x
      (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)) :=
    measurable_walkBlockExitPos _ hc.le s hF x₀ (n + 1)
  have hE : Measurable fun p : (Fin (n + 1) → ℂ) × ℂ => (historyEmbed n N p.1, p.2) :=
    ((measurable_historyEmbed n N).comp measurable_fst).prodMk measurable_snd
  have hae : ∀ᵐ x ∂srwLaw m x₀,
      (paddedHistory (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n x :
        Fin (N + 1) → ℂ) = historyEmbed n N (walkBlockExitHistory (vertexPoint ε η) hc.le s F n x) := by
    filter_upwards [srwLaw_ae_start m x₀] with x hx
    exact paddedHistory_walkBlockExitPos_eq _ hc.le s F hx N n
  have h1 : (srwLaw m x₀).map (fun x =>
        ((paddedHistory (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n x :
          Fin (N + 1) → ℂ), walkBlockExitPos (vertexPoint ε η) hc.le s F x₀ (n + 1) x)) =
      ((srwLaw m x₀).map (fun x => (walkBlockExitHistory (vertexPoint ε η) hc.le s F n x,
        interpPathCM (vertexPoint ε η) hc.le x
          (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x))))).map
        (fun p : (Fin (n + 1) → ℂ) × ℂ => (historyEmbed n N p.1, p.2)) := by
    rw [Measure.map_map hE (hH.prodMk hY)]
    exact Measure.map_congr (hae.mono fun x hx => Prod.ext hx rfl)
  have h2 : (srwLaw m x₀).map
        (paddedHistory (N := N) (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n) =
      ((srwLaw m x₀).map (walkBlockExitHistory (vertexPoint ε η) hc.le s F n)).map
        (historyEmbed n N) := by
    rw [Measure.map_map (measurable_historyEmbed n N) hH]
    exact Measure.map_congr hae
  rw [h1, h2, map_walkBlockExitHistory_next_eq_compProd_of_proper hlf hcons hε hη hp hc x₀ hs hF
    hM n]
  have := isMarkovKernel_walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s hF N n
  exact compProd_map_dependent_of_kernel_map _ _ _ (historyEmbed n N) (fun _ b => b)
    (measurable_historyEmbed n N) measurable_snd fun g => by
      rw [Measure.map_id', walkPaddedStepKernel_historyEmbed _ _ _ _ _ _ hn]

/-- **The walk's block-exit history law is a chain on padded histories.** Under the hypotheses of
`map_walkBlockExitHistory_next_eq_compProd_of_proper`, the law under `P^{x₀}` of the first `N + 1`
block-exit positions of the interpolated walk is the `N`-th law of the chain on `Fin (N + 1) → ℂ`
with steps `paddedHistoryKernel n (walkPaddedStepKernel … N n)`, started from the constant history
at `vertexPoint ε η x₀`. -/
theorem map_blockExitPositions_eq_chainSeqLaw {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (x₀ : ℤ) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (N : ℕ) :
    (srwLaw m x₀).map
        (fun x => blockExitPositions s F N (interpPathCM (vertexPoint ε η) hc.le x)) =
      chainSeqLaw (fun n => paddedHistoryKernel n
          (walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n))
        (Measure.dirac fun _ => vertexPoint ε η x₀) N := by
  have := fun n => isMarkovKernel_walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s hF N n
  have hlaw := map_history_eq_chainSeqLaw (μ := srwLaw m x₀)
    (measurable_walkBlockExitPos (vertexPoint ε η) hc.le s hF x₀) (z := vertexPoint ε η x₀)
    (fun _ => rfl) (fun n => walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n)
    (fun n hn => map_walkPaddedHistory_next_eq_compProd hlf hcons hε hη hp hc x₀ hs hF hM hn.le)
  rw [← hlaw]
  refine Measure.map_congr ?_
  filter_upwards [srwLaw_ae_start m x₀] with x hx
  funext i
  rw [blockExitPositions_apply, walkBlockExitPos_eq _ hc.le s F hx]

end BlockExit

end MatedCRT
