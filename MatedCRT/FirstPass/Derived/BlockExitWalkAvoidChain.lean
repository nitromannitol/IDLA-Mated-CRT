import MatedCRT.FirstPass.Derived.BlockExitWalkHistoryChain
import MatedCRT.FirstPass.Derived.BlockExitWalkStepKernelClose
import MatedCRT.FirstPass.Derived.BlockExitWalkAvoidBound

/-!
# The walk's block-exit chain from the one-step closeness

Freeze the block-exit chain off the open grid rectangle `R = (a₁ s, a₂ s) × (c₁ s, c₂ s)`, that is
take `F = Rᶜ`, and start the walk at a vertex `x₀` whose embedded position `z = vertexPoint ε η x₀`
lies in `R`. Suppose the one-step closeness `hclose`: from every point `y ∈ R` and every vertex `u`
within `s / 2` of `y`, the law of the next block-exit position of the walk is `(δ, δ)`-close to the
frozen grid-rectangle block-exit kernel at `y` in the one-sided Lévy-Prokhorov sense.

The law of the first `N + 1` block-exit positions is the chain on padded histories whose step `n`
is the walk's kernel `walkPaddedStepKernel … N n` (`map_blockExitPositions_eq_chainSeqLaw`). Its
closeness to the frozen kernel and its concentration on the grid lines hold only for almost every
padded history. Modifying the step kernels on a measurable null set of padded histories (where they
are replaced by the frozen kernel read at the last entry) does not change the chain law, and gives
step laws with both properties at every history. Together with
`srwLaw_blockExit_avoid_frozen_le_of_chain` this bounds the probability that the first
`N = ⌊r ^ (-(2 + ζ))⌋` block-exit positions of the walk all stay in `R`, with `hclose` as the only
hypothesis on the walk's increments.

## Main results

* `exists_chain_of_hclose_frozen`: the modified step laws, for a chain frozen on a measurable set
  `F` with the start off `F`; `exists_chain_of_hclose` is the grid-rectangle form.
* `srwLaw_blockExit_avoid_frozen_le_of_hclose`: the bound with `hclose` as the walk hypothesis.
* `prokhorovLE_srwLaw_blockExitPositions_of_hclose`: the law of the first `N + 1` block-exit
  positions of the walk is within `((N + 1) δ, N δ + 60 N³ δ / s)` of that of planar Brownian
  motion started at the embedded start, in the one-sided Lévy-Prokhorov sense;
  `prokhorovLE_srwLaw_blockExitPositions_of_hclose_frozen` is the same for a measurable grid-line
  stable frozen set `F` (`GridLineStable`), with `hclose` required off `F`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- A property holding almost everywhere holds on a measurable set of full measure: the complement
of a measurable hull of the exceptional set. The set is defined from the property alone, and is
contained in the set where the property holds in any case. -/
theorem exists_measurableSet_forall_mem_of_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → Prop) :
    ∃ S : Set α, MeasurableSet S ∧ (∀ x ∈ S, p x) ∧ ((∀ᵐ x ∂μ, p x) → ∀ᵐ x ∂μ, x ∈ S) := by
  refine ⟨(toMeasurable μ {x | ¬p x})ᶜ, (measurableSet_toMeasurable _ _).compl,
    fun x hx => Classical.byContradiction fun hpx => hx (subset_toMeasurable _ _ hpx),
    fun h => ?_⟩
  refine ae_iff.2 (measure_mono_null (fun x hx => Classical.byContradiction fun hT => hx hT) ?_)
  rw [measure_toMeasurable]
  exact ae_iff.1 h

/-- A measure is `(r, e)`-close to itself in the one-sided Lévy-Prokhorov sense for `0 < r` and
`0 ≤ e`. -/
theorem prokhorovLE_self_of_pos {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (μ : Measure E) {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e) : ProkhorovLE μ μ r e :=
  fun A hA => (prokhorovLE_refl μ hr A hA).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal he))

/-- The padding of a history of length `n + 1` ends with its last entry. -/
theorem historyEmbed_last {n N : ℕ} (hn : n ≤ N) (g : Fin (n + 1) → ℂ) :
    historyEmbed n N g (Fin.last N) = g (Fin.last n) :=
  congrArg g (Fin.ext (by simp [hn]))

/-- For `n ≤ N`, the padding of histories of length `n + 1` to length `N + 1` is a measurable
embedding. -/
theorem measurableEmbedding_historyEmbed {n N : ℕ} (hn : n ≤ N) :
    MeasurableEmbedding (historyEmbed n N) := by
  refine MeasurableEmbedding.of_measurable_inverse (measurable_historyEmbed n N) ?_
    (measurable_historyRestrict n N) (historyRestrict_historyEmbed hn)
  have hr : range (historyEmbed n N) =
      ⋂ i, {h | historyEmbed n N (historyRestrict n N h) i = h i} := by
    ext h
    refine ⟨?_, fun hh => ⟨historyRestrict n N h, funext fun i => mem_iInter.1 hh i⟩⟩
    rintro ⟨g, rfl⟩
    exact mem_iInter.2 fun i =>
      congrFun (congrArg (historyEmbed n N) (historyRestrict_historyEmbed hn g)) i
  rw [hr]
  exact MeasurableSet.iInter fun i => measurableSet_eq_fun
    ((measurable_pi_apply i).comp ((measurable_historyEmbed n N).comp
      (measurable_historyRestrict n N))) (measurable_pi_apply i)

/-- For `n ≤ N`, a property of padded histories holds almost everywhere for the image of a law of
histories of length `n + 1` as soon as it holds almost everywhere at the paddings. -/
theorem ae_map_historyEmbed {n N : ℕ} (hn : n ≤ N) {μ : Measure (Fin (n + 1) → ℂ)}
    {p : (Fin (N + 1) → ℂ) → Prop} (h : ∀ᵐ g ∂μ, p (historyEmbed n N g)) :
    ∀ᵐ h ∂μ.map (historyEmbed n N), p h :=
  (measurableEmbedding_historyEmbed hn).ae_map_iff.2 h

/-- The law of the padded history of the positions `walkBlockExitPos` after `n` steps is the image
under padding of the law of the block-exit history `H_n`. -/
theorem map_paddedHistory_walkBlockExitPos_eq (m : ℤ → ℤ → ℕ) (x₀ : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (N n : ℕ) :
    (srwLaw m x₀).map (paddedHistory (N := N) (walkBlockExitPos v hc s F x₀) n) =
      ((srwLaw m x₀).map (walkBlockExitHistory v hc s F n)).map (historyEmbed n N) := by
  rw [Measure.map_map (measurable_historyEmbed n N) (measurable_walkBlockExitHistory v hc s hF n)]
  refine Measure.map_congr ?_
  filter_upwards [srwLaw_ae_start m x₀] with x hx
  exact paddedHistory_walkBlockExitPos_eq v hc s F hx N n

/-- The block-exit kernel frozen on a measurable set `F` charges only the grid lines from a point
off `F` or of the grid lines. -/
theorem frozenBlockExitKernel_gridLines_compl_of_notMem_or {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    (hF : MeasurableSet F) {y : ℂ} (hy : y ∉ F ∨ y ∈ gridLines s) :
    frozenBlockExitKernel s hF y (gridLines s)ᶜ = 0 := by
  rcases hy with hy | hy
  · rw [frozenBlockExitKernel_of_notMem s hF hy]
    exact cellBlockExitKernel_gridLines_compl hs y
  · have hy' : y ∉ (gridLines s)ᶜ := fun h => h hy
    exact nonpos_iff_eq_zero.1 ((frozenBlockExitKernel_gridLines_compl_le hs hF y).trans_eq
      (indicator_of_notMem hy' _))

/-- The frozen grid-rectangle block-exit kernel charges only the grid lines from a point of the
open grid rectangle or of the grid lines. -/
theorem gridRectBlockExitKernel_gridLines_compl {s : ℝ} (hs : 0 < s) (a₁ a₂ c₁ c₂ : ℤ) {y : ℂ}
    (hy : y ∈ gridRectOpen s a₁ a₂ c₁ c₂ ∨ y ∈ gridLines s) :
    gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y (gridLines s)ᶜ = 0 :=
  frozenBlockExitKernel_gridLines_compl_of_notMem_or hs _ (hy.imp_left fun h h' => h' h)

/-- **Frozen-set form for the walk embedded by a continuous proper curve.** With the reference
kernel the Brownian block-exit kernel frozen on a measurable set `F`: per-vertex closeness for the
vertices within `s / 2` of points off `F` gives
`ProkhorovLE (κ_n g) (frozenBlockExitKernel s hF g_n) r e` for almost every block-exit history
`g`. -/
theorem ae_prokhorovLE_walkBlockExitStepKernel_frozen_of_proper {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 ≤ s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (n : ℕ) {r e : ℝ} (hr : 0 < r)
    (hclose : ∀ y ∉ F, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      ProkhorovLE (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s F (y, u))
        (frozenBlockExitKernel s hF y) r e) :
    ∀ᵐ g ∂(srwLaw m a).map (walkBlockExitHistory (vertexPoint ε η) hc.le s F n),
      ProkhorovLE (walkBlockExitStepKernel m a (vertexPoint ε η) hc.le s F n g)
        (frozenBlockExitKernel s hF (g (Fin.last n))) r e :=
  ae_prokhorovLE_walkBlockExitStepKernel m a (vertexPoint ε η) hc hs hF hM n
    ((ae_walkBlockExitStepTime_ne_top hlf hcons hε hη hp hc a s _).mono fun _ hx => hx n)
    (fun y => frozenBlockExitKernel s hF y) hr (fun _ hy => frozenBlockExitKernel_of_mem s _ hy)
    hclose

/-- **Step laws of the walk's block-exit chain from the one-step closeness.** Freeze the chain on
a measurable set `F`, start the walk at `x₀` with `vertexPoint ε η x₀ ∉ F`, and assume the one-step
closeness `hclose` of the next block-exit position to the block-exit kernel frozen on `F`.
Then there are step laws `q n` on padded histories of length `N + 1`, measurable and probability
measures, charging only the grid lines from histories ending at the start or on the grid lines,
`(δ, δ)`-close to the frozen kernel at the last entry at every history, and such that the law of the
first `N + 1` block-exit positions is the history chain with steps `q n` started at the constant
history. -/
theorem exists_chain_of_hclose_frozen {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (x₀ : ℤ) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hz : vertexPoint ε η x₀ ∉ F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
        z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hclose : ∀ y ∉ F, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      ProkhorovLE
        (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s F (y, u))
        (frozenBlockExitKernel s hF y) δ δ)
    (N : ℕ) :
    ∃ q : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ, (∀ n, Measurable (q n)) ∧
      (∀ n g, IsProbabilityMeasure (q n g)) ∧
      (∀ n < N, ∀ g, (g (Fin.last N) = vertexPoint ε η x₀ ∨ g (Fin.last N) ∈ gridLines s) →
        q n g (gridLines s)ᶜ = 0) ∧
      (∀ n < N, ∀ g, ProkhorovLE (q n g)
        (frozenBlockExitKernel s hF (g (Fin.last N))) δ δ) ∧
      (srwLaw m x₀).map (fun x => blockExitPositions s F N
          (interpPathCM (vertexPoint ε η) hc.le x)) =
        chainSeqLaw (fun n => paddedHistoryKernel n (q n))
          (Measure.dirac fun _ => vertexPoint ε η x₀) N := by
  classical
  have hW := fun n => isMarkovKernel_walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s hF N n
  -- measurable full-measure sets of padded histories where the walk's step kernel is good
  choose S hS hSp hSae using fun n => exists_measurableSet_forall_mem_of_ae
    ((srwLaw m x₀).map (paddedHistory (N := N)
      (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n))
    (fun h => ProkhorovLE
        (walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n h)
        (frozenBlockExitKernel s hF (h (Fin.last N))) δ δ ∧
      walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n h
        (gridLines s)ᶜ = 0)
  have hgood : ∀ n ≤ N, ∀ᵐ h ∂(srwLaw m x₀).map (paddedHistory (N := N)
      (walkBlockExitPos (vertexPoint ε η) hc.le s F x₀) n),
      h ∈ S n := by
    intro n hn
    refine hSae n ?_
    rw [map_paddedHistory_walkBlockExitPos_eq m x₀ (vertexPoint ε η) hc.le s hF N n]
    refine ae_map_historyEmbed hn ?_
    filter_upwards [ae_prokhorovLE_walkBlockExitStepKernel_frozen_of_proper hlf hcons hε hη hp
        hc x₀ hs.le hF hM n hδ hclose,
      ae_walkBlockExitStepKernel_gridLines_compl hlf hcons hε hη hp hc x₀ hs hF
        hz hM n] with g hg1 hg2
    rw [walkPaddedStepKernel_historyEmbed _ _ _ _ _ _ hn, historyEmbed_last hn]
    exact ⟨hg1, hg2⟩
  -- the step kernels modified on the null sets
  obtain ⟨q, hq⟩ : ∃ q : ℕ → Kernel (Fin (N + 1) → ℂ) ℂ, ∀ n, q n = Kernel.piecewise (hS n)
      (walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n)
      ((frozenBlockExitKernel s hF).comap (fun h => h (Fin.last N))
        (measurable_pi_apply _)) := ⟨_, fun _ => rfl⟩
  have hqM : ∀ n, IsMarkovKernel (q n) := fun n => by rw [hq n]; infer_instance
  have hq_mem : ∀ n g, g ∈ S n → q n g =
      walkPaddedStepKernel m x₀ (vertexPoint ε η) hc.le s F N n g :=
    fun n g hg => by rw [hq n, Kernel.piecewise_apply]; simp only [hg, ↓reduceIte]
  have hq_nmem : ∀ n g, g ∉ S n →
      q n g = frozenBlockExitKernel s hF (g (Fin.last N)) :=
    fun n g hg => by
      rw [hq n, Kernel.piecewise_apply]; simp only [hg, ↓reduceIte, Kernel.comap_apply]
  refine ⟨fun n => q n, fun n => (q n).measurable,
    fun n g => by have := hqM n; infer_instance, ?_, ?_, ?_⟩
  · beta_reduce
    intro n _ g hg
    by_cases hgS : g ∈ S n
    · rw [hq_mem n g hgS]
      exact (hSp n g hgS).2
    · rw [hq_nmem n g hgS]
      rcases hg with hg | hg
      · rw [hg]
        exact frozenBlockExitKernel_gridLines_compl_of_notMem_or hs hF (Or.inl hz)
      · exact frozenBlockExitKernel_gridLines_compl_of_notMem_or hs hF (Or.inr hg)
  · beta_reduce
    intro n _ g
    by_cases hgS : g ∈ S n
    · rw [hq_mem n g hgS]
      exact (hSp n g hgS).1
    · rw [hq_nmem n g hgS]
      exact prokhorovLE_self_of_pos _ hδ hδ.le
  · beta_reduce
    have hκ : ∀ n < N, (srwLaw m x₀).map (fun x =>
        ((paddedHistory (walkBlockExitPos (vertexPoint ε η) hc.le s
          F x₀) n x : Fin (N + 1) → ℂ),
          walkBlockExitPos (vertexPoint ε η) hc.le s F x₀ (n + 1) x)) =
        (srwLaw m x₀).map (paddedHistory (N := N) (walkBlockExitPos (vertexPoint ε η) hc.le s
          F x₀) n) ⊗ₘ q n := by
      intro n hn
      rw [map_walkPaddedHistory_next_eq_compProd hlf hcons hε hη hp hc x₀ hs hF hM hn.le]
      refine Measure.compProd_congr ?_
      filter_upwards [hgood n hn.le] with h hh
      exact (hq_mem n h hh).symm
    have hlaw := map_history_eq_chainSeqLaw (μ := srwLaw m x₀)
      (measurable_walkBlockExitPos (vertexPoint ε η) hc.le s hF x₀) (z := vertexPoint ε η x₀)
      (fun _ => rfl) q hκ
    rw [← hlaw]
    refine Measure.map_congr ?_
    filter_upwards [srwLaw_ae_start m x₀] with x hx
    funext i
    rw [blockExitPositions_apply, walkBlockExitPos_eq _ hc.le s _ hx]

/-- **Step laws of the walk's block-exit chain, grid-rectangle form.**
`exists_chain_of_hclose_frozen` with the frozen set the complement of the open grid rectangle
`R`, the start in `R`. -/
theorem exists_chain_of_hclose {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (x₀ : ℤ) {s : ℝ}
    (hs : 0 < s) {a₁ a₂ c₁ c₂ : ℤ} (hz : vertexPoint ε η x₀ ∈ gridRectOpen s a₁ a₂ c₁ c₂)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
        z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hclose : ∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      ProkhorovLE
        (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ (y, u))
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) δ δ)
    (N : ℕ) :
    ∃ q : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ, (∀ n, Measurable (q n)) ∧
      (∀ n g, IsProbabilityMeasure (q n g)) ∧
      (∀ n < N, ∀ g, (g (Fin.last N) = vertexPoint ε η x₀ ∨ g (Fin.last N) ∈ gridLines s) →
        q n g (gridLines s)ᶜ = 0) ∧
      (∀ n < N, ∀ g, ProkhorovLE (q n g)
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) δ δ) ∧
      (srwLaw m x₀).map (fun x => blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N
          (interpPathCM (vertexPoint ε η) hc.le x)) =
        chainSeqLaw (fun n => paddedHistoryKernel n (q n))
          (Measure.dirac fun _ => vertexPoint ε η x₀) N :=
  exists_chain_of_hclose_frozen hlf hcons hε hη hp hc x₀ hs
    (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl (fun h => h hz) hM hδ
    (fun y hy => hclose y (by simpa using hy)) N


/-- **The walk's block-exit chain reaches the complement of a grid rectangle, from the one-step
closeness.** For `0 < ζ < 1` and every `p` there is `C` such that the following holds. Let `m` be a
locally finite multigraph whose consecutive vertices are adjacent, `ε > 0`, `η` a continuous proper
curve, `c > 0` a speed, `R` an open grid rectangle containing the embedded start
`vertexPoint ε η x₀`, with every edge meeting `R` of length at most `s / 2`. Suppose every point of
`R` lies at distance less than `a - 4 s - (N + 1) δ` from the start, and that from every `y ∈ R` and
every vertex `u` within `s / 2` of `y` the next block-exit position of the walk frozen off `R` is
`(δ, δ)`-close to the frozen grid-rectangle block-exit kernel at `y`. Then the probability that the
first `N = ⌊r ^ (-(2 + ζ))⌋` block-exit positions all stay in `R` is at most
`C r ^ p + N δ + 60 N³ δ / s`. -/
theorem srwLaw_blockExit_avoid_frozen_le_of_hclose {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m → (∀ k : ℤ, m k (k + 1) ≠ 0) →
      ∀ (ε : ℝ), 0 < ε → ∀ (η : ℝ → ℂ), Continuous η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ (c : ℝ) (hc : 0 < c) (x₀ : ℤ) (s : ℝ), 0 < s → ∀ (a₁ a₂ c₁ c₂ : ℤ),
      vertexPoint ε η x₀ ∈ gridRectOpen s a₁ a₂ c₁ c₂ →
      (∀ b b' : ℤ, m b b' ≠ 0 →
        (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
          z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ) →
        dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2) →
      ∀ (a r δ : ℝ) (N : ℕ), N = ⌊r ^ (-(2 + ζ))⌋₊ → 0 < N → 0 < a → 0 < r → r < 1 →
      0 < δ → ((N : ℝ) + 1) * δ ≤ s / 4 → 2 * (a * r) ≤ s / 2 - 2 * (((N : ℝ) + 1) * δ) →
      (∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂,
        ‖y - vertexPoint ε η x₀‖ + ((N : ℝ) + 1) * δ < a - 4 * s) →
      (∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
        ProkhorovLE
          (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ
            (y, u))
          (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) δ δ) →
      srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ n
              (interpPathCM (vertexPoint ε η) hc.le x)) ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ} ≤
        ENNReal.ofReal (C * r ^ p) +
          ENNReal.ofReal (N * δ + 60 * (N : ℝ) ^ 3 * δ / s) := by
  obtain ⟨C, hC⟩ := srwLaw_blockExit_avoid_frozen_le_of_chain hζ0 hζ1 p
  refine ⟨C, fun m hlf hcons ε hε η hη hp c hc x₀ s hs a₁ a₂ c₁ c₂ hz hM a r δ N hNr hN ha hr0
    hr1 hδ hδs hac hKz hclose => ?_⟩
  obtain ⟨q, hq, hqP, hqΓ, hqK, hlaw⟩ :=
    exists_chain_of_hclose hlf hcons hε hη hp hc x₀ hs hz hM hδ hclose N
  exact hC m hlf hcons ε hε η hη hp c hc x₀ s hs a₁ a₂ c₁ c₂ _ hz _
    (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl a r δ N hNr hN ha hr0 hr1 hδ hδs hac
    (fun y hy => hKz y (by simpa using hy)) q hq hqP hqΓ hqK hlaw

/-- **Block-exit positions of the walk against planar Brownian motion, frozen-set form.** Freeze
the block-exit chains on a measurable grid-line stable set `F`, start the walk at `x₀` with
`z = vertexPoint ε η x₀ ∉ F`, and assume the one-step closeness `hclose` to the block-exit kernel
frozen on `F`. If `0 < N` and `(N + 1) δ ≤ s / 4`, the law under `srwLaw m x₀` of the first `N + 1`
block-exit positions of the interpolated walk is within `((N + 1) δ, N δ + 60 N³ δ / s)` of the law
of the first `N + 1` block-exit positions of planar Brownian motion started at `z`, in the
one-sided Lévy-Prokhorov sense. -/
theorem prokhorovLE_srwLaw_blockExitPositions_of_hclose_frozen {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (x₀ : ℤ) {s : ℝ} (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hFs : GridLineStable s F) (hz : vertexPoint ε η x₀ ∉ F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hclose : ∀ y ∉ F, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      ProkhorovLE (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s F (y, u))
        (frozenBlockExitKernel s hF y) δ δ)
    {N : ℕ} (hN : 0 < N) (hδs : ((N : ℝ) + 1) * δ ≤ s / 4) :
    ProkhorovLE
      ((srwLaw m x₀).map (fun x => blockExitPositions s F N
        (interpPathCM (vertexPoint ε η) hc.le x)))
      ((planarBrownianMotion (vertexPoint ε η x₀)).map (blockExitPositions s F N))
      (((N : ℝ) + 1) * δ) (N * δ + 60 * (N : ℝ) ^ 3 * δ / s) := by
  obtain ⟨q, hq, hqP, hqΓ, hqK, hlaw⟩ :=
    exists_chain_of_hclose_frozen hlf hcons hε hη hp hc x₀ hs hF hz hM hδ hclose N
  have := hqP
  rw [hlaw, law_blockExitPositions_eq_chainHistoryLaw s hF N (vertexPoint ε η x₀)]
  exact prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable_cubic hs hF hFs hN hz hδ hδs hq
    hqΓ hqK

/-- **Block-exit positions of the walk against planar Brownian motion, from the one-step
closeness.** Freeze the block-exit chains off the open grid rectangle `R`, start the walk at `x₀`
with `z = vertexPoint ε η x₀ ∈ R`, and assume the one-step closeness `hclose`. If `0 < N` and
`(N + 1) δ ≤ s / 4`, the law under `srwLaw m x₀` of the first `N + 1` block-exit positions of the
interpolated walk is within `((N + 1) δ, N δ + 60 N³ δ / s)` of the law of the first `N + 1`
block-exit positions of planar Brownian motion started at `z`, in the one-sided Lévy-Prokhorov
sense. -/
theorem prokhorovLE_srwLaw_blockExitPositions_of_hclose {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (x₀ : ℤ) {s : ℝ} (hs : 0 < s) {a₁ a₂ c₁ c₂ : ℤ}
    (hz : vertexPoint ε η x₀ ∈ gridRectOpen s a₁ a₂ c₁ c₂)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
        z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hclose : ∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
      ProkhorovLE
        (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ (y, u))
        (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) δ δ)
    {N : ℕ} (hN : 0 < N) (hδs : ((N : ℝ) + 1) * δ ≤ s / 4) :
    ProkhorovLE
      ((srwLaw m x₀).map (fun x => blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N
        (interpPathCM (vertexPoint ε η) hc.le x)))
      ((planarBrownianMotion (vertexPoint ε η x₀)).map
        (blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N))
      (((N : ℝ) + 1) * δ) (N * δ + 60 * (N : ℝ) ^ 3 * δ / s) :=
  prokhorovLE_srwLaw_blockExitPositions_of_hclose_frozen hlf hcons hε hη hp hc x₀ hs
    (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl
    (gridLineStable_compl_gridRectOpen hs a₁ a₂ c₁ c₂)
    (fun h => h hz) hM hδ (fun y hy => hclose y (by simpa using hy)) hN hδs

end BlockExit

end MatedCRT
