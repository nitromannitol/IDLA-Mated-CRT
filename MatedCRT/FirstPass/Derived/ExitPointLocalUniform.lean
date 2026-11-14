import MatedCRT.FirstPass.Derived.BrownianRegularExitSquare

/-!
# Continuity of the exit point at a regular exit, for locally uniform convergence

Let `U ⊆ ℂ` be open and let `f` be a continuous path which leaves `U` at a finite time `τ` and exits regularly (it
visits the complement of `closure U` at times arbitrarily close to `τ` from above). If paths `g i` converge to `f`
uniformly on every bounded time interval `[0, T]`, then

* the exit times converge, `pathExitTime U (g i) → τ` (only the paths on a bounded interval `[0, s]` with `s > τ`
  matter: before `τ` the compact arc `f([0, s'])` has a neighbourhood inside `U`, just after `τ` the path is at
  positive distance from `closure U`);
* the exit points converge, `g i (τ_U (g i)) → f τ`.

Locally uniform convergence is convergence in the compact-open topology of `C([0, ∞), ℂ)`, the topology of the
weak convergence of random-walk paths to Brownian motion (Gwynne–Miller–Sheffield, *An invariance principle for
ergodic scale-free random environments*, arXiv 1807.07515, Theorem 1.16). Hence the exit-point map is continuous at
every path with a regular finite exit, and in particular at almost every planar Brownian path started in an open
square (`BrownianRegularExitSquare.lean`). This is the continuity input of condition 1 in the proof of Lemma 3.14 of
the same paper: the law of the exit point of the rescaled walk from a square converges to the harmonic measure of
the square.

## Main statements

* `MatedCRT.StopAtExitCmp.tendsto_pathExitTime_of_locallyUniform`
* `MatedCRT.StopAtExitCmp.tendsto_exitPoint_of_locallyUniform`
* `MatedCRT.StopAtExitCmp.continuousAt_exitPoint`: continuity in the compact-open topology.
* `MatedCRT.StopAtExitCmp.ae_continuousAt_exitPoint_openSquare_planarBrownian`
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

variable {ι : Type*} {l : Filter ι}

/-- The exit point `f(τ_U(f))` of the path `f` from `U` (the value at time `0` if the path never leaves `U`,
since `(⊤ : ℝ≥0∞).toNNReal = 0`). -/
noncomputable def exitPoint (U : Set ℂ) (f : ℝ≥0 → ℂ) : ℂ :=
  f (pathExitTime U f).toNNReal

/-- **Continuity of the exit time at a regular exit, for locally uniform convergence.** -/
theorem tendsto_pathExitTime_of_locallyUniform {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U)
    {g : ι → ℝ≥0 → ℂ}
    (hg : ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ t ≤ T, dist (g i t) (f t) < ε) :
    Tendsto (fun i => pathExitTime U (g i)) l (𝓝 (pathExitTime U f)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨s, has, hsτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hK : IsCompact (f '' Icc 0 s) := isCompact_Icc.image hf
    have hKU : f '' Icc 0 s ⊆ U := by
      rintro _ ⟨t, ht, rfl⟩
      exact mem_of_lt_exitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hsτ)
    obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
    filter_upwards [hg s δ hδ] with i hi
    refine lt_of_lt_of_le has (le_exitTime_of_forall_le_mem fun t ht => hthick ?_)
    exact mem_thickening_iff.2 ⟨f t, ⟨t, ⟨by positivity, ht⟩, rfl⟩, hi t ht⟩
  · have hτa : ((pathExitTime U f).toNNReal : ℝ≥0∞) < a := by rwa [ENNReal.coe_toNNReal hfin]
    obtain ⟨s, hτs, hsa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτa
    have hτs' : (pathExitTime U f).toNNReal < s := ENNReal.coe_lt_coe.1 hτs
    obtain ⟨t₀, ht₀f, ht₀I⟩ := (hreg.and_eventually (Ioo_mem_nhdsGT hτs')).exists
    have hopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (f t₀) ht₀f
    filter_upwards [hg s ε hε] with i hi
    have hout : g i t₀ ∉ U := fun hmem =>
      hball (mem_ball.2 (hi t₀ ht₀I.2.le)) (subset_closure hmem)
    exact lt_of_le_of_lt (exitTime_le_of_not_mem hout)
      (lt_trans (ENNReal.coe_lt_coe.2 ht₀I.2) hsa)

/-- **Continuity of the exit point at a regular exit, for locally uniform convergence.** -/
theorem tendsto_exitPoint_of_locallyUniform {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U)
    {g : ι → ℝ≥0 → ℂ}
    (hg : ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ t ≤ T, dist (g i t) (f t) < ε) :
    Tendsto (fun i => exitPoint U (g i)) l (𝓝 (exitPoint U f)) := by
  set τ := (pathExitTime U f).toNNReal with hτ
  show Tendsto (fun i => g i (pathExitTime U (g i)).toNNReal) l (𝓝 (f τ))
  have hT : Tendsto (fun i => (pathExitTime U (g i)).toNNReal) l (𝓝 τ) :=
    (ENNReal.tendsto_toNNReal hfin).comp (tendsto_pathExitTime_of_locallyUniform hU hf hfin hreg hg)
  have hfT : Tendsto (fun i => f (pathExitTime U (g i)).toNNReal) l (𝓝 (f τ)) :=
    (hf.tendsto τ).comp hT
  rw [Metric.tendsto_nhds] at hfT ⊢
  intro ε hε
  have hle : ∀ᶠ i in l, (pathExitTime U (g i)).toNNReal ≤ τ + 1 :=
    hT.eventually (eventually_le_nhds (lt_add_one τ))
  filter_upwards [hfT (ε / 2) (half_pos hε), hle, hg (τ + 1) (ε / 2) (half_pos hε)] with i h1 h2 h3
  calc dist (g i (pathExitTime U (g i)).toNNReal) (f τ)
      ≤ dist (g i (pathExitTime U (g i)).toNNReal) (f (pathExitTime U (g i)).toNNReal) +
        dist (f (pathExitTime U (g i)).toNNReal) (f τ) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h3 _ h2) h1
    _ = ε := add_halves ε

/-- **The exit-point map is continuous at a regular finite exit** in the compact-open topology of
`ContinuousPath ℂ = C([0, ∞), ℂ)` (locally uniform convergence). -/
theorem continuousAt_exitPoint {U : Set ℂ} (hU : IsOpen U) {f : ContinuousPath ℂ}
    (hfin : pathExitTime U ⇑f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U ⇑f).toNNReal, f t ∉ closure U) :
    ContinuousAt (fun g : ContinuousPath ℂ => exitPoint U ⇑g) f := by
  refine tendsto_exitPoint_of_locallyUniform (l := 𝓝 f) (g := fun g : ContinuousPath ℂ => ⇑g) hU f.continuous
    hfin hreg fun T ε hε => ?_
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (id : ContinuousPath ℂ → ContinuousPath ℂ) (𝓝 f) (𝓝 f)) (Icc 0 T) isCompact_Icc
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu ε hε] with g hg t ht
  rw [dist_comm]
  exact hg t ⟨zero_le, ht⟩

/-- For a bounded open set with a measurable exterior normal field, the exit-point map is continuous (compact-open
topology) at almost every planar Brownian path started in the set. -/
theorem ae_continuousAt_exitPoint_planarBrownian_of_exteriorNormal {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {v : ℂ → ℂ} (hv : Measurable v)
    (hvU : ∀ p ∈ frontier U, v p ≠ 0 ∧ ∀ q : ℂ, 0 < inner ℝ (v p) (q - p) → q ∉ closure U)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      ContinuousAt (fun g : ContinuousPath ℂ => exitPoint U ⇑g) b := by
  filter_upwards [ae_regularExit_planarBrownian_of_exteriorNormal hU hUb hv hvU hx] with b hb
  exact continuousAt_exitPoint hU hb.1 (hb.2.resolve_left hb.1)

/-- **Exit point from a square.** The exit-point map from an open axis-parallel square is continuous (compact-open
topology) at almost every planar Brownian path started in the square. -/
theorem ae_continuousAt_exitPoint_openSquare_planarBrownian {c x : ℂ} {a : ℝ}
    (hx : x ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      ContinuousAt
        (fun g : ContinuousPath ℂ => exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⇑g) b := by
  filter_upwards [ae_regularExit_openSquare_planarBrownian hx] with b hb
  exact continuousAt_exitPoint (isOpen_openSquare c a) hb.1 (hb.2.resolve_left hb.1)

end MatedCRT.StopAtExitCmp

/-! ## Audit -/

#print axioms MatedCRT.StopAtExitCmp.tendsto_exitPoint_of_locallyUniform
#print axioms MatedCRT.StopAtExitCmp.continuousAt_exitPoint
#print axioms MatedCRT.StopAtExitCmp.ae_continuousAt_exitPoint_planarBrownian_of_exteriorNormal
#print axioms MatedCRT.StopAtExitCmp.ae_continuousAt_exitPoint_openSquare_planarBrownian
