import MatedCRT.Proofs.Sec1.EnvironmentScaling.PostLastZeroShiftedLaw
import MatedCRT.Proposed.DMSRemark44Printed

/-!
# Conditioned weak limit of the positive-level shifted law on the canonical Wiener space

Canonical-space component of DMS Remark 4.4 (Duplantier–Miller–Sheffield, arXiv:1409.7055v4, pp. 74–75), in the form of
`steps4-r2.tex` Section 2, lines 408–427 ("the coupling and its limit"). The space is the canonical Wiener space
`W = MarkovProcess.brownianMotion 0` on `ContinuousPath ℝ = C(ℝ≥0, ℝ)` with the compact-open topology. For a drift `d`
and a path `y` that is strictly positive at every positive real time, with first hit `τ_δ = dmsFirstLevelHit δ y` of
the level `δ`:

1. `tendstoUniformlyOn_affinePath_shift_firstLevelHit`: the drift-corrected shifted paths
   `t ↦ y(τ_δ + t) - δ - d t` converge uniformly on every compact time interval `[0, T]` as `δ ↓ 0`. The first hits
   tend to `0` (`tendsto_dmsFirstLevelHit`), and `y` is uniformly continuous on `[0, T + 1]`.
2. `tendsto_affinePath_shift_firstLevelHit_compactOpen`: hence convergence in the compact-open topology.
3. `canonical_isBMConditionedPositive_of_printed`: for a measurable `F` on `W` with the printed DMS clauses
   `DMS14Remark44PositiveRealization` and `DMS14Remark44PositiveLevelLaw` (explicit premises, for `P = W` and drift `d`),
   the undrifted post-last-zero path `G = F - d·` satisfies `IsBMConditionedPositive d (W.map G)`. The proof combines the
   conditional-law identity `W.map (shifted path) = W[· | stayAboveEvent d δ]` (`map_cond_driftedBrownianFrom`), bounded
   continuous dominated convergence along each sequence `δ_n ↓ 0`, and the sequential criterion `tendsto_iff_seq_tendsto`
   for the real limit along `𝓝[>] 0`.

Not used: the numbered target `DMS14Remark44PostLastZeroLaw` (no circular use), and the arbitrary-space transfer from
`ProbabilityTheory.IsBrownianReal`, which remains the residual `DMS14Remark44TransferResidual`
(`MatedCRT/Proposed/DMSRemark44Printed.lean`) for a separate successor. Nothing here is a closure of a numbered result.

Credits: `ContinuousPath.shift`, `exitTime`, `brownianMotion` and the conditioned Wiener laws are from Scott Armstrong's
`MarkovProcess` library. The drifted post-last-zero path and the printed clauses live in `MatedCRT.Proposed.DMSRemark44Printed`,
which imports Leonardo Bonanno's `LatticeProb.Bonanno.MatedCRTHarmonic` modules (`lqgQ`, `lastZeroR`, used by its
`DMS14Remark44PrintedWiener` clause). This file uses no Bonanno declaration directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

open MatedCRT.Proposed

/-! ### Uniform convergence on compact time intervals -/

/-- **Uniform convergence on each compact time interval** (steps4-r2 lines 408–418). Let `y` be a continuous path with
`0 < y η` for every real time `η > 0` (all-real-time strict positivity of the post-last-zero path). For a drift `d` and
`T : ℝ≥0`, the drift-corrected shifted paths `t ↦ y(τ_δ + t) - δ - d t`, with `τ_δ = dmsFirstLevelHit δ y` the first hit of
`δ`, converge uniformly on `[0, T]` to `t ↦ y t - d t` as `δ ↓ 0`. The difference is `δ - (y(τ_δ + t) - y t)`, which is
small because `τ_δ → 0` and `y` is uniformly continuous on `[0, T + 1]`. -/
theorem tendstoUniformlyOn_affinePath_shift_firstLevelHit (d : ℝ) (y : ContinuousPath ℝ)
    (hy : ∀ η : ℝ≥0, 0 < η → 0 < y η) (T : ℝ≥0) :
    TendstoUniformlyOn (fun δ : ℝ => ⇑(affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ y) y)))
      ⇑(affinePath 0 (-d) y) (𝓝[>] 0) (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- uniform continuity of `y` on the compact interval `[0, T + 1]`
  have hUC : UniformContinuousOn (fun t : ℝ≥0 => y t) (Icc (0 : ℝ≥0) (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous y.continuous.continuousOn
  obtain ⟨η, hη, hηy⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 2) (half_pos hε)
  -- first hits below `min η 1` and shifts below `ε / 2`, eventually along `𝓝[>] 0`
  have hc : (0 : ℝ≥0) < (min η 1).toNNReal := Real.toNNReal_pos.2 (lt_min hη zero_lt_one)
  have hτ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), dmsFirstLevelHit δ y < (min η 1).toNNReal :=
    (tendsto_order.1 (tendsto_dmsFirstLevelHit y hy)).2 _ hc
  have hδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ε / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (half_pos hε))
  filter_upwards [hτ, hδ, self_mem_nhdsWithin] with δ hτδ hδε hδpos
  have hδ0 : (0 : ℝ) < δ := hδpos
  intro t ht
  have hτ1 : (dmsFirstLevelHit δ y : ℝ) < min η 1 := by
    have h : (dmsFirstLevelHit δ y : ℝ) < ((min η 1).toNNReal : ℝ) := NNReal.coe_lt_coe.2 hτδ
    rwa [Real.coe_toNNReal _ (le_min hη.le zero_le_one)] at h
  have hτη : (dmsFirstLevelHit δ y : ℝ) < η := lt_of_lt_of_le hτ1 (min_le_left _ _)
  have hτle : dmsFirstLevelHit δ y ≤ 1 := by
    have h : (dmsFirstLevelHit δ y : ℝ) ≤ 1 := (lt_of_lt_of_le hτ1 (min_le_right _ _)).le
    exact_mod_cast h
  -- the times `τ_δ + t` and `t` lie in `[0, T + 1]` and are `η`-close
  have hmemK1 : dmsFirstLevelHit δ y + t ∈ Icc (0 : ℝ≥0) (T + 1) := by
    refine ⟨zero_le, ?_⟩
    calc dmsFirstLevelHit δ y + t ≤ 1 + T := add_le_add hτle ht.2
      _ = T + 1 := add_comm _ _
  have hmemK2 : t ∈ Icc (0 : ℝ≥0) (T + 1) := ⟨zero_le, le_trans ht.2 le_self_add⟩
  have hdist : dist (dmsFirstLevelHit δ y + t) t < η := by
    rw [NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_right, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact hτη
  have h1 : |y (dmsFirstLevelHit δ y + t) - y t| < ε / 2 := by
    have h : dist (y (dmsFirstLevelHit δ y + t)) (y t) < ε / 2 := hηy _ hmemK1 _ hmemK2 hdist
    rwa [Real.dist_eq] at h
  obtain ⟨h1a, h1b⟩ := abs_lt.1 h1
  simp only [affinePath, ContinuousMap.coe_mk, ContinuousPath.shift_apply]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Convergence in the compact-open topology -/

/-- **Compact-open convergence** (steps4-r2 lines 415–418). Uniform convergence on each compact time interval
(`tendstoUniformlyOn_affinePath_shift_firstLevelHit`) gives convergence in the compact-open topology of
`ContinuousPath ℝ`, because every compact subset of `ℝ≥0` lies in some `[0, T]`. -/
theorem tendsto_affinePath_shift_firstLevelHit_compactOpen (d : ℝ) (y : ContinuousPath ℝ)
    (hy : ∀ η : ℝ≥0, 0 < η → 0 < y η) :
    Tendsto (fun δ : ℝ => affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ y) y))
      (𝓝[>] 0) (𝓝 (affinePath 0 (-d) y)) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  exact (tendstoUniformlyOn_affinePath_shift_firstLevelHit d y hy T).mono
    fun t ht => ⟨zero_le, hT ht⟩

/-! ### The canonical conditioned weak limit -/

/-- **Full positive-real conditioning limit on the canonical Wiener space** (steps4-r2 lines 388–427; the target
predicate is `IsBMConditionedPositive`, `MatedCRT/Defs/QuantumCone.lean`).

Let `W = brownianMotion 0`, let `d` be a real drift (the positive-real drift `Q - γ` of DMS Remark 4.4, with `0 < d`), and let
`F : ContinuousPath ℝ → ContinuousPath ℝ` be measurable with the two printed clauses for `W` and `d` as explicit premises:
`hreal` (`W`-almost surely `F ω 0 = 0` and `F ω t > 0` at every real `t > 0`) and `hlaw` (for every `δ > 0`, the `W`-law of the
path shifted after its first hit `τ_δ` of `δ` is the conditioned drifted Brownian law `W[· | stayAboveEvent d δ]`).

Then the undrifted post-last-zero path `G = F - d·` satisfies `IsBMConditionedPositive d (W.map G)`: `W.map G` is a
probability measure, and `∫ f dW[· | stayAboveEvent d δ] → ∫ f d(W.map G)` as `δ ↓ 0` along the full filter `𝓝[>] 0`, for every
bounded continuous `f` on `ContinuousPath ℝ`.

Proof. For `δ > 0`, the conditional-law identity `W.map (shifted path) = W[· | stayAboveEvent d δ]` follows from `hlaw` and
`map_cond_driftedBrownianFrom`. For each sequence `δ_n ↓ 0`, the shifted paths converge pathwise in the compact-open topology
(`tendsto_affinePath_shift_firstLevelHit_compactOpen`), so `f` of them converges `W`-almost surely, and dominated convergence
with bound `‖f‖` applies. The sequential criterion `tendsto_iff_seq_tendsto` then gives the full limit.

It uses no `DMS14Remark44PostLastZeroLaw` and no arbitrary-space transfer, and is not a closure of any numbered result. -/
theorem canonical_isBMConditionedPositive_of_printed {d : ℝ} (_hd : 0 < d)
    (F : ContinuousPath ℝ → ContinuousPath ℝ) (hF : Measurable F)
    (hreal : DMS14Remark44PositiveRealization (MarkovProcess.brownianMotion 0) F)
    (hlaw : DMS14Remark44PositiveLevelLaw (MarkovProcess.brownianMotion 0) d F) :
    MatedCRT.IsBMConditionedPositive d
      ((MarkovProcess.brownianMotion 0).map (fun ω => affinePath 0 (-d) (F ω))) := by
  have hG : Measurable (fun ω => affinePath 0 (-d) (F ω)) :=
    (measurable_affinePath 0 (-d)).comp hF
  have hZ : ∀ δ : ℝ, Measurable (fun ω => affinePath (-δ) (-d)
      (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω))) :=
    fun δ => (measurable_affinePath (-δ) (-d)).comp (measurable_shift_dmsFirstLevelHit δ hF)
  -- the checked conditional-law coupling at each level `δ > 0`
  have hlawZ : ∀ δ : ℝ, 0 < δ → (MarkovProcess.brownianMotion 0).map (fun ω => affinePath (-δ) (-d)
      (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω)))
      = ProbabilityTheory.cond (MarkovProcess.brownianMotion 0) (MatedCRT.stayAboveEvent d δ) := by
    intro δ hδ
    calc (MarkovProcess.brownianMotion 0).map (fun ω => affinePath (-δ) (-d)
            (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω)))
        = Measure.map (affinePath (-δ) (-d))
            (Measure.map (fun ω => ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω))
              (MarkovProcess.brownianMotion 0)) :=
          (Measure.map_map (measurable_affinePath (-δ) (-d))
            (measurable_shift_dmsFirstLevelHit δ hF)).symm
      _ = ProbabilityTheory.cond (MarkovProcess.brownianMotion 0) (MatedCRT.stayAboveEvent d δ) := by
          rw [hlaw δ hδ]
          exact map_cond_driftedBrownianFrom d δ hδ
  have hreal' : ∀ᵐ ω ∂(MarkovProcess.brownianMotion 0), ∀ η : ℝ≥0, 0 < η → 0 < F ω η :=
    hreal.mono fun ω hω => hω.2
  have hprob : IsProbabilityMeasure
      ((MarkovProcess.brownianMotion 0).map (fun ω => affinePath 0 (-d) (F ω))) :=
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
  refine ⟨hprob, fun f => ?_⟩
  rw [integral_map hG.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  -- sequential criterion: it suffices to take the limit along every sequence `δ_n → 0⁺`
  refine tendsto_iff_seq_tendsto.2 fun s hs => ?_
  have hev : ∀ᶠ n in atTop, (0 : ℝ) < s n := hs.eventually self_mem_nhdsWithin
  -- bounded continuous dominated convergence along the sequence
  have hdct : Tendsto (fun n => ∫ ω, f (affinePath (-(s n)) (-d)
      (ContinuousPath.shift (dmsFirstLevelHit (s n) (F ω)) (F ω))) ∂(MarkovProcess.brownianMotion 0))
      atTop (𝓝 (∫ ω, f (affinePath 0 (-d) (F ω)) ∂(MarkovProcess.brownianMotion 0))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun n => ?_) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _) ?_
    · exact (f.continuous.measurable.comp (hZ (s n))).aestronglyMeasurable
    · filter_upwards [hreal'] with ω hω
      exact (f.continuous.tendsto _).comp
        ((tendsto_affinePath_shift_firstLevelHit_compactOpen d (F ω) hω).comp hs)
  refine hdct.congr' ?_
  filter_upwards [hev] with n hn
  simp only [Function.comp_apply]
  rw [← hlawZ (s n) hn, integral_map (hZ (s n)).aemeasurable f.continuous.measurable.aestronglyMeasurable]

end MatedCRT.Sec1
