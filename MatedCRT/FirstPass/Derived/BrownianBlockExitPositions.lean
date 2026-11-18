import MatedCRT.FirstPass.Derived.BrownianBlockExitChain
import MatedCRT.FirstPass.Derived.BrownianExitPointRestart
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-!
# Successive block-exit positions of planar Brownian motion

The Brownian side of the chaining step in the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield
invariance principle. For a mesh `s > 0` and a frozen set `F`, the first block-exit time of a path
`ω` is `0` if `ω 0 ∈ F`, and otherwise the exit time of the open block of side `3 s` around the
grid cell of `ω 0` (`firstBlockExitTime`). Iterating it on the shifted path gives the stopping
times `σ₀ = 0 < σ₁ ≤ σ₂ ≤ …` of the successive block exits, frozen once the path has entered `F`,
and `blockExitPositions s F N ω = (ω σ₀, …, ω σ_N)` is defined by the first-step recursion
`(ω 0, blockExitPositions s F N (θ_{σ₁} ω))`.

The strong Markov property of planar Brownian motion at the single stopping time `σ₁` (with the
starting point fixed, `σ₁` is the exit time of one fixed block) gives the first-step recursion of
the joint law of the positions:
`P_z ∘ (pos_{N+1})⁻¹ = ((κ z).bind fun x => P_x ∘ (pos_N)⁻¹).map (Fin.cons z)`,
where `κ = frozenBlockExitKernel s hF` is the block-exit kernel frozen on `F`. Together with the
first-step decomposition of the history law of a Markov kernel, this identifies the joint law of
the positions with the history law of the chain of `κ`.

* `firstBlockExitTime`, `measurable_firstBlockExitTime`.
* `blockExitPositions`, `measurable_blockExitPositions`.
* `map_blockExitPositions_zero`, `map_blockExitPositions_succ`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT
namespace BlockExit

/-- The image of a mixture is the mixture of the images. -/
private theorem map_bind_eq_bind_map' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {K : α → Measure β} (hK : Measurable K) {f : β → γ}
    (hf : Measurable f) : (μ.bind K).map f = μ.bind fun x => (K x).map f := by
  have hm : Measurable fun x => (K x).map f := (Measure.measurable_map f hf).comp hK
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) hK.aemeasurable,
    Measure.bind_apply hs hm.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply hf hs]

/-- A mixture over an image law is the mixture of the composed kernel. -/
private theorem bind_map_eq_bind_comp' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {f : α → β} (hf : Measurable f) {K : β → Measure γ}
    (hK : Measurable K) : (μ.map f).bind K = μ.bind fun x => K (f x) := by
  have hm : Measurable fun x => K (f x) := hK.comp hf
  ext s hs
  have hKs : Measurable fun y => K y s := (Measure.measurable_coe hs).comp hK
  rw [Measure.bind_apply hs hK.aemeasurable, Measure.bind_apply hs hm.aemeasurable,
    lintegral_map hKs hf]

theorem measurable_eval_zero : Measurable fun ω : ContinuousPath ℂ => ω 0 :=
  ContinuousPath.measurable_eval_of_measurable (fun _ => 0) measurable_const

/-- The exit time from the block with index `p.2` of the path `p.1` (read as `0` if infinite). -/
noncomputable def blockExitTimeAt (s : ℝ) (p : ContinuousPath ℂ × (ℤ × ℤ)) : ℝ≥0 :=
  (ContinuousPath.exitTime (openBlock s p.2.1 p.2.2) p.1).untopD 0

theorem measurable_blockExitTimeAt (s : ℝ) : Measurable (blockExitTimeAt s) := by
  refine measurable_from_prod_countable_left fun c => ?_
  have h := (ContinuousPath.measurable_exitTime _ (isOpen_openBlock s c.1 c.2)).ennreal_toNNReal
  exact h

/-- The first block-exit time: `0` on the frozen set `F`, otherwise the exit time of the open
block of side `3 s` around the grid cell of the starting point (read as `0` if infinite). -/
noncomputable def firstBlockExitTime (s : ℝ) (F : Set ℂ) (ω : ContinuousPath ℂ) : ℝ≥0 :=
  open Classical in
  if ω 0 ∈ F then 0 else blockExitTimeAt s (ω, cellIndex s (ω 0))

theorem measurable_prod_cellIndex_eval_zero (s : ℝ) :
    Measurable fun ω : ContinuousPath ℂ => (ω, cellIndex s (ω 0)) :=
  measurable_id.prodMk ((measurable_cellIndex s).comp measurable_eval_zero)

theorem measurable_firstBlockExitTime (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) :
    Measurable (firstBlockExitTime s F) := by
  have hS : MeasurableSet {ω : ContinuousPath ℂ | ω 0 ∈ F} := measurable_eval_zero hF
  have hgc : Measurable fun ω : ContinuousPath ℂ => blockExitTimeAt s (ω, cellIndex s (ω 0)) :=
    (measurable_blockExitTimeAt s).comp (measurable_prod_cellIndex_eval_zero s)
  unfold firstBlockExitTime
  exact Measurable.ite hS measurable_const hgc

/-- The positions `(ω σ₀, …, ω σ_N)` of a path at its successive block-exit times, frozen once
the path is in `F`, by the first-step recursion. -/
noncomputable def blockExitPositions (s : ℝ) (F : Set ℂ) :
    (N : ℕ) → ContinuousPath ℂ → Fin (N + 1) → ℂ
  | 0, ω => fun _ => ω 0
  | N + 1, ω => Fin.cons (ω 0)
      (blockExitPositions s F N (ContinuousPath.shift (firstBlockExitTime s F ω) ω))

theorem blockExitPositions_zero (s : ℝ) (F : Set ℂ) (ω : ContinuousPath ℂ) :
    blockExitPositions s F 0 ω = fun _ => ω 0 :=
  rfl

theorem blockExitPositions_succ (s : ℝ) (F : Set ℂ) (N : ℕ) (ω : ContinuousPath ℂ) :
    blockExitPositions s F (N + 1) ω = Fin.cons (ω 0)
      (blockExitPositions s F N (ContinuousPath.shift (firstBlockExitTime s F ω) ω)) :=
  rfl

theorem measurable_blockExitPositions (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (N : ℕ) :
    Measurable (blockExitPositions s F N) := by
  induction N with
  | zero => exact measurable_pi_iff.2 fun _ => measurable_eval_zero
  | succ N ih =>
    have hsh : Measurable fun ω : ContinuousPath ℂ =>
        ContinuousPath.shift (firstBlockExitTime s F ω) ω :=
      ContinuousPath.measurable_shift_of_measurable _ (measurable_firstBlockExitTime s hF)
    refine measurable_pi_iff.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [blockExitPositions_succ, Fin.cons_zero]
      exact measurable_eval_zero
    · simp only [blockExitPositions_succ, Fin.cons_succ]
      exact (measurable_pi_apply j).comp (ih.comp hsh)

theorem measurable_finCons (z : ℂ) (N : ℕ) :
    Measurable fun g : Fin (N + 1) → ℂ => (Fin.cons z g : Fin (N + 1 + 1) → ℂ) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

/-- At time `0` the positions are the starting point. -/
theorem map_blockExitPositions_zero (s : ℝ) (F : Set ℂ) (z : ℂ) :
    (planarBrownianMotion z).map (blockExitPositions s F 0) = Measure.dirac fun _ => z := by
  have hae : blockExitPositions s F 0 =ᵐ[planarBrownianMotion z] fun _ => fun _ => z := by
    filter_upwards [ae_planarBrownianMotion_eval_zero z] with ω h0
    funext i
    exact h0
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]

/-- **First-step recursion of the joint law of the block-exit positions** (strong Markov property
at the first block exit). -/
theorem map_blockExitPositions_succ (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (N : ℕ) (z : ℂ) :
    (planarBrownianMotion z).map (blockExitPositions s F (N + 1)) =
      ((frozenBlockExitKernel s hF z).bind fun x =>
        (planarBrownianMotion x).map (blockExitPositions s F N)).map
        (fun g : Fin (N + 1) → ℂ => (Fin.cons z g : Fin (N + 1 + 1) → ℂ)) := by
  have hpos := measurable_blockExitPositions s hF N
  have hcons := measurable_finCons z N
  have hPm : Measurable fun x => (planarBrownianMotion x).map (blockExitPositions s F N) :=
    (Measure.measurable_map _ hpos).comp planarBrownianMotion.measurable
  by_cases hz : z ∈ F
  · have hae : ∀ᵐ ω ∂planarBrownianMotion z, blockExitPositions s F (N + 1) ω =
        (Fin.cons z (blockExitPositions s F N ω) : Fin (N + 1 + 1) → ℂ) := by
      filter_upwards [ae_planarBrownianMotion_eval_zero z] with ω h0
      simp only [blockExitPositions_succ, firstBlockExitTime, h0, hz, ↓reduceIte,
        ContinuousPath.shift_zero]
    rw [Measure.map_congr hae, frozenBlockExitKernel_of_mem s hF hz, Measure.dirac_bind hPm,
      Measure.map_map hcons hpos]
    rfl
  · let τ : ContinuousPath ℂ → ℝ≥0∞ :=
      ContinuousPath.exitTime (openBlock s (cellIndex s z).1 (cellIndex s z).2)
    have hU : IsOpen (openBlock s (cellIndex s z).1 (cellIndex s z).2) := isOpen_openBlock _ _ _
    have hτ := ContinuousPath.isStoppingTime_exitTime _ hU
    have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
    have hev := ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ
    have hfin : ∀ᵐ ω ∂(planarBrownianMotion z), τ ω < ⊤ :=
      ae_planarBrownian_exitTime_bounded_lt_top z (isBounded_openBlock _ _ _)
    have hae : ∀ᵐ ω ∂planarBrownianMotion z, blockExitPositions s F (N + 1) ω =
        (Fin.cons z (blockExitPositions s F N
          (ContinuousPath.shift ((τ ω).untopD 0) ω)) : Fin (N + 1 + 1) → ℂ) := by
      filter_upwards [ae_planarBrownianMotion_eval_zero z] with ω h0
      simp only [blockExitPositions_succ, firstBlockExitTime, blockExitTimeAt, h0, hz, ↓reduceIte]
      rfl
    have hrestart :=
      SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
        z τ hτ univ (by simp)
    rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
    simp only [univ_inter] at hrestart
    have hre : (planarBrownianMotion z).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} =
        planarBrownianMotion z :=
      Measure.restrict_eq_self_of_ae_mem hfin
    change ((planarBrownianMotion z).restrict {ω | τ ω < ⊤}).map
        (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
      Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
          ((planarBrownianMotion z).restrict {ω | τ ω < ⊤}) at hrestart
    rw [hre] at hrestart
    have hexit : (planarBrownianMotion z).map (fun ω => ω ((τ ω).untopD 0)) =
        frozenBlockExitKernel s hF z := by
      rw [frozenBlockExitKernel_of_notMem s hF hz, cellBlockExitKernel_apply,
        blockExitKernel_apply]
      rfl
    have hmix : (planarBrownianMotion z).map
        (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
        (frozenBlockExitKernel s hF z).bind planarBrownianMotion := by
      rw [hrestart, ← hexit, bind_map_eq_bind_comp' hev planarBrownianMotion.measurable]
      rfl
    rw [Measure.map_congr hae, ← map_bind_eq_bind_map' planarBrownianMotion.measurable hpos,
      ← hmix, Measure.map_map hpos hshift, Measure.map_map hcons (hpos.comp hshift)]
    rfl

end BlockExit
end MatedCRT
