import MatedCRT.FirstPass.Derived.BlockExitWalkAttained
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The block-exit history of the interpolated walk as a one-step composition-product

For the linear interpolation of the simple random walk, let `H_n` be its block-exit position
history `(Y_0, …, Y_n)`, `Y_{n+1}` its next block-exit position, `τ_n` the step index just after
its `n`-th block exit and `U_n = x_{τ_n}` the walk position at that step. Then the joint law of
`(H_n, Y_{n+1})` is the composition-product of the law of `H_n` with the Markov kernel
`κ_n g = ∫ (P^u ∘ walkNextBlockExit (g_n)⁻¹) d(condDistrib U_n H_n)(g)`:
the next block-exit position is that of the walk restarted from `U_n`, where `U_n` is drawn from
its regular conditional distribution given the history.

## Main definitions

* `srwPathKernel m`: the simple random walk path law `u ↦ P^u` as a Markov kernel.
* `walkNextBlockExitKernel m v hc s F`: `(y, u) ↦ P^u ∘ (walkNextBlockExit y)⁻¹`.
* `walkBlockExitHistory`, `walkBlockExitStepPos`: `H_n` and `U_n` as functions of the walk.
* `walkBlockExitStepKernel m a v hc s F n`: the kernel `κ_n` from histories to positions.

## Main results

* `measurable_walkBlockExitStepPos`: `U_n` is measurable.
* `map_walkBlockExitHistory_next_eq_compProd`: `P^a ∘ (H_n, Y_{n+1})⁻¹ = (P^a ∘ H_n⁻¹) ⊗ κ_n`
  when edges meeting the unfrozen region are short and `τ_n` is almost surely finite.
* `map_walkBlockExitHistory_next_eq_compProd_of_proper`: the same for the walk embedded by a
  continuous proper curve, with the finiteness of `τ_n` proved.
-/

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- The simple random walk path law `u ↦ P^u` as a kernel from the starting vertex. -/
noncomputable def srwPathKernel (m : ℤ → ℤ → ℕ) : Kernel ℤ (ℕ → ℤ) :=
  ⟨fun u => srwLaw m u, measurable_of_countable _⟩

theorem srwPathKernel_apply (m : ℤ → ℤ → ℕ) (u : ℤ) : srwPathKernel m u = srwLaw m u := rfl

instance (m : ℤ → ℤ → ℕ) : IsMarkovKernel (srwPathKernel m) :=
  ⟨fun u => (inferInstance : IsProbabilityMeasure (srwLaw m u))⟩

/-- The law of the next block-exit position from the current position `y` for the walk restarted
at the vertex `u`: `(y, u) ↦ P^u ∘ (walkNextBlockExit y)⁻¹`. -/
noncomputable def walkNextBlockExitKernel (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (s : ℝ) (F : Set ℂ) : Kernel (ℂ × ℤ) ℂ :=
  (Kernel.deterministic Prod.fst measurable_fst ×ₖ
      (srwPathKernel m).comap Prod.snd measurable_snd).map
    (fun q : ℂ × (ℕ → ℤ) => walkNextBlockExit v hc s F q.1 q.2)

theorem isMarkovKernel_walkNextBlockExitKernel (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) :
    IsMarkovKernel (walkNextBlockExitKernel m v hc s F) :=
  Kernel.IsMarkovKernel.map _ (measurable_walkNextBlockExit v hc s hF)

theorem walkNextBlockExitKernel_apply (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (y : ℂ) (u : ℤ) {A : Set ℂ}
    (hA : MeasurableSet A) :
    walkNextBlockExitKernel m v hc s F (y, u) A =
      srwLaw m u {x' | walkNextBlockExit v hc s F y x' ∈ A} := by
  have hW := measurable_walkNextBlockExit v hc s hF
  rw [walkNextBlockExitKernel, Kernel.map_apply' _ hW _ hA, Kernel.prod_apply' _ _ _ (hW hA),
    Kernel.deterministic_apply, lintegral_dirac]
  rfl

/-- The block-exit position history `H_n = (Y_0, …, Y_n)` of the interpolated walk. -/
noncomputable def walkBlockExitHistory (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) (x : ℕ → ℤ) : Fin (n + 1) → ℂ :=
  blockExitPositions s F n (interpPathCM v hc x)

/-- The walk position `U_n = x_{τ_n}` at the step index just after the `n`-th block exit (the
position at step `0` when `τ_n = ∞`). -/
noncomputable def walkBlockExitStepPos (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) (x : ℕ → ℤ) : ℤ :=
  x (walkBlockExitStepTime v hc s F n x).toNat

theorem measurable_walkBlockExitHistory (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ}
    (hF : MeasurableSet F) (n : ℕ) : Measurable (walkBlockExitHistory v hc s F n) :=
  (measurable_blockExitPositions s hF n).comp (measurable_interpPathCM v hc)

theorem measurable_walkBlockExitStepTime (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) : Measurable (walkBlockExitStepTime v hc.le s F n) := by
  have hk : ∀ k : ℕ, MeasurableSet {x : ℕ → ℤ | walkBlockExitStepTime v hc.le s F n x = k} := by
    intro k
    have h := measurableSet_blockExitPositions_mem_inter_stepTime_eq v hc s F n univ k
    simpa only [mem_univ, ofPred_true, univ_inter] using h
  refine measurable_to_countable' fun t => ?_
  induction t using ENat.recTopCoe with
  | top =>
    have heq : walkBlockExitStepTime v hc.le s F n ⁻¹' {⊤} =
        (⋃ k : ℕ, {x : ℕ → ℤ | walkBlockExitStepTime v hc.le s F n x = k})ᶜ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, mem_ofPred_eq,
        not_exists]
      constructor
      · intro h k hk
        rw [h] at hk
        exact ENat.top_ne_natCast k hk
      · intro h
        by_contra hne
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
        exact h k hk.symm
    rw [heq]
    exact (MeasurableSet.iUnion hk).compl
  | coe k => exact hk k

theorem measurable_walkBlockExitStepPos (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) : Measurable (walkBlockExitStepPos v hc.le s F n) := by
  have hτ : Measurable fun x : ℕ → ℤ => (walkBlockExitStepTime v hc.le s F n x).toNat :=
    (measurable_of_countable ENat.toNat).comp (measurable_walkBlockExitStepTime v hc s F n)
  refine measurable_to_countable' fun u => ?_
  have heq : walkBlockExitStepPos v hc.le s F n ⁻¹' {u} =
      ⋃ j : ℕ, ({x : ℕ → ℤ | (walkBlockExitStepTime v hc.le s F n x).toNat = j} ∩
        {x | x j = u}) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      walkBlockExitStepPos]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      rw [hj]
      exact h
  rw [heq]
  refine MeasurableSet.iUnion fun j => ?_
  have hj : MeasurableSet ((fun f : ℕ → ℤ => f j) ⁻¹' {u}) :=
    measurable_pi_apply j (measurableSet_singleton u)
  exact (hτ (measurableSet_singleton j)).inter hj

/-- **The one-step kernel of the walk's block-exit chain.** From a history `g`, draw the walk
position `U_n` from its regular conditional distribution given `H_n = g`, restart the walk there
and read off the next block-exit position from `g_n`. -/
noncomputable def walkBlockExitStepKernel (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ) (n : ℕ) : Kernel (Fin (n + 1) → ℂ) ℂ :=
  Kernel.snd (condDistrib (walkBlockExitStepPos v hc s F n) (walkBlockExitHistory v hc s F n)
      (srwLaw m a) ⊗ₖ
    (walkNextBlockExitKernel m v hc s F).comap (fun p : (Fin (n + 1) → ℂ) × ℤ =>
      (p.1 (Fin.last n), p.2)) (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk
        measurable_snd))

theorem isMarkovKernel_walkBlockExitStepKernel (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (n : ℕ) :
    IsMarkovKernel (walkBlockExitStepKernel m a v hc s F n) := by
  have := isMarkovKernel_walkNextBlockExitKernel m v hc s hF
  unfold walkBlockExitStepKernel
  infer_instance

/-- **The joint law of the history and the next block-exit position is a composition-product.**
If every edge of `m` whose segment meets the complement of the measurable set `F` has length at
most `s / 2` and the step index `τ_n` is almost surely finite, then
`P^a ∘ (H_n, Y_{n+1})⁻¹ = (P^a ∘ H_n⁻¹) ⊗ₘ κ_n`. -/
theorem map_walkBlockExitHistory_next_eq_compProd (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ s / 2)
    (n : ℕ) (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc.le s F n x ≠ ⊤) :
    (srwLaw m a).map (fun x => (walkBlockExitHistory v hc.le s F n x,
        interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)))) =
      (srwLaw m a).map (walkBlockExitHistory v hc.le s F n) ⊗ₘ
        walkBlockExitStepKernel m a v hc.le s F n := by
  have := isMarkovKernel_walkNextBlockExitKernel m v hc.le s hF
  have := isMarkovKernel_walkBlockExitStepKernel m a v hc.le s hF n
  set H := walkBlockExitHistory v hc.le s F n with hHdef
  set U := walkBlockExitStepPos v hc.le s F n with hUdef
  have hH : Measurable H := measurable_walkBlockExitHistory v hc.le s hF n
  have hU : Measurable U := measurable_walkBlockExitStepPos v hc s F n
  have hY : Measurable fun x : ℕ → ℤ =>
      interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) := by
    have heq : (fun x : ℕ → ℤ =>
        interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x))) =
        fun x => blockExitPositions s F (n + 1) (interpPathCM v hc.le x) (Fin.last (n + 1)) := by
      funext x
      rw [blockExitPositions_apply, Fin.val_last]
    rw [heq]
    exact (measurable_pi_apply (Fin.last (n + 1))).comp
      ((measurable_blockExitPositions s hF (n + 1)).comp (measurable_interpPathCM v hc.le))
  have hL : ∀ {A : Set ℂ}, MeasurableSet A → Measurable fun p : (Fin (n + 1) → ℂ) × ℤ =>
      walkNextBlockExitKernel m v hc.le s F (p.1 (Fin.last n), p.2) A := by
    intro A hA
    exact (Kernel.measurable_coe _ hA).comp
      (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd)
  refine Measure.ext_prod fun {B} {A} hB hA => ?_
  rw [Measure.map_apply (hH.prodMk hY) (hB.prod hA), mk_preimage_prod,
    Measure.compProd_apply_prod hB hA]
  have hjoint := srwLaw_blockExitPositions_succ_mem_eq_setLIntegral m a v hc hs F hM n B hA hτ
  refine hjoint.trans ?_
  have hκ : ∀ g : Fin (n + 1) → ℂ, walkBlockExitStepKernel m a v hc.le s F n g A =
      ∫⁻ u, walkNextBlockExitKernel m v hc.le s F (g (Fin.last n), u) A
        ∂condDistrib U H (srwLaw m a) g := by
    intro g
    rw [walkBlockExitStepKernel, Kernel.snd_apply' _ _ hA, Kernel.compProd_apply (measurable_snd hA)]
    rfl
  simp_rw [hκ]
  have h1 := Measure.setLIntegral_compProd (μ := (srwLaw m a).map H)
    (κ := condDistrib U H (srwLaw m a)) (hL hA) hB MeasurableSet.univ
  simp only [Measure.restrict_univ] at h1
  rw [← h1, compProd_map_condDistrib hH.aemeasurable hU.aemeasurable,
    setLIntegral_map (hB.prod MeasurableSet.univ) (hL hA) (hH.prodMk hU), mk_preimage_prod,
    preimage_univ, inter_univ]
  refine setLIntegral_congr_fun (hH hB) fun x _ => ?_
  rw [walkNextBlockExitKernel_apply m v hc.le s hF _ _ hA]
  simp only [hHdef, hUdef, walkBlockExitHistory, walkBlockExitStepPos, blockExitPositions_apply,
    Fin.val_last]

/-- **The composition-product form for the walk embedded by a proper curve.** For a locally finite
multigraph whose consecutive vertices are adjacent, a continuous proper curve `η`, `ε > 0`,
speed `c > 0`, block size `s > 0` and a measurable `F` such that every edge whose segment meets
`Fᶜ` has length at most `s / 2`: `P^a ∘ (H_n, Y_{n+1})⁻¹ = (P^a ∘ H_n⁻¹) ⊗ₘ κ_n`. -/
theorem map_walkBlockExitHistory_next_eq_compProd_of_proper {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (n : ℕ) :
    (srwLaw m a).map (fun x => (walkBlockExitHistory (vertexPoint ε η) hc.le s F n x,
        interpPathCM (vertexPoint ε η) hc.le x
          (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)))) =
      (srwLaw m a).map (walkBlockExitHistory (vertexPoint ε η) hc.le s F n) ⊗ₘ
        walkBlockExitStepKernel m a (vertexPoint ε η) hc.le s F n :=
  map_walkBlockExitHistory_next_eq_compProd m a (vertexPoint ε η) hc hs hF hM n
    ((ae_walkBlockExitStepTime_ne_top hlf hcons hε hη hp hc a s F).mono fun _ hx => hx n)

end BlockExit

end MatedCRT
