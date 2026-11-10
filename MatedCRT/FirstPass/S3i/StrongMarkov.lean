import MatedCRT.FirstPass.S4S6c.StrongMarkovState
import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral

/-!
# Strong Markov inequality at `vExitTime` (plan `CHATGPT-221-idla-3-6-QuenchedLensStep-plan-PRO`, §2, worker H2)

Plan Lemma 2, `srwLaw_strongMarkov_vExitTime`, stated exactly as in the plan, in the private namespace
`MatedCRT.FirstPass36.H2`. The definitions `shiftedPath`, `FiniteExitData`, `exitHitProb` are copies of the
plan's "Minimal internal definitions"; merge with `MatedCRT/FirstPass/S3i/LensDefs.lean` by renaming.

Proof. The event is `{τ < ⊤} ∩ {the walk after τ enters the good event}` with `τ = vExitTime A`.
Strong Markov decomposition at `τ` (`srwLaw_strong_markov_state`) gives a sum over `k` of integrals over
`{τ = k}` of `srwLaw m (x k) (future event)`. On `{τ = k}` the exit vertex `x k` lies in `vBoundary m A`
almost surely (`ae_exitPosition_mem_vBoundary`: `x 0 = a ∈ A` a.s., and every step is an edge of `m`
a.s. by `srwLaw_nonadjacent_null`). Each term is therefore at most `M * P(τ = k)` with
`M = ⨆ v ∈ vBoundary m A, ofReal (exitHitProb …)`, and `∑_k P(τ = k) ≤ 1`.

Lemma 1 (almost-sure finite exit) is not used: the bound needs only `∑_k P(τ = k) ≤ 1`.
-/

namespace MatedCRT
namespace FirstPass36
namespace H2

open MeasureTheory Set Function
open scoped ENNReal

/-- The path after time `n`, read from `x n` on (copy of the plan's definition). -/
def shiftedPath (n : ℕ) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun k => x (n + k)

/-- Finite-state data for almost-sure exit and first-step harmonicity (copy of the plan's definition). -/
def FiniteExitData (m : ℤ → ℤ → ℕ) (A : Set ℤ) : Prop :=
  A.Finite ∧
  (∀ a ∈ A, 0 < mdeg m a) ∧
  ∀ a ∈ A, ∃ b ∈ vBoundary m A, ∃ p : List ℤ,
    IsVPathIn m (vClosure m A) p a b

/-- Probability of exiting `A` through `B`, as a real-valued function of the starting vertex
(copy of the plan's definition). -/
noncomputable def exitHitProb
    (m : ℤ → ℤ → ℕ) (A B : Set ℤ) (a : ℤ) : ℝ :=
  (srwLaw m a
    {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B}).toReal

/-- The first exit time equals `k` iff `x k` leaves `A` and `x j ∈ A` for `j < k`. -/
lemma vExitTime_eq_coe_iff_spec (A : Set ℤ) (x : ℕ → ℤ) (k : ℕ) :
    vExitTime A x = (k : ℕ∞) ↔ x k ∉ A ∧ ∀ j < k, x j ∈ A := by
  rw [vExitTime_eq_natCast_iff]
  constructor
  · rintro ⟨hlt, hj⟩
    refine ⟨fun hk => hlt (natCast_lt_vExitTime_iff.2 fun j hjk => ?_), hj⟩
    rcases Nat.lt_or_ge j k with h | h
    · exact hj j h
    · rw [show j = k from le_antisymm hjk h]
      exact hk
  · rintro ⟨hk, hj⟩
    exact ⟨fun hlt => hk (natCast_lt_vExitTime_iff.1 hlt k le_rfl), hj⟩

/-- The level set `{τ_A = k}` of the first exit time is measurable. -/
lemma measurableSet_vExitTime_eq (A : Set ℤ) (k : ℕ) :
    MeasurableSet {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)} :=
  measurable_vExitTime A (measurableSet_singleton _)

/-- Almost surely every step of the walk from `a` is trivial or an edge of `m`. -/
lemma ae_step_adjacent (m : ℤ → ℤ → ℕ) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
  refine ae_all_iff.2 fun n => ?_
  exact ae_iff.2 (MatedCRT.WalkSteps.srwLaw_nonadjacent_null m n a)

/-- Almost surely, if the walk from `a ∈ A` first leaves `A` at time `k`, the exit vertex lies in
the boundary `∂A = vBoundary m A`. -/
lemma ae_exitPosition_mem_vBoundary (m : ℤ → ℤ → ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (k : ℕ) :
    ∀ᵐ x ∂srwLaw m a, vExitTime A x = (k : ℕ∞) → x k ∈ vBoundary m A := by
  filter_upwards [srwLaw_ae_start m a, ae_step_adjacent m a] with x hx0 hadj hτ
  obtain ⟨hk, hj⟩ := (vExitTime_eq_coe_iff_spec A x k).1 hτ
  cases k with
  | zero =>
    exfalso
    have h0 : x 0 ∈ A := by
      rw [hx0]
      exact ha
    exact hk h0
  | succ j =>
    have hjA : x j ∈ A := hj j (Nat.lt_succ_self j)
    show x (j + 1) ∉ A ∧ ∃ b ∈ A, m b (x (j + 1)) ≠ 0
    refine ⟨hk, x j, hjA, ?_⟩
    rcases hadj j with h | h
    · exact absurd (by rw [h]; exact hjA) hk
    · exact h

/-- The event that the walk started at a fixed vertex `y` exits `U y` through `B y` is measurable. -/
lemma measurableSet_exitHitEvent (U B : ℤ → Set ℤ) (y : ℤ) :
    MeasurableSet {z : ℕ → ℤ | vExitTime (U y) z < ⊤ ∧ vExitPosition (U y) z ∈ B y} := by
  have h1 : MeasurableSet {z : ℕ → ℤ | vExitTime (U y) z < ⊤} :=
    measurable_vExitTime (U y) (Set.to_countable (Iio (⊤ : ℕ∞))).measurableSet
  have h2 : MeasurableSet {z : ℕ → ℤ | vExitPosition (U y) z ∈ B y} :=
    measurable_vExitPosition (U y) (Set.to_countable (B y)).measurableSet
  exact h1.inter h2

-- `hA` is kept as in the plan but not used: the bound needs only `∑_k P(τ = k) ≤ 1`.
set_option linter.unusedVariables false in
/-- **Plan Lemma 2** (`srwLaw_strongMarkov_vExitTime`). Strong Markov inequality at the first exit time
`vExitTime A` of the walk from `a ∈ A`: the probability that, after leaving `A` at a vertex `v` of the
boundary, the walk exits `U v` through `B v` is at most the supremum over `v ∈ ∂A` of
`P_v(exit U v through B v)`. -/
theorem srwLaw_strongMarkov_vExitTime
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {a : ℤ}
    (hA : FiniteExitData m A) (ha : a ∈ A)
    (U B : ℤ → Set ℤ) :
    srwLaw m a
      {x |
        vExitTime A x < ⊤ ∧
        (let n := (vExitTime A x).toNat
         let v := vExitPosition A x
         vExitTime (U v) (shiftedPath n x) < ⊤ ∧
         vExitPosition (U v) (shiftedPath n x) ∈ B v)}
      ≤
    ⨆ v ∈ vBoundary m A,
      ENNReal.ofReal (exitHitProb m (U v) (B v) v) := by
  -- the level sets of the exit time are cut out by the first `k + 1` coordinates
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      (univ : Set (ℕ → ℤ)) ∩ {x | vExitTime A x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
    intro k
    refine ⟨{h | (∀ i : Fin (k + 1), (i : ℕ) < k → h i ∈ A) ∧ h (Fin.last k) ∉ A},
      (Set.to_countable _).measurableSet, ?_⟩
    ext x
    simp only [univ_inter, mem_ofPred_eq, pathHist, Fin.val_last]
    rw [vExitTime_eq_coe_iff_spec]
    constructor
    · rintro ⟨hk, hj⟩
      exact ⟨fun i hi => hj i hi, hk⟩
    · rintro ⟨hi, hk⟩
      exact ⟨hk, fun j hj => hi ⟨j, by omega⟩ hj⟩
  -- strong Markov decomposition at `τ = vExitTime A`
  have key : srwLaw m a (univ ∩ {x | ∃ k : ℕ, vExitTime A x = (k : ℕ∞) ∧
        WalkPotential.pathShift k x ∈
          {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}})
      = ∑' k : ℕ, ∫⁻ x in (univ ∩ {x | vExitTime A x = (k : ℕ∞)}),
          srwLaw m (x k)
            {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}
            ∂srwLaw m a :=
    srwLaw_strong_markov_state m a (vExitTime A)
      (fun y => {z : ℕ → ℤ | vExitTime (U y) z < ⊤ ∧ vExitPosition (U y) z ∈ B y})
      (fun y => measurableSet_exitHitEvent U B y) hS
  -- the event of the lemma is the union over the exit time of the future events
  have hevent : {x : ℕ → ℤ |
        vExitTime A x < ⊤ ∧
        (let n := (vExitTime A x).toNat
         let v := vExitPosition A x
         vExitTime (U v) (shiftedPath n x) < ⊤ ∧
         vExitPosition (U v) (shiftedPath n x) ∈ B v)}
      = univ ∩ {x | ∃ k : ℕ, vExitTime A x = (k : ℕ∞) ∧
        WalkPotential.pathShift k x ∈
          {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}} := by
    ext x
    constructor
    · rintro ⟨hlt, hfut⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne
      have hn : (vExitTime A x).toNat = k := by
        rw [← hk, ENat.toNat_natCast]
      have hpos : vExitPosition A x = x k := by
        unfold vExitPosition
        rw [hn]
      refine ⟨mem_univ _, k, hk.symm, ?_⟩
      simp only [hn, hpos] at hfut
      exact hfut
    · rintro ⟨-, k, hk, hfut⟩
      have hn : (vExitTime A x).toNat = k := by
        rw [hk, ENat.toNat_natCast]
      have hpos : vExitPosition A x = x k := by
        unfold vExitPosition
        rw [hn]
      refine ⟨by rw [hk]; exact ENat.natCast_lt_top k, ?_⟩
      simp only [hn, hpos]
      exact hfut
  rw [hevent, key]
  -- on `{τ = k}` the future event has conditional mass at most `M`
  set M : ℝ≥0∞ := ⨆ v ∈ vBoundary m A, ENNReal.ofReal (exitHitProb m (U v) (B v) v) with hM
  have hpt : ∀ k : ℕ, ∫⁻ x in (univ ∩ {x | vExitTime A x = (k : ℕ∞)}),
      srwLaw m (x k)
        {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}
        ∂srwLaw m a ≤ M * srwLaw m a {x | vExitTime A x = (k : ℕ∞)} := by
    intro k
    have hmeas : MeasurableSet (univ ∩ {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)}) := by
      rw [univ_inter]
      exact measurableSet_vExitTime_eq A k
    calc ∫⁻ x in (univ ∩ {x | vExitTime A x = (k : ℕ∞)}),
          srwLaw m (x k)
            {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}
            ∂srwLaw m a
        ≤ ∫⁻ _ in (univ ∩ {x | vExitTime A x = (k : ℕ∞)}), M ∂srwLaw m a := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hmeas]
          filter_upwards [ae_exitPosition_mem_vBoundary m ha k] with x hx hxs
          have hv : x k ∈ vBoundary m A := hx hxs.2
          calc srwLaw m (x k)
                {z : ℕ → ℤ | vExitTime (U (x k)) z < ⊤ ∧ vExitPosition (U (x k)) z ∈ B (x k)}
              = ENNReal.ofReal (exitHitProb m (U (x k)) (B (x k)) (x k)) :=
                (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
            _ ≤ M := le_iSup₂ (f := fun (v : ℤ) (_ : v ∈ vBoundary m A) =>
                  ENNReal.ofReal (exitHitProb m (U v) (B v) v)) (x k) hv
      _ = M * srwLaw m a (univ ∩ {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)}) :=
          setLIntegral_const _ _
      _ = M * srwLaw m a {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)} := by rw [univ_inter]
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  -- the level sets of `τ` are disjoint, so their masses sum to at most one
  have hdisj : Pairwise (Disjoint on fun k : ℕ => {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)}) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj => hij ?_
    have hi' : vExitTime A x = (i : ℕ∞) := hi
    have hj' : vExitTime A x = (j : ℕ∞) := hj
    have h : ((i : ℕ) : ℕ∞) = (j : ℕ∞) := hi'.symm.trans hj'
    exact_mod_cast h
  calc ∑' k : ℕ, M * srwLaw m a {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)}
      = M * ∑' k : ℕ, srwLaw m a {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)} :=
        ENNReal.tsum_mul_left
    _ = M * srwLaw m a (⋃ k : ℕ, {x : ℕ → ℤ | vExitTime A x = (k : ℕ∞)}) := by
        rw [measure_iUnion hdisj fun k => measurableSet_vExitTime_eq A k]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left prob_le_one (by exact zero_le)
    _ = M := mul_one M

end H2
end FirstPass36
end MatedCRT
