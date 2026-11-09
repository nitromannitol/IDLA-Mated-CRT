import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# FIRST PASS: walk and measurability lemmas for the localization of Lemma 6.8 (task fp-S6e-6-7-6-8-from-uniform, q4)

Deterministic and measure-theoretic facts used to derive the faithful Lemma 6.8 (`firstPass_6_8_faithful`, FirstPass/S6d.lean)
from the uniform Lemma 6.7 (`UniformConstantOrderLowerBoundStmt`) by localization (operator note 22:52 UTC; the argument of
`notes/fp-gaps/CHATGPT-6-9-claims-referee.md`, section "Do faithful 6.7 and 6.8 follow?"). No new probabilistic input here.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

open Classical in
/-- `n < τ_A` (the first exit time of `A`) iff the path stays in `A` at all times `k ≤ n`. -/
theorem lt_vExitTime_iff {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} :
    (n : ℕ∞) < vExitTime A x ↔ ∀ k ≤ n, x k ∈ A := by
  unfold vExitTime
  split_ifs with h
  · rw [ENat.natCast_lt_natCast]
    constructor
    · intro hlt k hk
      by_contra hk'
      have := Nat.find_min' h hk'
      omega
    · intro hall
      by_contra hle
      push Not at hle
      exact Nat.find_spec h (hall _ hle)
  · push Not at h
    simp only [ENat.natCast_lt_top, true_iff]
    intro k _
    exact h k

/-- The event `{x | x k ∈ A for all k ≤ n → x n ∈ A}` is measurable on path space. -/
theorem measurableSet_stay_step (A' A : Set ℤ) (n : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (∀ k ≤ n, x k ∈ A') → x n ∈ A} := by
  have hA : ∀ k : ℕ, MeasurableSet {x : ℕ → ℤ | x k ∈ A'} := fun k =>
    measurable_pi_apply k (Set.to_countable A').measurableSet
  have hset : {x : ℕ → ℤ | (∀ k ≤ n, x k ∈ A') → x n ∈ A} =
      (⋂ k : ℕ, ⋂ (_ : k ≤ n), {x : ℕ → ℤ | x k ∈ A'})ᶜ ∪ {x : ℕ → ℤ | x n ∈ A} := by
    ext x
    simp [imp_iff_not_or]
  rw [hset]
  exact (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hA k).compl.union
    (measurable_pi_apply n (Set.to_countable A).measurableSet)

open Classical in
/-- The target event of Lemma 6.8, `{x | ∀ n < τ_{A'}, x n ∈ A}`, is measurable on path space. -/
theorem measurableSet_stay_target (A' A : Set ℤ) :
    MeasurableSet {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A} := by
  have hset : {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A} =
      ⋂ n : ℕ, {x : ℕ → ℤ | (∀ k ≤ n, x k ∈ A') → x n ∈ A} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, lt_vExitTime_iff]
  rw [hset]
  exact MeasurableSet.iInter fun n => measurableSet_stay_step A' A n

/-- Walk localization: a path started in `W₁` with no edge from `W₁` to `W₀` stays in `W₁` before its first exit
from `W₀ ∪ W₁` (the adjacency of the walk is `hstep`, the absence of edges is `hno`). -/
theorem walk_stays_in_W1 {m : ℤ → ℤ → ℕ} {x : ℕ → ℤ} {W0 W1 : Set ℤ} {a : ℤ}
    (hx0 : x 0 = a) (ha : a ∈ W1)
    (hstep : ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hno : ∀ v ∈ W1, ∀ w ∈ W0, m v w = 0) :
    ∀ k : ℕ, (k : ℕ∞) < vExitTime (W0 ∪ W1) x → x k ∈ W1 := by
  intro k
  induction k with
  | zero => intro _; rw [hx0]; exact ha
  | succ k ih =>
    intro hk
    have hk' : (k : ℕ∞) < vExitTime (W0 ∪ W1) x :=
      lt_vExitTime_iff.2 fun j hj => (lt_vExitTime_iff.1 hk) j (by omega)
    have hmem : x (k + 1) ∈ W0 ∪ W1 := (lt_vExitTime_iff.1 hk) (k + 1) le_rfl
    rcases hstep k with h | h
    · rw [h]; exact ih hk'
    · rcases hmem with h0 | h1
      · exact absurd (hno (x k) (ih hk') (x (k + 1)) h0) h
      · exact h1

/-- **Localized walk bound** (the last step of `firstPass_6_8_faithful`). Let `W₀, W₁` be vertex sets with `a ∈ W₁`, no
edge from `W₁` to `W₀` (`hno`), and `W₁ ⊆ A'` (`hA'`). If the walk from `a` hits `W₁ \ A` before its exit from `W₀ ∪ W₁`
with probability `≥ s`, then the walk stays in `A` before its exit from `A'` with probability `≤ 1 - s`. Walk-level
counterpart of the localization in `CHATGPT-6-9-claims-referee.md`; the law is a probability measure, the target event
is measurable (`measurableSet_stay_target`), and the inclusion holds on the almost sure set of paths with `x 0 = a` and
nearest-neighbour steps. -/
theorem srw_localized_bound (m : ℤ → ℤ → ℕ) (a : ℤ) (A A' W0 W1 Θ' : Set ℤ) {s : ℝ} (hs : 0 ≤ s)
    (ha1 : a ∈ W1) (hno : ∀ v ∈ W1, ∀ w ∈ W0, m v w = 0) (hA' : ∀ v ∈ W1, v ∈ A')
    (hT : ENNReal.ofReal s ≤ srwLaw m a {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime (W0 ∪ W1) x ∧
      x n ∈ (W0 ∪ W1) \ ((A ∩ W1) ∪ Θ')}) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A} ≤ ENNReal.ofReal (1 - s) := by
  have hBm : MeasurableSet {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A} :=
    measurableSet_stay_target A' A
  have hae : ∀ᵐ x ∂srwLaw m a, x 0 = a ∧ ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 :=
    (srwLaw_ae_start m a).and (srwAeAdjacentStep m a)
  have hmono : srwLaw m a {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime (W0 ∪ W1) x ∧
      x n ∈ (W0 ∪ W1) \ ((A ∩ W1) ∪ Θ')} ≤
      srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A}ᶜ := by
    apply measure_mono_ae
    filter_upwards [hae] with x hx hxT hxB
    obtain ⟨n, hn, hxn⟩ := hxT
    have hW : ∀ k : ℕ, (k : ℕ∞) < vExitTime (W0 ∪ W1) x → x k ∈ W1 :=
      walk_stays_in_W1 hx.1 ha1 hx.2 hno
    have hnA' : (n : ℕ∞) < vExitTime A' x := lt_vExitTime_iff.2 fun k hk =>
      hA' _ (hW k (lt_vExitTime_iff.2 fun j hj => (lt_vExitTime_iff.1 hn) j (le_trans hj hk)))
    have hxA : x n ∈ A := hxB n hnA'
    exact hxn.2 (Or.inl ⟨hxA, hW n hn⟩)
  have hcompl := prob_compl_eq_one_sub (μ := srwLaw m a) hBm
  have h1 : ENNReal.ofReal s ≤ 1 - srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A} := by
    rw [← hcompl]
    exact hT.trans hmono
  rw [ENNReal.ofReal_sub 1 hs, ENNReal.ofReal_one]
  calc srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A}
      = 1 - (1 - srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime A' x → x n ∈ A}) :=
        (ENNReal.sub_sub_cancel ENNReal.one_ne_top (prob_le_one (μ := srwLaw m a))).symm
    _ ≤ 1 - ENNReal.ofReal s := tsub_le_tsub_left h1 1

end MatedCRT
