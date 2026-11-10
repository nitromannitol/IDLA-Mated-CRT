import Mathlib
import MatedCRT.Defs.RandomWalk
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.FirstPass.S6e.Relation
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6r.Amplification

/-!
# Lemma 6.8, walk bridge (q2, S10 item (b))

The quenched exit probability `Lemma68Config.exitQ S ε ω r i` is the `srwLaw` probability of
`Lemma68Walk.exitEvent U A` with `U = killed ε η Θ F0 r` and `A = i.A` (S6h/Core.lean). The event is the
no-escape event `{X n ∈ A for all n < τ_U}` of `prefix_bad_bound` (S6r/Amplification.lean), with coordinates
`X n x = x n`, killing time `τ_U = vExitTime U` (Defs/RandomWalk.lean) and the natural filtration
`coordFiltration` of the coordinates. Hence the strong-Markov chain bound of `prefix_bad_bound` transfers to `exitQ`.

Named hypotheses, not proved here: the one-test bound `hone` (strong Markov at `T k`; z8, S6r/OneTest.lean),
the stopping times `T k`, `L k` (z9, S6r/ShellWiring.lean) and the pathwise shell inequalities `hTT`, `hLT`,
`hcross`, `hend` (z9). Nothing here uses the environment.
-/

open MeasureTheory

namespace MatedCRT

namespace Lemma68WalkBridge

open Lemma68Window

/-- The natural filtration of the coordinate process `n ↦ x n` on path space `ℕ → ℤ`. -/
noncomputable def coordFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℤ)) :=
  Filtration.natural (fun n (x : ℕ → ℤ) => x n) (fun n => (measurable_pi_apply n).stronglyMeasurable)

/-- The coordinate `x n` is `coordFiltration n`-measurable. -/
theorem coord_measurable (n : ℕ) : Measurable[coordFiltration n] (fun x : ℕ → ℤ => x n) := by
  intro s _
  exact (le_iSup₂ (f := fun (j : ℕ) (_ : j ≤ n) =>
    MeasurableSpace.comap (fun x : ℕ → ℤ => x j) (inferInstance : MeasurableSpace ℤ)) n le_rfl)
    _ ⟨s, ‹MeasurableSet s›, rfl⟩

/-- The first exit time `vExitTime U` of a path from `U` is a stopping time of `coordFiltration`
(the set `{τ_U ≤ i}` is `{∃ k ≤ i, x k ∉ U}`, by `lt_vExitTime_iff'`). -/
theorem isStoppingTime_vExitTime (U : Set ℤ) : IsStoppingTime coordFiltration (vExitTime U) := by
  intro i
  have hiff : ∀ x : ℕ → ℤ, vExitTime U x ≤ (i : ℕ∞) ↔ ¬ ∀ k ≤ i, x k ∈ U := fun x => by
    rw [← not_lt, Lemma68Relation.lt_vExitTime_iff']
  have hset2 : {x : ℕ → ℤ | ∀ k ≤ i, x k ∈ U} = ⋂ k ∈ Set.Iic i, (fun x : ℕ → ℤ => x k) ⁻¹' U := by
    ext x
    simp
  have key : MeasurableSet[coordFiltration i] {x : ℕ → ℤ | ∀ k ≤ i, x k ∈ U}ᶜ := by
    refine MeasurableSet.compl ?_
    rw [hset2]
    refine MeasurableSet.biInter (Set.to_countable _) fun k hk => ?_
    exact coordFiltration.mono (Set.mem_Iic.1 hk) _ (coord_measurable k MeasurableSet.of_discrete)
  convert key using 1
  exact Set.ext hiff

/-- The walk exit event is the no-escape event of the coordinates killed at `vExitTime U`. -/
theorem exitEvent_eq_noEscapeSet (U A : Set ℤ) :
    Lemma68Walk.exitEvent U A = noEscapeSet (fun n (x : ℕ → ℤ) => x n) A (vExitTime U) := by
  ext x
  simp only [Lemma68Walk.exitEvent, noEscapeSet, Set.mem_ofPred_eq]
  exact ⟨fun h n hn => h n (Lemma68Relation.lt_vExitTime_iff'.1 hn),
    fun h n hn => h n (Lemma68Relation.lt_vExitTime_iff'.2 hn)⟩

/-- `exitQ` as a no-escape probability for the simple random walk law. -/
theorem srw_exit_eq_noEscape (m : ℤ → ℤ → ℕ) (a : ℤ) (U A : Set ℤ) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) =
      (srwLaw m a).real (noEscapeSet (fun n (x : ℕ → ℤ) => x n) A (vExitTime U)) := by
  rw [exitEvent_eq_noEscapeSet]

/-- Walk-level chain bound: `prefix_bad_bound` for the simple random walk law, with the exit event of
`U` in place of the no-escape event. -/
theorem srw_exit_le_pow {m : ℤ → ℤ → ℕ} {a : ℤ} {U A : Set ℤ}
    {T L : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    (hL : ∀ k, IsStoppingTime coordFiltration (L k)) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw m a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) A (T k) (vExitTime U) →
        (srwLaw m a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) A (T k) (L k)).indicator
          (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ x, T j x ≤ T (j + 1) x) (hLT : ∀ j < n, ∀ x, L j x ≤ T (j + 1) x)
    (hcross : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U),
      T n x < vExitTime U x)
    (hend : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U), L n x ≤ vExitTime U x) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) ≤ (1 - q) ^ (n + 1) := by
  rw [srw_exit_eq_noEscape]
  exact prefix_bad_bound coordFiltration coord_measurable MeasurableSet.of_discrete hT hL
    (isStoppingTime_vExitTime U) hq1 n hone hTT hLT hcross hend

/-- The quenched exit probability `exitQ` of a Lemma 6.8 configuration satisfies the walk-level chain bound
`(1 - q)^(n + 1)`; `U` is the killed set `killed ε η Θ F0 r` and `A = i.A` (S6h/Core.lean). -/
theorem exitQ_le_pow {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r : ℝ)
    (i : Lemma68Config.Config68) {T L : ℕ → (ℕ → ℤ) → ℕ∞}
    (hT : ∀ k, IsStoppingTime coordFiltration (T k)) (hL : ∀ k, IsStoppingTime coordFiltration (L k))
    {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k)
          (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k) (L k)).indicator
          (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ x, T j x ≤ T (j + 1) x) (hLT : ∀ j < n, ∀ x, L j x ≤ T (j + 1) x)
    (hcross : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)),
      T n x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x)
    (hend : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)),
      L n x ≤ vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x) :
    Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ (n + 1) := by
  unfold Lemma68Config.exitQ
  exact srw_exit_le_pow hT hL hq1 n hone hTT hLT hcross hend

/-- The test-count prefactor: `q0 / (1 + log (1/r))^2 ≤ 1` for `0 < r ≤ 1` and `q0 ≤ 1`. -/
theorem q_le_one {q0 r : ℝ} (hq0 : 0 ≤ q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hD : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  calc q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q0 := div_le_self hq0 hD
    _ ≤ 1 := hq1

end Lemma68WalkBridge

end MatedCRT
