import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.Proofs.WalkPotential.GreenFirstStep

/-!
# Lemma 6.7 from Lemma 6.8 at the level of walk laws

The printed proof of Lemma 6.7 (paper lemma:constant-order-lower-bound, the proof "assuming Lemma
lemma:constant-order-lower-bound-div") runs as follows. The walk from `a ∈ cl Θ` reaches the frontier
`F = V(∂(Θ̄ + B_{r/2}))` before exiting `V = V(Θ̄ + B_r)` (cell-size estimate; this is the input `hF`
below). By the strong Markov property at the first hit `τ_F`, the trace event
`E = {∃ n < τ_V, X_n ∈ V \ (S ∪ Θ)}` has probability at least `s₂` from `a`, provided it has
probability at least `s₂` from every `b ∈ F`. From `b`, the complement of `E` is contained in the event
`{X_n ∈ S \ Θ for all n < τ_{V \ Θ}}` of Lemma 6.8, which has probability at most `1 - s₂`.

Here the frontier separation `hF` and the frontier bound `hfront` (Lemma 6.8 at each `b ∈ F`) are explicit
hypotheses. The file proves the walk-law reduction `trace_bound_of_exit_bound`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

open WalkPotential

namespace TraceFrom68

/-- The trace event: the walk visits `B` at a time before its exit from `V`. -/
abbrev traceSet (V B : Set ℤ) : Set (ℕ → ℤ) :=
  {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime V x ∧ x n ∈ B}

/-- The paths that hit `F` before they exit `V`. -/
abbrev hitBeforeExit (F V : Set ℤ) : Set (ℕ → ℤ) :=
  {x | vHitTime F x < vExitTime V x}

theorem measurableSet_traceSet (V B : Set ℤ) : MeasurableSet (traceSet V B) := by
  have h : traceSet V B = ⋃ n : ℕ, ({x : ℕ → ℤ | (n : ℕ∞) < vExitTime V x} ∩
      (fun x : ℕ → ℤ => x n) ⁻¹' B) := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq, mem_preimage]
  rw [h]
  exact MeasurableSet.iUnion fun n =>
    (ConstantOrderDiv.measurableSet_lt_vExitTime V n).inter
      ((measurable_pi_apply n) (Set.to_countable B).measurableSet)

theorem measurable_pathHist_fin (k : ℕ) : Measurable (pathHist k) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem vHitTime_eq_iff (F : Set ℤ) (k : ℕ) (x : ℕ → ℤ) :
    vHitTime F x = (k : ℕ∞) ↔ x k ∈ F ∧ ∀ i < k, x i ∉ F := by
  rw [vHitTime, NextExitStop.vExitTime_eq_coe_iff]
  simp only [mem_compl_iff, not_not]
  exact and_comm

theorem vHitTime_le_of_mem {F : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (hn : x n ∈ F) :
    vHitTime F x ≤ (n : ℕ∞) := by
  by_contra h
  rw [not_le] at h
  have h' : (n : ℕ∞) < vExitTime Fᶜ x := h
  exact (WalkPotential.natCast_lt_vExitTime_iff.1 h' n le_rfl) hn

/-- **Lemma 6.8 gives Lemma 6.7 from each frontier start** (walk-level form of the printed argument): if the walk
started at `b` stays in `S \ Θ` until it exits `V \ Θ` with probability at most `1 - s₂`, then the trace of
the walk from `b` before its exit from `V` meets `V \ (S ∪ Θ)` with probability at least `s₂`. -/
theorem start_bound (m : ℤ → ℤ → ℕ) (V Θ S' : Set ℤ) {s2 : ℝ} (hs0 : 0 ≤ s2) (hs1 : s2 ≤ 1) (b : ℤ)
    (hb : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (V \ Θ) x → x n ∈ S' \ Θ} ≤
      ENNReal.ofReal (1 - s2)) :
    ENNReal.ofReal s2 ≤ srwLaw m b (traceSet V (V \ (S' ∪ Θ))) := by
  have hsub : (traceSet V (V \ (S' ∪ Θ)))ᶜ ⊆
      {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (V \ Θ) x → x n ∈ S' \ Θ} := by
    intro x hx n hn
    have hxV : ∀ i ≤ n, x i ∈ V \ Θ := WalkPotential.natCast_lt_vExitTime_iff.1 hn
    have hnV : (n : ℕ∞) < vExitTime V x :=
      WalkPotential.natCast_lt_vExitTime_iff.2 fun i hi => (hxV i hi).1
    refine ⟨?_, (hxV n le_rfl).2⟩
    by_contra hS
    exact hx ⟨n, hnV, (hxV n le_rfl).1, fun h => h.elim hS (hxV n le_rfl).2⟩
  have h1 : srwLaw m b (traceSet V (V \ (S' ∪ Θ)))ᶜ ≤ ENNReal.ofReal (1 - s2) :=
    (measure_mono hsub).trans hb
  have h2 : (1 : ℝ≥0∞) ≤ srwLaw m b (traceSet V (V \ (S' ∪ Θ))) +
      srwLaw m b (traceSet V (V \ (S' ∪ Θ)))ᶜ := by
    calc (1 : ℝ≥0∞) = srwLaw m b univ := measure_univ.symm
      _ = srwLaw m b (traceSet V (V \ (S' ∪ Θ)) ∪ (traceSet V (V \ (S' ∪ Θ)))ᶜ) := by
        rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  have hsum : ENNReal.ofReal s2 + ENNReal.ofReal (1 - s2) = 1 := by
    rw [← ENNReal.ofReal_add hs0 (by linarith : (0 : ℝ) ≤ 1 - s2)]
    norm_num
  have h3 : ENNReal.ofReal s2 + ENNReal.ofReal (1 - s2) ≤
      srwLaw m b (traceSet V (V \ (S' ∪ Θ))) + ENNReal.ofReal (1 - s2) :=
    calc ENNReal.ofReal s2 + ENNReal.ofReal (1 - s2) = 1 := hsum
      _ ≤ _ := h2
      _ ≤ _ := add_le_add le_rfl h1
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h3

/-- **The trace bound of Lemma 6.7 from Lemma 6.8** (walk-law form). Inputs: `hF`, the frontier separation (the walk
from `a` exits `V` only after visiting `F`, a.s.), and `hfront`, the Lemma 6.8 bound at every frontier start `b ∈ F`. -/
theorem trace_bound_of_exit_bound (m : ℤ → ℤ → ℕ) (a : ℤ) (V Θ S' F : Set ℤ) {s2 : ℝ}
    (hs0 : 0 ≤ s2) (hs1 : s2 ≤ 1)
    (hF : srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime V x → x n ∉ F} = 0)
    (hfront : ∀ b ∈ F, srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (V \ Θ) x → x n ∈ S' \ Θ} ≤
      ENNReal.ofReal (1 - s2)) :
    ENNReal.ofReal s2 ≤ srwLaw m a (traceSet V (V \ (S' ∪ Θ))) := by
  -- the determinacy of the first hit of `F` before exit of `V` by the path up to a fixed time `k`
  have key : ∀ (k : ℕ) (z : ℕ → ℤ),
      (z ∈ hitBeforeExit F V ∧ vHitTime F z = (k : ℕ∞)) ↔
        (((∀ i : Fin (k + 1), (i : ℕ) < k → pathHist k z i ∉ F) ∧
            ∃ i : Fin (k + 1), (i : ℕ) = k ∧ pathHist k z i ∈ F) ∧
          ∀ i : Fin (k + 1), pathHist k z i ∈ V) := by
    intro k z
    constructor
    · rintro ⟨hS, hτ⟩
      have hS' : vHitTime F z < vExitTime V z := hS
      rw [hτ] at hS'
      obtain ⟨h1, h2⟩ := (vHitTime_eq_iff F k z).1 hτ
      have hV := WalkPotential.natCast_lt_vExitTime_iff.1 hS'
      exact ⟨⟨fun i hi => h2 i hi, ⟨⟨k, Nat.lt_succ_self k⟩, rfl, h1⟩⟩,
        fun i => hV i (Nat.lt_succ_iff.1 i.2)⟩
    · rintro ⟨⟨h2, ⟨i, hi, hmem⟩⟩, hV⟩
      have hzk : z k ∈ F := by
        have e : z k = z i := by rw [hi]
        rw [e]
        exact hmem
      have hlt : ∀ j < k, z j ∉ F := fun j hj => h2 ⟨j, by omega⟩ hj
      have hVk : ∀ j ≤ k, z j ∈ V := fun j hj => hV ⟨j, by omega⟩
      have hτ : vHitTime F z = (k : ℕ∞) := (vHitTime_eq_iff F k z).2 ⟨hzk, hlt⟩
      refine ⟨?_, hτ⟩
      show vHitTime F z < vExitTime V z
      rw [hτ]
      exact WalkPotential.natCast_lt_vExitTime_iff.2 hVk
  have hS : ∀ k : ℕ, ∃ F' : Set (Fin (k + 1) → ℤ), MeasurableSet F' ∧
      hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)} = {x | pathHist k x ∈ F'} := by
    intro k
    obtain ⟨F', hF', hEq⟩ := NextExitStop.exists_pathHist_of_determinacy k
      (fun x => x ∈ hitBeforeExit F V ∧ vHitTime F x = (k : ℕ∞))
      (fun x y hxy => by
        rw [key k x, key k y, hxy])
    exact ⟨F', hF', hEq⟩
  have hmeasA : ∀ k : ℕ, MeasurableSet (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}) := by
    intro k
    obtain ⟨F', hF', hEq⟩ := hS k
    rw [hEq]
    exact measurable_pathHist_fin k hF'
  -- strong Markov property at the first hit of `F` before exit of `V`
  have hSM := srwLaw_strong_markov_state m a (vHitTime F) (fun _ => traceSet V (V \ (S' ∪ Θ)))
    (fun _ => measurableSet_traceSet V _) (S := hitBeforeExit F V) hS
  -- the strong Markov event lies inside the trace event
  have hincl : hitBeforeExit F V ∩ {x | ∃ k : ℕ, vHitTime F x = (k : ℕ∞) ∧
      pathShift k x ∈ traceSet V (V \ (S' ∪ Θ))} ⊆ traceSet V (V \ (S' ∪ Θ)) := by
    rintro x ⟨hxS, k, hk, n, hn, hmem⟩
    have hxS' : vHitTime F x < vExitTime V x := hxS
    rw [hk] at hxS'
    have hk' : (k : ℕ∞) < vExitTime V x := hxS'
    refine ⟨k + n, ?_, hmem⟩
    refine WalkPotential.natCast_lt_vExitTime_iff.2 fun i hi => ?_
    by_cases hik : i ≤ k
    · exact WalkPotential.natCast_lt_vExitTime_iff.1 hk' i hik
    · have h := WalkPotential.natCast_lt_vExitTime_iff.1 hn (i - k) (by omega)
      have e : k + (i - k) = i := by omega
      have h' : x (k + (i - k)) ∈ V := h
      rw [e] at h'
      exact h'
  -- the trace event of the walk from each frontier point
  have hpiece : ∀ k : ℕ, ∫⁻ x in (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}),
      ENNReal.ofReal s2 ∂srwLaw m a ≤
      ∫⁻ x in (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}),
        srwLaw m (x k) (traceSet V (V \ (S' ∪ Θ))) ∂srwLaw m a := by
    intro k
    refine setLIntegral_mono' (hmeasA k) fun x hx => ?_
    have hxF : x k ∈ F := ((vHitTime_eq_iff F k x).1 hx.2).1
    exact start_bound m V Θ S' hs0 hs1 (x k) (hfront (x k) hxF)
  have hlow := ENNReal.tsum_le_tsum hpiece
  have hconst : ∀ k : ℕ, ∫⁻ x in (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}),
      ENNReal.ofReal s2 ∂srwLaw m a =
      ENNReal.ofReal s2 * srwLaw m a (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}) :=
    fun k => setLIntegral_const _ _
  -- the first hit of `F` before exit of `V` has full measure (frontier separation hF)
  have hcover : srwLaw m a (hitBeforeExit F V) ≤
      ∑' k : ℕ, srwLaw m a (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}) := by
    refine (measure_mono ?_).trans (measure_iUnion_le _)
    intro x hx
    have hx' : vHitTime F x < vExitTime V x := hx
    have hne : vHitTime F x ≠ ⊤ := by
      intro h
      rw [h] at hx'
      exact not_top_lt hx'
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    exact mem_iUnion.2 ⟨k, hx, hk.symm⟩
  have hfull : (1 : ℝ≥0∞) ≤ srwLaw m a (hitBeforeExit F V) := by
    have hSc : srwLaw m a (hitBeforeExit F V)ᶜ = 0 := by
      refine measure_mono_null ?_ hF
      intro x hx n hn hFn
      apply hx
      exact lt_of_le_of_lt (vHitTime_le_of_mem hFn) hn
    calc (1 : ℝ≥0∞) = srwLaw m a univ := measure_univ.symm
      _ = srwLaw m a (hitBeforeExit F V ∪ (hitBeforeExit F V)ᶜ) := by
        rw [Set.union_compl_self]
      _ ≤ srwLaw m a (hitBeforeExit F V) + srwLaw m a (hitBeforeExit F V)ᶜ := measure_union_le _ _
      _ = srwLaw m a (hitBeforeExit F V) := by rw [hSc, add_zero]
  calc ENNReal.ofReal s2 = ENNReal.ofReal s2 * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal s2 * srwLaw m a (hitBeforeExit F V) := mul_le_mul_of_nonneg_left hfull zero_le
    _ ≤ ENNReal.ofReal s2 * ∑' k : ℕ, srwLaw m a (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}) :=
        mul_le_mul_of_nonneg_left hcover zero_le
    _ = ∑' k : ℕ, ENNReal.ofReal s2 * srwLaw m a (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}) :=
        ENNReal.tsum_mul_left.symm
    _ = ∑' k : ℕ, ∫⁻ x in (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}),
        ENNReal.ofReal s2 ∂srwLaw m a := by
        simp only [hconst]
    _ ≤ ∑' k : ℕ, ∫⁻ x in (hitBeforeExit F V ∩ {x | vHitTime F x = (k : ℕ∞)}),
        srwLaw m (x k) (traceSet V (V \ (S' ∪ Θ))) ∂srwLaw m a := hlow
    _ = srwLaw m a (hitBeforeExit F V ∩ {x | ∃ k : ℕ, vHitTime F x = (k : ℕ∞) ∧
        pathShift k x ∈ traceSet V (V \ (S' ∪ Θ))}) := hSM.symm
    _ ≤ srwLaw m a (traceSet V (V \ (S' ∪ Θ))) := measure_mono hincl

#print axioms MatedCRT.TraceFrom68.trace_bound_of_exit_bound

end TraceFrom68

end MatedCRT
