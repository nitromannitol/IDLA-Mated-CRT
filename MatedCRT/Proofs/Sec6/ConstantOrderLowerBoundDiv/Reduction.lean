import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Steps.Sec6.ConstantOrderLowerBound
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Lemma 6.8, Step 1: reduction to walks started on `V^ε(∂B_{(4/3)𝐫_z}(z))` (lines 2527-2528)

`prob_stay_le_of_crossing`: let `O` be open (`O = B_{(4/3)𝐫_z}(z)`), with the cell of `a` meeting `O`, and such that
every vertex outside `U` (the walk has exited) and every vertex outside `I` (a set which the walk exits almost surely)
has a cell disjoint from `cl O`. A walk along intersecting cells which stays in `A` until it exits `U` then visits
`V^ε(∂O)`, at a time before it exits `U` and hence at a vertex of `A`, and from there on it stays in `A` until it exits
`U`. The strong Markov property (`SrwHitDecompositionStep`) bounds the probability of this by the supremum over the
starting points `b ∈ V^ε(∂O) ∩ A`.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

namespace ConstantOrderDiv

/-- A preconnected set meeting the open set `O` and its complement meets `∂O` (as in
`ConstantOrder.IsPreconnected.inter_frontier_nonempty_of_isOpen`). -/
theorem preconnected_inter_frontier_nonempty {α : Type*} [TopologicalSpace α] {s O : Set α}
    (hs : IsPreconnected s) (hO : IsOpen O) (h1 : (s ∩ O).Nonempty) (h2 : (s \ O).Nonempty) :
    (s ∩ frontier O).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hcover : s ⊆ O ∪ (closure O)ᶜ := by
    intro y hy
    by_cases hyO : y ∈ O
    · exact Or.inl hyO
    · refine Or.inr fun hcl => ?_
      have hmem : y ∈ s ∩ frontier O := ⟨hy, by rw [hO.frontier_eq]; exact ⟨hcl, hyO⟩⟩
      rw [hcon] at hmem
      exact hmem
  have h2' : (s ∩ (closure O)ᶜ).Nonempty := by
    obtain ⟨y, hy, hyO⟩ := h2
    exact ⟨y, hy, (hcover hy).resolve_left hyO⟩
  obtain ⟨y, -, hyO, hycl⟩ := hs O (closure O)ᶜ hO isClosed_closure.isOpen_compl hcover h1 h2'
  exact hycl (subset_closure hyO)

theorem cell_isPreconnected' {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- **Crossing lemma for cells.** A path along intersecting cells from a cell meeting the open set `O` to a cell
disjoint from `cl O` visits, strictly before, a vertex whose cell meets `∂O`. -/
theorem exists_cell_meets_frontier' {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {O : Set ℂ} (hO : IsOpen O)
    {x : ℕ → ℤ} (hadj : ∀ n, x (n + 1) = x n ∨ (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (h0 : (cell ε η (x 0) ∩ O).Nonempty) {t : ℕ} (ht : cell ε η (x t) ∩ closure O = ∅) :
    ∃ j < t, (cell ε η (x j) ∩ frontier O).Nonempty := by
  classical
  have htO : ¬ (cell ε η (x t) ∩ O).Nonempty := fun ⟨y, hy, hyO⟩ =>
    (Set.eq_empty_iff_forall_notMem.1 ht) y ⟨hy, subset_closure hyO⟩
  have hex : ∃ j, ¬ (cell ε η (x j) ∩ O).Nonempty := ⟨t, htO⟩
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := Nat.exists_eq_succ_of_ne_zero fun h0' => by
    have hs := Nat.find_spec hex
    rw [h0'] at hs
    exact hs h0
  have hle := Nat.find_min' hex htO
  rw [hi] at hle
  have hin : (cell ε η (x i) ∩ O).Nonempty := not_not.1 (Nat.find_min hex (by rw [hi]; omega))
  have hout := Nat.find_spec hex
  rw [hi] at hout
  rcases hadj i with heq | ⟨p, hp1, hp2⟩
  · exact absurd (by rw [heq]; exact hin) hout
  · have hC := IsPreconnected.union p hp1 hp2 (cell_isPreconnected' hη (x i)) (cell_isPreconnected' hη (x (i + 1)))
    obtain ⟨y, hyC, hyF⟩ := preconnected_inter_frontier_nonempty hC hO
      (hin.mono (inter_subset_inter_left O subset_union_left))
      ⟨p, Or.inr hp2, fun hpO => hout ⟨p, hp2, hpO⟩⟩
    rcases hyC with hy | hy
    · exact ⟨i, by omega, y, hy, hyF⟩
    · refine ⟨i + 1, lt_of_le_of_ne hle fun hit => ?_, y, hy, hyF⟩
      rw [hit] at hy
      exact (Set.eq_empty_iff_forall_notMem.1 ht) y ⟨hy, frontier_subset_closure hyF⟩

open Classical in
theorem vExitTime_ne_top_iff {W : Set ℤ} {y : ℕ → ℤ} : vExitTime W y ≠ ⊤ ↔ ∃ n, y n ∉ W := by
  unfold vExitTime
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => ENat.natCast_ne_top _⟩
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

theorem measurableSet_stay (U A : Set ℤ) :
    MeasurableSet {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} := by
  have : {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} =
      ⋂ n : ℕ, ({x : ℕ → ℤ | (n : ℕ∞) < vExitTime U x}ᶜ ∪ (fun x : ℕ → ℤ => x n) ⁻¹' A) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_preimage]
    exact forall_congr' fun n => imp_iff_not_or
  rw [this]
  exact MeasurableSet.iInter fun n => (measurableSet_lt_vExitTime U n).compl.union
    ((measurable_pi_apply n) (Set.to_countable A).measurableSet)

/-- **Step 1** (lines 2527-2528): the strong Markov property at the first visit to `V^ε(∂O)`. -/
theorem prob_stay_le_of_crossing (hW : SrwHitDecompositionStep) {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) {U A I : Set ℤ} {O : Set ℂ} (hO : IsOpen O) {a : ℤ} {c : ℝ≥0∞}
    (hadj : ∀ᵐ x ∂srwLaw m a, ∀ n, x (n + 1) = x n ∨ (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hexit : srwLaw m a {x | vExitTime I x = ⊤} = 0)
    (hIO : ∀ k ∉ I, cell ε η k ∩ closure O = ∅) (hUO : ∀ k ∉ U, cell ε η k ∩ closure O = ∅)
    (ha : (cell ε η a ∩ O).Nonempty)
    (hb : ∀ b ∈ cellVertices ε η (frontier O) ∩ A,
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ c) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ c := by
  classical
  set F : Set (ℕ → ℤ) := {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A}
  set Bz := cellVertices ε η (frontier O)
  set B := Bz ∩ A
  set HD : Set (ℕ → ℤ) := {x | ∃ n : ℕ, x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F}
  have hgood : ∀ᵐ x ∂srwLaw m a, x ∈ F → x ∈ HD := by
    have hτ : ∀ᵐ x ∂srwLaw m a, vExitTime I x ≠ ⊤ := by
      rw [ae_iff]
      simpa only [ne_eq, not_not] using hexit
    filter_upwards [hadj, hτ, srwLaw_ae_start m a] with x hxadj hxτ hx0 hxF
    obtain ⟨t, ht⟩ := vExitTime_ne_top_iff.1 hxτ
    have h0 : (cell ε η (x 0) ∩ O).Nonempty := by rw [hx0]; exact ha
    obtain ⟨j, -, hj⟩ := exists_cell_meets_frontier' hη hO hxadj h0 (hIO _ ht)
    have hexB : ∃ j, x j ∈ Bz := ⟨j, hj⟩
    set n := Nat.find hexB
    have hnB : x n ∈ Bz := Nat.find_spec hexB
    have hU : ∀ i ≤ n, x i ∈ U := by
      intro i hi
      by_contra hiU
      obtain ⟨j', hj'i, hj'⟩ := exists_cell_meets_frontier' hη hO hxadj h0 (hUO _ hiU)
      exact Nat.find_min hexB (lt_of_lt_of_le hj'i hi) hj'
    have hnU : (n : ℕ∞) < vExitTime U x := lt_vExitTime_iff'.2 hU
    refine ⟨n, ⟨hnB, hxF n hnU⟩, fun j hj hjB => Nat.find_min hexB hj hjB.1, ?_⟩
    intro i hi
    have hi' : ∀ j ≤ i, x (n + j) ∈ U := fun j hj => lt_vExitTime_iff'.1 hi j hj
    refine hxF (n + i) (lt_vExitTime_iff'.2 fun j hj => ?_)
    by_cases hjn : j ≤ n
    · exact hU j hjn
    · have := hi' (j - n) (by omega)
      rwa [show n + (j - n) = j by omega] at this
  calc srwLaw m a F ≤ srwLaw m a HD := measure_mono_ae hgood
    _ ≤ c := hW m a B F c (measurableSet_stay U A) hb

end ConstantOrderDiv

end MatedCRT
