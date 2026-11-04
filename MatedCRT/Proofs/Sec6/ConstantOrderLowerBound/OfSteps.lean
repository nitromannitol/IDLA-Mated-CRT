import MatedCRT.Steps.Sec6.ConstantOrderLowerBound
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Steps.Infra.MatingOfTrees

/-!
# Lemma 6.7 from Lemma 6.8 (proof of lines 2449-2461)

* `exists_cell_meets_frontier`: a walk along edges of `𝒢^ε` from a vertex whose cell meets an open set `O` to a
  vertex whose cell does not meet `O` passes through a vertex whose cell meets `∂O` (cells are connected, the cells
  of adjacent vertices intersect).
* `constantOrderLowerBound_core`: deterministic given the map; a walk from `a ∈ cl(Θ)` which never visits
  `U \ (S ∪ Θ)` before exiting `U = V^ε(Θ̄ + B_r)` hits `V^ε(∂(Θ̄ + B_{r/2}))` and from there exits `U \ Θ` through
  `A = S \ Θ`; the strong Markov property and Lemma 6.8 bound the probability of this by `1 - s₂`.
* `constantOrderLowerBound_of_steps`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### "With probability tending to `1`" -/

theorem ProbTendsToOne.inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : ProbTendsToOne P E) (hF : ProbTendsToOne P F) : ProbTendsToOne P fun ε => E ε ∩ F ε := by
  unfold ProbTendsToOne at *
  have h := hE.add hF
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) fun ε => ?_
  simp only [compl_inter]
  exact measure_union_le _ _

theorem probTendsToOne_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Set Ω}
    (hG : ∀ᵐ ω ∂P, ω ∈ G) : ProbTendsToOne P fun _ => G := by
  unfold ProbTendsToOne
  have h : P Gᶜ = 0 := ae_iff.1 hG
  simp only [h]
  exact tendsto_const_nhds

theorem ProbTendsToOne.mono_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : ProbTendsToOne P E) (hEF : ∀ ε > 0, E ε ⊆ F ε) : ProbTendsToOne P F :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (Eventually.of_forall fun _ => zero_le)
    (eventually_nhdsWithin_of_forall fun ε hε => measure_mono (compl_subset_compl.2 (hEF ε hε)))

namespace ConstantOrder

/-! ### Cells -/

theorem cell_nonempty {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty :=
  ⟨η (ε * k), ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

theorem cell_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) : IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

theorem cells_inter_of_cellMult_ne_zero {ε : ℝ} {η : ℝ → ℂ} {j k : ℤ} (h : cellMult ε η j k ≠ 0) :
    (cell ε η j ∩ cell ε η k).Nonempty := by
  unfold cellMult at h
  split_ifs at h with hjk
  · exact absurd rfl h
  · obtain ⟨C, hC, -⟩ := Set.nonempty_of_ncard_ne_zero h
    obtain ⟨y, hy, -⟩ := hC
    exact ⟨y, hy⟩

theorem cellVertices_mono {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ ⟨p, hp1, hp2⟩ => ⟨p, hp1, h hp2⟩

theorem cell_inter_fillCells_of_mem_vClosure {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {Θ : Set ℤ} {a : ℤ}
    (ha : a ∈ vClosure m Θ) : (cell ε η a ∩ fillCells ε η Θ).Nonempty := by
  rcases ha with ha | ⟨-, a', ha', hm⟩
  · obtain ⟨p, hp⟩ := cell_nonempty hε η a
    exact ⟨p, hp, mem_iUnion₂.2 ⟨a, ha, hp⟩⟩
  · obtain ⟨p, hp1, hp2⟩ := hcell _ _ hm
    exact ⟨p, hp2, mem_iUnion₂.2 ⟨a', ha', hp1⟩⟩

theorem thickening_subset_ball {Θb : Set ℂ} {ρ δ : ℝ} (h : closure Θb ⊆ ball 0 (ρ / 2)) (hδ : δ ≤ ρ / 2) :
    thickening δ Θb ⊆ ball 0 ρ := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  have hz' := h (subset_closure hz)
  rw [mem_ball, dist_zero_right] at hz' ⊢
  rw [dist_eq_norm] at hyz
  have := norm_sub_norm_le y z
  linarith

/-! ### Crossing the frontier -/

theorem IsPreconnected.inter_frontier_nonempty_of_isOpen {α : Type*} [TopologicalSpace α] {s O : Set α}
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

/-- A walk along edges of `𝒢^ε` from a vertex whose cell meets the open set `O` to a vertex whose cell does not meet
`O` visits a vertex whose cell meets `∂O` (for a map `m` whose adjacent vertices have intersecting cells; for the map
of Definition 1.1 this is `AdjacentCellsMeetAeStep`, MatedCRT/Steps/Infra/MatingOfTrees.lean). -/
theorem exists_cell_meets_frontier {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {O : Set ℂ}
    (hO : IsOpen O) {x : ℕ → ℤ} (hadj : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (h0 : (cell ε η (x 0) ∩ O).Nonempty) {t : ℕ} (ht : ¬ (cell ε η (x t) ∩ O).Nonempty) :
    ∃ j ≤ t, (cell ε η (x j) ∩ frontier O).Nonempty := by
  classical
  have hex : ∃ j, ¬ (cell ε η (x j) ∩ O).Nonempty := ⟨t, ht⟩
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := Nat.exists_eq_succ_of_ne_zero fun h0' => by
    have hs := Nat.find_spec hex
    rw [h0'] at hs
    exact hs h0
  have hle := Nat.find_min' hex ht
  rw [hi] at hle
  have hin : (cell ε η (x i) ∩ O).Nonempty := not_not.1 (Nat.find_min hex (by rw [hi]; omega))
  have hout := Nat.find_spec hex
  rw [hi] at hout
  rcases hadj i with heq | hm
  · exact absurd (by rw [heq]; exact hin) hout
  · obtain ⟨p, hp1, hp2⟩ := hcell _ _ hm
    have hC := IsPreconnected.union p hp1 hp2 (cell_isPreconnected hη (x i)) (cell_isPreconnected hη (x (i + 1)))
    obtain ⟨q, hq⟩ := cell_nonempty hε η (x (i + 1))
    obtain ⟨y, hyC, hyF⟩ := IsPreconnected.inter_frontier_nonempty_of_isOpen hC hO
      (hin.mono (inter_subset_inter_left O subset_union_left)) ⟨q, Or.inr hq, fun hqO => hout ⟨q, hq, hqO⟩⟩
    rcases hyC with hy | hy
    · exact ⟨i, by omega, y, hy, hyF⟩
    · exact ⟨i + 1, hle, y, hy, hyF⟩

/-! ### Exit times -/

open Classical in
theorem lt_vExitTime_iff {W : Set ℤ} {y : ℕ → ℤ} {i : ℕ} : (i : ℕ∞) < vExitTime W y ↔ ∀ j ≤ i, y j ∈ W := by
  unfold vExitTime
  split_ifs with h
  · rw [Nat.cast_lt]
    constructor
    · intro hi j hj
      exact not_not.1 (Nat.find_min h (lt_of_le_of_lt hj hi))
    · intro hall
      by_contra hle
      exact Nat.find_spec h (hall _ (not_lt.1 hle))
  · refine ⟨fun _ j _ => not_not.1 fun hj => h ⟨j, hj⟩, fun _ => ENat.natCast_lt_top i⟩

open Classical in
theorem exists_of_vExitTime_ne_top {W : Set ℤ} {y : ℕ → ℤ} (h : vExitTime W y ≠ ⊤) :
    ∃ t, y t ∉ W ∧ ∀ j < t, y j ∈ W := by
  unfold vExitTime at h
  split_ifs at h with hex
  · exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_not.1 (Nat.find_min hex hj)⟩
  · exact absurd rfl h

theorem measurableSet_forall_lt_vExitTime (W A : Set ℤ) :
    MeasurableSet {y : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W y → y n ∈ A} := by
  have : {y : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W y → y n ∈ A} =
      ⋂ n : ℕ, (fun y : ℕ → ℤ => fun j : Fin (n + 1) => y j) ⁻¹'
        {z | (∀ j : Fin (n + 1), z j ∈ W) → z (Fin.last n) ∈ A} := by
    ext y
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, Fin.val_last, lt_vExitTime_iff]
    constructor
    · intro h n hz
      exact h n fun j hj => hz ⟨j, by omega⟩
    · intro h n hz
      exact h n fun j => hz j (Nat.lt_succ_iff.1 j.is_lt)
  rw [this]
  exact MeasurableSet.iInter fun n => (Set.to_countable _).measurableSet.preimage
    (Measurable.of_eval fun j => measurable_pi_apply _)

/-! ### The core estimate -/

/-- **Proof of Lemma 6.7 from Lemma 6.8, given the map.** `U` plays `V^ε(Θ̄ + B_r)` and `O` plays `Θ̄ + B_{r/2}`. -/
theorem constantOrderLowerBound_core (hW : SrwHitDecompositionStep) (hN : SrwAeAdjacentStep)
    {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {Θ S' U : Set ℤ} {O : Set ℂ} {r L s₂ : ℝ} {a : ℤ}
    (hO : IsOpen O) (hΘO : fillCells ε η Θ ⊆ O) (hOU : cellVertices ε η (closure O) ⊆ U) (hUfin : U.Finite)
    (hexit : ∀ b : ℤ, srwLaw m b {x | vExitTime (interiorCellVertices ε η O) x = ⊤} = 0)
    (h68 : ∀ A ⊆ U \ Θ, (∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < L) →
      ∀ b ∈ cellVertices ε η (frontier O), srwLaw m b
        {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (U \ Θ) x → x n ∈ A} ≤ ENNReal.ofReal (1 - s₂))
    (hs₂ : 0 ≤ s₂) (hs₂1 : s₂ ≤ 1) (ha : a ∈ vClosure m Θ) (hS' : S' ⊆ U)
    (hcard : ((S' \ Θ).ncard : ℝ) < L) :
    ENNReal.ofReal s₂ ≤
      srwLaw m a {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime U x ∧ x n ∈ U \ (S' ∪ Θ)} := by
  set μ := srwLaw m a
  set E : Set (ℕ → ℤ) := {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime U x ∧ x n ∈ U \ (S' ∪ Θ)} with hE
  set B := cellVertices ε η (frontier O) with hB
  set F : Set (ℕ → ℤ) := {y | ∀ n : ℕ, (n : ℕ∞) < vExitTime (U \ Θ) y → y n ∈ S' \ Θ} with hF
  set N1 : Set (ℕ → ℤ) := {x | ¬ (x 0 = a ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)} with hN1
  set N2 : Set (ℕ → ℤ) := {x | vExitTime (interiorCellVertices ε η O) x = ⊤} with hN2
  set H : Set (ℕ → ℤ) := {x | ∃ n : ℕ, x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F} with hH
  have hBU : B ⊆ U := (cellVertices_mono frontier_subset_closure).trans hOU
  have hVU : cellVertices ε η O ⊆ U := (cellVertices_mono subset_closure).trans hOU
  have hAfin : (S' \ Θ).Finite := hUfin.subset fun y hy => hS' hy.1
  have hHle : μ H ≤ ENNReal.ofReal (1 - s₂) :=
    hW m a B F _ (measurableSet_forall_lt_vExitTime _ _) fun b hb =>
      h68 (S' \ Θ) (fun y hy => ⟨hS' hy.1, hy.2⟩)
        (fun z => lt_of_le_of_lt (by exact_mod_cast Set.ncard_inter_le_ncard_left _ _ hAfin) hcard) b hb
  have hN1z : μ N1 = 0 := ae_iff.1 ((srwLaw_ae_start m a).and (hN m a))
  have hN2z : μ N2 = 0 := hexit a
  have hsub : Eᶜ ⊆ N1 ∪ N2 ∪ H := by
    intro x hx
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hN1x, hN2x⟩, hHx⟩ := hcon
    have hgood : x 0 = a ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 :=
      not_not.1 hN1x
    obtain ⟨t, ht, hbefore⟩ := exists_of_vExitTime_ne_top (W := interiorCellVertices ε η O) hN2x
    have hexB : ∃ j, x j ∈ B ∧ j ≤ t := by
      by_cases hxt : x t ∈ cellVertices ε η O
      · exact ⟨t, not_not.1 fun hB' => ht ⟨hxt, hB'⟩, le_rfl⟩
      · have h0 : (cell ε η (x 0) ∩ O).Nonempty := by
          rw [hgood.1]
          obtain ⟨p, hp1, hp2⟩ := cell_inter_fillCells_of_mem_vClosure hε hcell ha
          exact ⟨p, hp1, hΘO hp2⟩
        obtain ⟨j, hjt, hj⟩ := exists_cell_meets_frontier hε hη hcell hO hgood.2 h0 hxt
        exact ⟨j, hj, hjt⟩
    classical
    obtain ⟨j, hjB, hjt⟩ := hexB
    have hex' : ∃ j, x j ∈ B := ⟨j, hjB⟩
    obtain ⟨n, hnB, hmin, hnj⟩ : ∃ n, x n ∈ B ∧ (∀ i < n, x i ∉ B) ∧ n ≤ j :=
      ⟨Nat.find hex', Nat.find_spec hex', fun i hi => Nat.find_min hex' hi, Nat.find_min' hex' hjB⟩
    have hU : ∀ i ≤ n, x i ∈ U := by
      intro i hi
      rcases lt_or_eq_of_le hi with hi | hi
      · exact hVU (hbefore i (lt_of_lt_of_le hi (hnj.trans hjt))).1
      · rw [hi]; exact hBU hnB
    apply hHx
    refine ⟨n, hnB, hmin, ?_⟩
    intro i hi
    rw [lt_vExitTime_iff] at hi
    have hi' : ∀ j ≤ i, x (n + j) ∈ U \ Θ := fun j hj => hi j hj
    have hlt : ((n + i : ℕ) : ℕ∞) < vExitTime U x := by
      rw [lt_vExitTime_iff]
      intro j hj
      by_cases hjn : j ≤ n
      · exact hU j hjn
      · have hmem := (hi' (j - n) (by omega)).1
        rwa [show n + (j - n) = j by omega] at hmem
    have hnot : x (n + i) ∉ U \ (S' ∪ Θ) := fun hmem => hx ⟨n + i, hlt, hmem⟩
    have hxi := hi' i le_rfl
    refine ⟨?_, hxi.2⟩
    by_contra hS''
    exact hnot ⟨hxi.1, fun h => h.elim hS'' hxi.2⟩
  have hEc : μ Eᶜ ≤ ENNReal.ofReal (1 - s₂) :=
    calc μ Eᶜ ≤ μ (N1 ∪ N2 ∪ H) := measure_mono hsub
      _ ≤ μ (N1 ∪ N2) + μ H := measure_union_le _ _
      _ ≤ μ N1 + μ N2 + μ H := add_le_add (measure_union_le _ _) le_rfl
      _ = μ H := by rw [hN1z, hN2z, zero_add, zero_add]
      _ ≤ ENNReal.ofReal (1 - s₂) := hHle
  have htot : (1 : ℝ≥0∞) ≤ μ E + μ Eᶜ :=
    calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
      _ = μ (E ∪ Eᶜ) := by rw [union_compl_self]
      _ ≤ μ E + μ Eᶜ := measure_union_le _ _
  have hsum : ENNReal.ofReal s₂ + ENNReal.ofReal (1 - s₂) = 1 := by
    rw [← ENNReal.ofReal_add hs₂ (by linarith)]
    simp
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 - s₂)) ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal s₂ + ENNReal.ofReal (1 - s₂) = 1 := hsum
    _ ≤ μ E + μ Eᶜ := htot
    _ ≤ μ E + ENNReal.ofReal (1 - s₂) := add_le_add le_rfl hEc

end ConstantOrder

open ConstantOrder in
/-- **Lemma 6.7 from Lemma 6.8** (proof of lines 2449-2461), with the same `ω₀`, `s₁`, `s₂` and with
`𝛅 ∧ ρ/4` in place of the `𝛅` of Lemma 6.8. -/
theorem constantOrderLowerBound_of_steps (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
    (hW : SrwHitDecompositionStep) (hN : SrwAeAdjacentStep) (hF : CellVerticesBallFiniteStep 𝒮)
    (hE : WalkExitsStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβ
  obtain ⟨ω₀, hω₀, h⟩ := h68 γ hγ hγ2 ρ hρ hρ1 βm hβ
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h'⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hP⟩ := h' Ω S hS
  refine ⟨fun ω => min (dd ω) (ρ / 4), hdd.min measurable_const, fun ω => lt_min (hddpos ω) (by positivity), ?_⟩
  have hcont : ∀ᵐ ω ∂S.P, ω ∈ {ω | Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty} :=
    (hS.isAreaParametrized.and (hcell γ hγ hγ2 Ω S hS)).mono fun ω hω => ⟨hω.1.1, hω.2⟩
  have hall := ((hP.inter (hF γ hγ hγ2 ρ hρ hρ1 Ω S hS)).inter
    (hE γ hγ hγ2 ρ s₀ hρ hρ1 hs₀ Ω S hS)).inter (probTendsToOne_of_ae hcont)
  refine hall.mono_pos fun ε hε ω hω => ?_
  obtain ⟨⟨⟨h68ω, hfinω⟩, hexitω⟩, hcontω⟩ := hω
  simp only [mem_ofPred_eq] at h68ω hfinω hexitω hcontω ⊢
  intro r hr1 hr2 Θ hΘ1 hΘ2 a ha S' hS' hcard
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hrρ : r ≤ ρ / 4 := hr2.trans (min_le_right _ _)
  have hthick : ∀ δ, δ ≤ ρ / 2 → thickening δ (fillCells ε (S.η ω) Θ) ⊆ ball 0 ρ :=
    fun δ hδ => thickening_subset_ball hΘ1 hδ
  exact constantOrderLowerBound_core hW hN hε.le hcontω.1 (hcontω.2 ε hε)
    (U := cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)))
    (O := thickening (r / 2) (fillCells ε (S.η ω) Θ)) isOpen_thickening
    (self_subset_thickening (by linarith) _)
    (cellVertices_mono ((closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' hr (by linarith) _)))
    (hfinω.subset (cellVertices_mono (hthick r (by linarith))))
    (fun b => hexitω _ isOpen_thickening (hΘ2.trans (self_subset_thickening (by linarith) _))
      (hthick _ (by linarith)) b)
    (h68ω r hr1 (hr2.trans (min_le_left _ _)) Θ hΘ1 hΘ2) hs₂.le hs₂1.le ha hS' hcard

end MatedCRT
