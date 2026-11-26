import MatedCRT.FirstPass.Derived.WindowChartBGDiscreteLawIntrinsic
import MatedCRT.FirstPass.Derived.GMS21AnnulusLocality
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonPaths

/-!
# The frozen window law is the law of the walk of the map, frozen

The frozen window law (`frozenWindowLaw`) runs the walk with the weights `frozenWindowMult` of the inside rows. In the
comparison of Berestycki–Gwynne (2020), proof of Lemma 7.21 (written answer MQ-sbl-35, line 21), every neighbour of
an inside cell is retained, so an inside row keeps all its original weights, and the walks with the two weight arrays
agree until the first step out of the inside cells. This file proves the corresponding identity of laws.

* `MatedCRT.FrozenPath.frozenSeq_eq_comp_frozenIdx`: the frozen walk at step `i` is the walk at the frozen index.
* `MatedCRT.FrozenPath.frozenSeq_stoppedPath`: freezing only uses the walk up to its first exit.
* `MatedCRT.FrozenPath.map_frozenSeq_srwLaw_eq_of_rows`: the law of a functional of the frozen walk only depends on
  the rows of the weights at the states of `A` (from `srwLaw_map_stoppedPath_eq_of_rows`).
* `MatedCRT.FrozenPath.frozenWindowLaw_eq_map_srwLaw`: the frozen window law is the law of the walk with the original
  weights from `⌈u/ε⌉`, frozen and drawn in the intrinsic chart, when the inside rows charge retained labels only.
* `MatedCRT.FrozenPath.windowRetained_of_inter_nonempty`: a cell meeting an inside cell is retained, when the curve
  visits the window domain during `[a, b]` only and `ε ≤ min (a - p) (q - b)`.
-/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

namespace FrozenPath

/-! ### The frozen walk -/

theorem frozenSeq_eq_comp_frozenIdx (A : Set ℤ) (x : ℕ → ℤ) (i : ℕ) :
    frozenSeq A x i = x (frozenIdx (fun j => x j ∈ A) i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [frozenSeq, frozenIdx]
    by_cases h : ∀ j ≤ i + 1, x j ∈ A
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      exact ih

theorem coe_le_vExitTime {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (h : ∀ i ≤ n, x i ∈ A) {i : ℕ} (hi : i ≤ n) :
    (i : ℕ∞) ≤ vExitTime A x := by
  classical
  unfold vExitTime
  split_ifs with hex
  · have hle : i ≤ Nat.find hex := by
      by_contra hlt
      exact Nat.find_spec hex (h _ ((not_le.1 hlt).le.trans hi))
    exact_mod_cast hle
  · exact le_top

theorem exists_le_vExitTime_notMem {A : Set ℤ} {x : ℕ → ℤ} {i : ℕ} (hi : x i ∉ A) :
    ∃ k ≤ i, (k : ℕ∞) ≤ vExitTime A x ∧ x k ∉ A := by
  classical
  unfold vExitTime
  split_ifs with hex
  · exact ⟨Nat.find hex, Nat.find_min' hex hi, le_rfl, Nat.find_spec hex⟩
  · exact absurd ⟨i, hi⟩ hex

/-- Freezing only uses the walk up to its first exit from `A`. -/
theorem frozenSeq_eq_of_agree {A : Set ℤ} {x y : ℕ → ℤ}
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ vExitTime A x → y k = x k) : frozenSeq A y = frozenSeq A x := by
  funext i
  induction i with
  | zero =>
    simp only [frozenSeq]
    exact h 0 (by simp)
  | succ i ih =>
    simp only [frozenSeq]
    by_cases hx : ∀ j ≤ i + 1, x j ∈ A
    · have hyx : ∀ j ≤ i + 1, y j = x j := fun j hj => h j (coe_le_vExitTime hx hj)
      have hy : ∀ j ≤ i + 1, y j ∈ A := fun j hj => by
        rw [hyx j hj]
        exact hx j hj
      rw [ite_eq_left hx, ite_eq_left hy, hyx _ le_rfl]
    · have hy : ¬ ∀ j ≤ i + 1, y j ∈ A := by
        intro hy
        obtain ⟨j, hj, hjx⟩ : ∃ j ≤ i + 1, x j ∉ A := by
          by_contra hc
          exact hx fun j hj => by_contra fun hn => hc ⟨j, hj, hn⟩
        obtain ⟨k, hk, hkv, hkA⟩ := exists_le_vExitTime_notMem hjx
        exact hkA (by rw [← h k hkv]; exact hy k (hk.trans hj))
      rw [ite_eq_right hx, ite_eq_right hy]
      exact ih

theorem frozenSeq_stoppedPath (A : Set ℤ) (x : ℕ → ℤ) :
    frozenSeq A (ExitDecomposition.stoppedPath A x) = frozenSeq A x := by
  refine frozenSeq_eq_of_agree fun k hk => ?_
  simp only [ExitDecomposition.stoppedPath, min_eq_right hk, ENat.toNat_natCast]

/-- **Locality of the frozen walk.** The law of a functional of the walk frozen before its first step out of `A` only
depends on the rows `m x ·` for `x ∈ A`. -/
theorem map_frozenSeq_srwLaw_eq_of_rows {A : Set ℤ} {m m' : ℤ → ℤ → ℕ} (h : ∀ x ∈ A, m x = m' x) (a : ℤ)
    {Y : Type*} [MeasurableSpace Y] {F : (ℕ → ℤ) → Y} (hF : Measurable F) :
    (srwLaw m a).map (fun x => F (frozenSeq A x)) = (srwLaw m' a).map (fun x => F (frozenSeq A x)) := by
  have hc : (fun x => F (frozenSeq A x)) = (fun x => F (frozenSeq A x)) ∘ ExitDecomposition.stoppedPath A := by
    funext x
    simp only [Function.comp_apply, frozenSeq_stoppedPath]
  have hm : Measurable fun x => F (frozenSeq A x) := hF.comp (measurable_frozenSeq_const A)
  rw [hc, ← Measure.map_map hm (ExitDecomposition.measurable_stoppedPath A),
    ← Measure.map_map hm (ExitDecomposition.measurable_stoppedPath A), srwLaw_map_stoppedPath_eq_of_rows h a]

/-! ### The frozen window law -/

/-- **The frozen window law is the frozen walk of the map.** On a window with an intrinsic chart whose start cell
`⌈u/ε⌉` is inside, if every inside row of `m` charges retained labels only, the frozen window law is the law of the
walk with weights `m` from `⌈u/ε⌉`, frozen before its first step out of the inside cells and drawn in the chart. -/
theorem frozenWindowLaw_eq_map_srwLaw {a u b p q ε mε : ℝ} (hm : 0 ≤ mε) {m : ℤ → ℤ → ℕ} {η : C(ℝ, ℂ)}
    (hG : WindowGoodIntr a u b η) (h0 : WindowCellInside a u b p q ε η ⌈u / ε⌉)
    (hrow : ∀ i j, WindowCellInside a u b p q ε η i → m i j ≠ 0 → WindowRetained p q ε j) :
    (frozenWindowLaw a u b p q ε hm m η : Measure (ContinuousPath ℂ)) =
      (srwLaw m ⌈u / ε⌉).map fun x => interpPathCM (frozenChartVertex a u b p q ε η) hm
        (frozenSeq {j | WindowCellInside a u b p q ε η j} x) := by
  have hW : ∀ i ∈ {j | WindowCellInside a u b p q ε η j}, frozenWindowMult a u b p q ε η m i = m i := by
    intro i hi
    funext j
    unfold frozenWindowMult
    by_cases hj : WindowRetained p q ε j
    · exact ite_eq_left ⟨hi, hj⟩
    · rw [ite_eq_right fun h => hj h.2]
      by_contra hne
      exact hj (hrow i j hi (Ne.symm hne))
  unfold frozenWindowLaw
  rw [ite_eq_left ⟨hG, h0⟩]
  exact map_frozenSeq_srwLaw_eq_of_rows hW ⌈u / ε⌉ (measurable_interpPathCM _ hm)

/-- **A cell meeting an inside cell is retained**, when the curve visits the window domain during `[a, b]` only and
`ε ≤ min (a - p) (q - b)`. -/
theorem windowRetained_of_inter_nonempty {a u b p q ε : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (hε : 0 < ε) (hεa : ε ≤ a - p) (hεb : ε ≤ q - b)
    (hpre : ∀ t, η t ∈ windowDomain η a u b → t ∈ Icc a b) {i j : ℤ} (hi : WindowCellInside a u b p q ε η i)
    (hij : (cell ε (⇑η) i ∩ cell ε (⇑η) j).Nonempty) : WindowRetained p q ε j := by
  obtain ⟨w, ⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩ := hij
  have hsU : η s ∈ windowDomain η a u b := hG.mem_windowDomain_of_windowCellInside hε hi hs
  have htab : t ∈ Icc a b := hpre t (by rw [hts]; exact hsU)
  have h1 : ε * ((j : ℝ) - 1) ≤ t := ht.1
  have h2 : t ≤ ε * j := ht.2
  have h3 : ε * (j : ℝ) - ε = ε * ((j : ℝ) - 1) := by ring
  constructor
  · linarith [htab.1]
  · linarith [htab.2]

end FrozenPath

end MatedCRT
