import MarkovProcess.Path.RelativeHitting
import MarkovProcess.Path.StoppedValueMeasurability
import MarkovProcess.Trajectory.StoppingLtTop
import MatedCRT.FirstPass.Derived.BrownianTemplateEvent

/-!
# Successive visit times of a closed set by a continuous path

For a stopping time `T` of the canonical filtration on continuous paths and a closed set `F`, the
first hitting time of `F` at or after `T` is again a stopping time: the event that it is at most
`t` is the event that the path meets `F` between `T` and `t`
(`ContinuousPath.measurableSet_hitsSetBetween`), the infimum being attained because the set of
times after `T` at which the path lies in `F` is closed.

Iterating with a unit delay gives the successive visit times of `F`: `σ₀` is the first hitting
time of `F`, and `σ_{j+1}` is the first hitting time of `F` at or after `σ_j + 1`. They are
stopping times, consecutive ones are at least one unit of time apart, the path lies in `F` at
every finite visit time, and all of them are finite for a path that returns to `F` at
arbitrarily large times. These are the restart times of the geometric-trials argument for the
divergence of an additive functional of a recurrent path.

## Main results
* `isStoppingTime_firstHitAfter`, `firstHitAfter_le_iff`, `le_firstHitAfter`,
  `mem_of_firstHitAfter_lt_top`, `firstHitAfter_lt_top`.
* `visitTime`, `isStoppingTime_visitTime`, `visitTime_add_one_le`,
  `monotone_visitTime_measurableSpace`, `mem_of_visitTime_lt_top`, `visitTime_lt_top`,
  `untopD_visitTime_add_one_le`.
* `measurable_shift_untopD_stoppedSpace`: the path shifted at a stopping time `τ` is measurable
  from the stopped sigma-algebra at `τ + s` to the canonical sigma-algebra at time `s`;
  `measurableSet_shift_visitTime_preimage`: an event of the path shifted at the `j`-th visit
  time, depending on its first unit of time, is measurable at the `(j + 1)`-st visit time.
-/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

variable {α : Type*} [PseudoMetricSpace α]

open Classical in
/-- The first time at or after `T ω` at which the path `ω` lies in `F`; it is `⊤` when the path
does not visit `F` after `T ω`. -/
noncomputable def firstHitAfter (T : ContinuousPath α → WithTop ℝ≥0) (F : Set α)
    (ω : ContinuousPath α) : WithTop ℝ≥0 :=
  if ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F then
    ((sInf {s : ℝ≥0 | T ω ≤ s ∧ ω s ∈ F} : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

/-- The times at or after `T ω` at which a path lies in a closed set form a closed set. -/
theorem isClosed_setOf_le_and_mem (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α}
    (hF : IsClosed F) (ω : ContinuousPath α) :
    IsClosed {s : ℝ≥0 | T ω ≤ s ∧ ω s ∈ F} := by
  have h1 : IsClosed {s : ℝ≥0 | T ω ≤ (s : WithTop ℝ≥0)} := by
    by_cases htop : T ω = ⊤
    · have hempty : {s : ℝ≥0 | T ω ≤ (s : WithTop ℝ≥0)} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun s (hs : T ω ≤ (s : WithTop ℝ≥0)) => by
          rw [htop] at hs
          exact WithTop.coe_ne_top (top_le_iff.1 hs)
      rw [hempty]
      exact isClosed_empty
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 htop
      have hIci : {s : ℝ≥0 | T ω ≤ (s : WithTop ℝ≥0)} = Ici a := by
        ext s
        show T ω ≤ (s : WithTop ℝ≥0) ↔ a ≤ s
        rw [← ha]
        exact WithTop.coe_le_coe
      rw [hIci]
      exact isClosed_Ici
  exact h1.inter (hF.preimage ω.continuous)

/-- When the path visits the closed set `F` after `T ω`, the first such time is attained. -/
theorem exists_firstHitAfter_eq_coe (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α}
    (hF : IsClosed F) (ω : ContinuousPath α) (h : ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F) :
    ∃ s : ℝ≥0, firstHitAfter T F ω = s ∧ T ω ≤ s ∧ ω s ∈ F := by
  refine ⟨sInf {s : ℝ≥0 | T ω ≤ s ∧ ω s ∈ F}, ?_,
    (isClosed_setOf_le_and_mem T hF ω).csInf_mem h (OrderBot.bddBelow _)⟩
  simp only [firstHitAfter, h, ↓reduceIte]

/-- Without a visit of `F` after `T ω`, the first hitting time is infinite. -/
theorem firstHitAfter_eq_top (T : ContinuousPath α → WithTop ℝ≥0) (F : Set α)
    (ω : ContinuousPath α) (h : ¬ ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F) :
    firstHitAfter T F ω = ⊤ := by
  simp only [firstHitAfter, h, ↓reduceIte]

/-- The first hitting time of a closed set after `T` is at most `t` exactly when the path meets
the set between `T` and `t`. -/
theorem firstHitAfter_le_iff (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α}
    (hF : IsClosed F) (ω : ContinuousPath α) (t : ℝ≥0) :
    firstHitAfter T F ω ≤ t ↔ ∃ s : ℝ≥0, T ω ≤ s ∧ s ≤ t ∧ ω s ∈ F := by
  by_cases h : ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F
  · obtain ⟨s₀, hs₀, hTs₀, hs₀F⟩ := exists_firstHitAfter_eq_coe T hF ω h
    rw [hs₀, WithTop.coe_le_coe]
    refine ⟨fun hle => ⟨s₀, hTs₀, hle, hs₀F⟩, ?_⟩
    rintro ⟨s, hTs, hst, hsF⟩
    have hmin : sInf {s : ℝ≥0 | T ω ≤ s ∧ ω s ∈ F} ≤ s :=
      csInf_le (OrderBot.bddBelow _) ⟨hTs, hsF⟩
    have hs₀' : firstHitAfter T F ω = ((sInf {s : ℝ≥0 | T ω ≤ s ∧ ω s ∈ F} : ℝ≥0) :
        WithTop ℝ≥0) := by
      simp only [firstHitAfter, h, ↓reduceIte]
    rw [hs₀', WithTop.coe_eq_coe] at hs₀
    rw [← hs₀]
    exact hmin.trans hst
  · rw [firstHitAfter_eq_top T F ω h]
    refine ⟨fun hle => absurd (top_le_iff.1 hle) WithTop.coe_ne_top, ?_⟩
    rintro ⟨s, hTs, -, hsF⟩
    exact absurd ⟨s, hTs, hsF⟩ h

/-- The first hitting time after `T` is at least `T`. -/
theorem le_firstHitAfter (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α} (hF : IsClosed F)
    (ω : ContinuousPath α) : T ω ≤ firstHitAfter T F ω := by
  by_cases h : ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F
  · obtain ⟨s₀, hs₀, hTs₀, -⟩ := exists_firstHitAfter_eq_coe T hF ω h
    rw [hs₀]
    exact hTs₀
  · rw [firstHitAfter_eq_top T F ω h]
    exact le_top

/-- At a finite first hitting time of a closed set, the path lies in the set. -/
theorem mem_of_firstHitAfter_lt_top (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α}
    (hF : IsClosed F) (ω : ContinuousPath α) (hlt : firstHitAfter T F ω < ⊤) :
    ω ((firstHitAfter T F ω).untopD 0) ∈ F := by
  by_cases h : ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F
  · obtain ⟨s₀, hs₀, -, hs₀F⟩ := exists_firstHitAfter_eq_coe T hF ω h
    rw [hs₀, WithTop.untopD_coe]
    exact hs₀F
  · rw [firstHitAfter_eq_top T F ω h] at hlt
    exact absurd hlt (lt_irrefl _)

/-- The first hitting time after a finite time is finite for a path that visits `F` at
arbitrarily large times. -/
theorem firstHitAfter_lt_top (T : ContinuousPath α → WithTop ℝ≥0) {F : Set α}
    (hF : IsClosed F) (ω : ContinuousPath α) (hT : T ω < ⊤)
    (hrec : ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ ω s ∈ F) : firstHitAfter T F ω < ⊤ := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hT.ne
  obtain ⟨s, has, hsF⟩ := hrec a
  have h : ∃ s : ℝ≥0, T ω ≤ s ∧ ω s ∈ F := ⟨s, by rw [← ha]; exact WithTop.coe_le_coe.2 has, hsF⟩
  obtain ⟨s₀, hs₀, -, -⟩ := exists_firstHitAfter_eq_coe T hF ω h
  rw [hs₀]
  exact WithTop.coe_lt_top s₀

/-- The successive visit times of `F` with unit delay: `visitTime F 0` is the first hitting time
of `F`, and `visitTime F (j + 1)` is the first hitting time of `F` at or after
`visitTime F j + 1`. -/
noncomputable def visitTime (F : Set α) : ℕ → ContinuousPath α → WithTop ℝ≥0
  | 0 => firstHitAfter (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) F
  | j + 1 => firstHitAfter (fun ω => visitTime F j ω + ((1 : ℝ≥0) : WithTop ℝ≥0)) F

/-- Consecutive visit times are at least one unit of time apart. -/
theorem visitTime_add_one_le {F : Set α} (hF : IsClosed F) (j : ℕ) (ω : ContinuousPath α) :
    visitTime F j ω + ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ visitTime F (j + 1) ω := by
  rw [visitTime]
  exact le_firstHitAfter (fun ω => visitTime F j ω + ((1 : ℝ≥0) : WithTop ℝ≥0)) hF ω

/-- The visit times are nondecreasing in the index. -/
theorem visitTime_le_succ {F : Set α} (hF : IsClosed F) (j : ℕ) (ω : ContinuousPath α) :
    visitTime F j ω ≤ visitTime F (j + 1) ω :=
  le_self_add.trans (visitTime_add_one_le hF j ω)

/-- At a finite visit time the path lies in `F`. -/
theorem mem_of_visitTime_lt_top {F : Set α} (hF : IsClosed F) (j : ℕ) (ω : ContinuousPath α)
    (hlt : visitTime F j ω < ⊤) : ω ((visitTime F j ω).untopD 0) ∈ F := by
  cases j with
  | zero =>
    rw [visitTime] at hlt ⊢
    exact mem_of_firstHitAfter_lt_top _ hF ω hlt
  | succ j =>
    rw [visitTime] at hlt ⊢
    exact mem_of_firstHitAfter_lt_top _ hF ω hlt

/-- All visit times are finite for a path that visits `F` at arbitrarily large times. -/
theorem visitTime_lt_top {F : Set α} (hF : IsClosed F) (ω : ContinuousPath α)
    (hrec : ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ ω s ∈ F) : ∀ j : ℕ, visitTime F j ω < ⊤
  | 0 => by
    rw [visitTime]
    exact firstHitAfter_lt_top _ hF ω (WithTop.coe_lt_top 0) hrec
  | j + 1 => by
    rw [visitTime]
    exact firstHitAfter_lt_top _ hF ω
      (WithTop.add_lt_top.2 ⟨visitTime_lt_top hF ω hrec j, WithTop.coe_lt_top 1⟩) hrec

/-- For a path that visits `F` at arbitrarily large times, the finite values of consecutive
visit times are at least one unit of time apart. -/
theorem untopD_visitTime_add_one_le {F : Set α} (hF : IsClosed F) (ω : ContinuousPath α)
    (hrec : ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ ω s ∈ F) (j : ℕ) :
    (visitTime F j ω).untopD 0 + 1 ≤ (visitTime F (j + 1) ω).untopD 0 := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (visitTime_lt_top hF ω hrec j).ne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (visitTime_lt_top hF ω hrec (j + 1)).ne
  have h := visitTime_add_one_le hF j ω
  rw [← ha, ← hb, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← ha, ← hb, WithTop.untopD_coe, WithTop.untopD_coe]
  exact h

variable [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

/-- **The first hitting time of a closed set after a stopping time is a stopping time** of the
canonical filtration. -/
theorem isStoppingTime_firstHitAfter {T : ContinuousPath α → WithTop ℝ≥0}
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) T) {F : Set α}
    (hF : IsClosed F) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) (firstHitAfter T F) := by
  intro t
  have hset : {ω : ContinuousPath α | firstHitAfter T F ω ≤ t} =
      ContinuousPath.hitsSetBetween T t F := by
    ext ω
    exact firstHitAfter_le_iff T hF ω t
  rw [hset]
  exact ContinuousPath.measurableSet_hitsSetBetween T hT t F hF

/-- **The visit times are stopping times** of the canonical filtration. -/
theorem isStoppingTime_visitTime {F : Set α} (hF : IsClosed F) :
    ∀ j : ℕ, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) (visitTime F j)
  | 0 => by
    rw [visitTime]
    exact isStoppingTime_firstHitAfter (isStoppingTime_const _ 0) hF
  | j + 1 => by
    rw [visitTime]
    exact isStoppingTime_firstHitAfter
      (MatedCRT.isStoppingTime_add_const_nnreal (isStoppingTime_visitTime hF j) 1) hF

/-- The stopped sigma-algebras at the successive visit times increase with the index. -/
theorem monotone_visitTime_measurableSpace {F : Set α} (hF : IsClosed F) :
    Monotone fun j : ℕ => (isStoppingTime_visitTime hF j).measurableSpace :=
  monotone_nat_of_le_succ fun j =>
    IsStoppingTime.measurableSpace_mono _ _ fun ω => visitTime_le_succ hF j ω

/-! ### The path shifted at a stopping time -/

/-- For `r ≤ s`, the state of the path at time `τ + r` (read as the state at time `r` on
`{τ = ∞}`) is measurable for the stopped sigma-algebra at `τ + s`. On `{τ < ∞}` it is the
stopped value at `τ + r` of the progressively measurable coordinate process; the event
`{τ = ∞}` does not meet `{τ + s ≤ t}`. -/
theorem measurable_eval_untopD_add {τ : ContinuousPath α → WithTop ℝ≥0}
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) τ) {r s : ℝ≥0}
    (hrs : r ≤ s) :
    Measurable[(MatedCRT.isStoppingTime_add_const_nnreal hτ s).measurableSpace]
      (fun ω : ContinuousPath α => ω ((τ ω).untopD 0 + r)) := by
  intro B hB
  set hρ := MatedCRT.isStoppingTime_add_const_nnreal hτ s with hρ_def
  have hρr := MatedCRT.isStoppingTime_add_const_nnreal hτ r
  have hmono : hρr.measurableSpace ≤ hρ.measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun ω =>
      add_le_add le_rfl (WithTop.coe_le_coe.2 hrs)
  have hD : MeasurableSet[hρ.measurableSpace]
      (stoppedValue (ContinuousPath.coordinateProcess (alpha := α))
        (fun ω => τ ω + (r : WithTop ℝ≥0)) ⁻¹' B) :=
    hmono _ (measurable_stoppedValue
      (ContinuousPath.progMeasurable_coordinateProcess (alpha := α)) hρr hB)
  have hlt : MeasurableSet[hρ.measurableSpace] {ω | τ ω < ⊤} := by
    have h := StoppingTime.measurableSet_stoppingTime_lt_top hρ
    have heq : {ω : ContinuousPath α | τ ω + (s : WithTop ℝ≥0) < ⊤} = {ω | τ ω < ⊤} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.add_lt_top, WithTop.coe_lt_top, and_true]
    rwa [heq] at h
  have htop : MeasurableSet[hρ.measurableSpace]
      ((fun ω : ContinuousPath α => ω r) ⁻¹' B ∩ {ω | τ ω < ⊤}ᶜ) := by
    refine ⟨MeasurableSet.inter ?_ hlt.1.compl, fun i => ?_⟩
    · exact le_iSup (ContinuousPath.canonicalFiltration (alpha := α)) r _
        (ContinuousPath.measurable_coordinateProcess_canonicalFiltration r hB)
    · have hempty : (fun ω : ContinuousPath α => ω r) ⁻¹' B ∩ {ω | τ ω < ⊤}ᶜ ∩
          {ω | τ ω + (s : WithTop ℝ≥0) ≤ i} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => hω.1.2 ?_
        exact lt_of_le_of_lt le_self_add (lt_of_le_of_lt hω.2 (WithTop.coe_lt_top i))
      rw [hempty]
      exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := α) i)
  have heq : (fun ω : ContinuousPath α => ω ((τ ω).untopD 0 + r)) ⁻¹' B =
      (stoppedValue (ContinuousPath.coordinateProcess (alpha := α))
          (fun ω => τ ω + (r : WithTop ℝ≥0)) ⁻¹' B ∩ {ω | τ ω < ⊤}) ∪
        ((fun ω : ContinuousPath α => ω r) ⁻¹' B ∩ {ω | τ ω < ⊤}ᶜ) := by
    ext ω
    by_cases htop : τ ω = ⊤
    · simp [htop]
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 htop
      have h3 : τ ω < ⊤ := lt_top_iff_ne_top.2 htop
      have hval : stoppedValue (ContinuousPath.coordinateProcess (alpha := α))
          (fun ω => τ ω + (r : WithTop ℝ≥0)) ω = ω ((τ ω).untopD 0 + r) := by
        show ω ((τ ω + (r : WithTop ℝ≥0)).untopA) = ω ((τ ω).untopD 0 + r)
        rw [← ha, ← WithTop.coe_add]
        rfl
      constructor
      · intro h
        exact Or.inl ⟨by rw [mem_preimage, hval]; exact h, h3⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · rw [mem_preimage, hval] at h
          exact h
        · exact absurd h3 h
  rw [heq]
  exact (hD.inter hlt).union htop

/-- **The path shifted at a stopping time `τ` is measurable from the stopped sigma-algebra at
`τ + s` to the canonical sigma-algebra at time `s`** (on `{τ = ∞}` the path is not shifted). -/
theorem measurable_shift_untopD_stoppedSpace {τ : ContinuousPath α → WithTop ℝ≥0}
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) τ) (s : ℝ≥0) :
    Measurable[(MatedCRT.isStoppingTime_add_const_nnreal hτ s).measurableSpace,
      ContinuousPath.canonicalFiltration (alpha := α) s]
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap _ (⨆ r : Iic s, MeasurableSpace.comap
    (ContinuousPath.coordinateProcess (alpha := α) (r : ℝ≥0)) ‹MeasurableSpace α›) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun r => ?_
  rw [MeasurableSpace.comap_comp]
  exact (measurable_eval_untopD_add hτ r.2).comap_le

/-- **The trial events at the visit times are measurable at the next visit time**: for an event
`Γ` of the canonical sigma-algebra at time `1`, the event that the path shifted at the `j`-th
visit time lies in `Γ` belongs to the stopped sigma-algebra at the `(j + 1)`-st visit time. -/
theorem measurableSet_shift_visitTime_preimage {F : Set α} (hF : IsClosed F) (j : ℕ)
    {Γ : Set (ContinuousPath α)}
    (hΓ : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) 1] Γ) :
    MeasurableSet[(isStoppingTime_visitTime hF (j + 1)).measurableSpace]
      {ω | ContinuousPath.shift ((visitTime F j ω).untopD 0) ω ∈ Γ} :=
  IsStoppingTime.measurableSpace_mono
    (MatedCRT.isStoppingTime_add_const_nnreal (isStoppingTime_visitTime hF j) 1) _
    (fun ω => visitTime_add_one_le hF j ω) _
    (measurable_shift_untopD_stoppedSpace (isStoppingTime_visitTime hF j) 1 hΓ)

end MatedCRT.KilledOccupation
