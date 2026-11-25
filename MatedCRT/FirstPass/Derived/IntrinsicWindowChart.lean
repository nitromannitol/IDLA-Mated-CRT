import MatedCRT.FirstPass.Derived.IntrinsicWindowReembedding
import MatedCRT.FirstPass.Derived.WindowChartBG

/-!
# The intrinsic inverse chart of a window

For a window `(a, u, b)` of a curve `η` with window domain `U` (the component containing `η(u)` of the interior of
`η([a, b])`), this file builds an inverse chart of `U` which is read off the intrinsic curve-decorated surface over any
set of times containing `[a, b]` (for the proof of Lemma 7.21 of Berestycki–Gwynne (2020),
arXiv:2003.10320):

* `v = openWindowDiscInv`: the inverse on `U` of the normalized conformal map `φ` of the open disc onto `U` with
  `φ(0) = η(u)`, `φ'(0) > 0` (`openWindowDiscMap`);
* `α' = windowEntryIntr`: the infimum of the rational times `r ∈ [a, u]` such that the rational visits of `η` to `U`
  are dense in `[r, u]` (the entry time `a'` of Berestycki–Gwynne (2020), Section 7.3, when the segments of `η` are
  regular closed);
* `ξ = windowEntryPoint`: the limit of `v(η(q_m))` along the first rational visits `q_m ∈ (α', α' + 1/(m+1))`
  (the image of the entry point `η(a')` under the extended chart, a prime end of `U`);
* the chart `ψ = unitRotation ξ · v` (`windowChartIntr`) and the conformal map `w ↦ φ(ξ w)` of the disc
  (`windowDiscMapIntr`).

All of these are Borel functions of the curve. Under an intrinsic re-embedding `f` over times `T ⊇ [a, b]`
(`IsIntrinsicCurveDecoratedReembedding`), the success of the construction is the same for both curves, and
`f ∘ windowDiscMapIntr η₂ = windowDiscMapIntr η₁` on the open disc.
-/

set_option autoImplicit false

open Set Metric Filter Topology Function MeasureTheory

namespace MatedCRT

/-! ### The inverse of the normalized conformal map of the open disc -/

/-- The window `(a, u, b)` of `η` has a conformal map of the open disc onto its window domain taking `0` to `η(u)`. -/
def HasOpenWindowDiscMap (a u b : ℝ) (η : C(ℝ, ℂ)) : Prop :=
  ∃ Φ, (η, Φ) ∈ openWindowDiscMapGraph a u b

theorem measurableSet_setOf_hasOpenWindowDiscMap (a u b : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | HasOpenWindowDiscMap a u b η} := by
  have heq : {η : C(ℝ, ℂ) | HasOpenWindowDiscMap a u b η} =
      (fun η => (η, openWindowDiscCode a u b η)) ⁻¹' openWindowDiscMapGraph a u b := by
    ext η
    exact ⟨fun h => openWindowDiscCode_mem h, fun h => ⟨_, h⟩⟩
  rw [heq]
  exact (measurable_id.prodMk (measurable_openWindowDiscCode a u b)) (measurableSet_openWindowDiscMapGraph a u b)

theorem hasOpenWindowDiscMap_iff {a u b : ℝ} {η : C(ℝ, ℂ)} :
    HasOpenWindowDiscMap a u b η ↔ ∃ φ, IsOpenDiscMap (windowDomain η a u b) φ ∧ φ 0 = η u := by
  constructor
  · intro h
    exact ⟨_, (isNormalizedOpenDiscMap_openWindowDiscMap h).isOpenDiscMap,
      (isNormalizedOpenDiscMap_openWindowDiscMap h).apply_zero⟩
  · rintro ⟨φ, hφ, h0⟩
    exact exists_mem_openWindowDiscMapGraph hφ h0

/-- **The inverse `v` of the normalized conformal map of the open disc onto the window domain**, on the window
domain. -/
noncomputable def openWindowDiscInv (a u b : ℝ) (η : C(ℝ, ℂ)) (x : ℂ) : ℂ :=
  planeToDisc (invCode (openWindowDiscCode a u b η, x))

theorem measurable_openWindowDiscInv (a u b : ℝ) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => openWindowDiscInv a u b p.1 p.2 :=
  planeToDisc.continuous.measurable.comp (measurable_invCode.comp
    (((measurable_openWindowDiscCode a u b).comp measurable_fst).prodMk measurable_snd))

theorem openWindowDiscInv_mem_ball (a u b : ℝ) (η : C(ℝ, ℂ)) (x : ℂ) :
    openWindowDiscInv a u b η x ∈ ball (0 : ℂ) 1 :=
  planeToDisc_mem_ball _

section Inverse

variable {a u b : ℝ} {η : C(ℝ, ℂ)}

theorem injective_openWindowDiscCode (h : HasOpenWindowDiscMap a u b η) :
    Injective (openWindowDiscCode a u b η) :=
  (injOn_comp_discToPlane_iff _).1 (isNormalizedOpenDiscMap_openWindowDiscMap h).isOpenDiscMap.injOn

theorem range_openWindowDiscCode (h : HasOpenWindowDiscMap a u b η) :
    range (openWindowDiscCode a u b η) = windowDomain η a u b := by
  rw [← image_comp_discToPlane]
  exact (isNormalizedOpenDiscMap_openWindowDiscMap h).isOpenDiscMap.image_ball

theorem openWindowDiscMap_openWindowDiscInv (h : HasOpenWindowDiscMap a u b η) {x : ℂ}
    (hx : x ∈ windowDomain η a u b) : openWindowDiscMap a u b η (openWindowDiscInv a u b η x) = x := by
  have hx' : x ∈ range (openWindowDiscCode a u b η) := by
    rw [range_openWindowDiscCode h]
    exact hx
  show openWindowDiscCode a u b η (discToPlane (planeToDisc (invCode (openWindowDiscCode a u b η, x)))) = x
  rw [discToPlane_planeToDisc]
  exact apply_invCode (injective_openWindowDiscCode h) hx'

theorem openWindowDiscInv_openWindowDiscMap (h : HasOpenWindowDiscMap a u b η) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : openWindowDiscInv a u b η (openWindowDiscMap a u b η w) = w := by
  show planeToDisc (invCode (openWindowDiscCode a u b η, openWindowDiscCode a u b η (discToPlane w))) = w
  rw [invCode_apply (injective_openWindowDiscCode h), planeToDisc_discToPlane hw]

end Inverse

/-! ### Visits of the window domain and the entry time -/

/-- The curves `η` with `f η` in their window domain form a Borel set, for a Borel `f`. -/
theorem measurableSet_setOf_mem_windowDomain (a u b : ℝ) {f : C(ℝ, ℂ) → ℂ} (hf : Measurable f) :
    MeasurableSet {η : C(ℝ, ℂ) | f η ∈ windowDomain η a u b} :=
  LatticeProb.measurableSet_mem_connectedComponentIn_interior_image
    (fun i : (ℚ × ℚ) × ℕ => ball (discRatCenter i) (discRatRadius i)) (fun η : C(ℝ, ℂ) => η) (fun η => η u)
    f isCompact_Icc measurable_id (continuous_eval_const u).measurable hf
    (fun _ => isOpen_ball) (fun _ => (convex_ball _ _).isPreconnected)
    (fun V hV z hz => by
      obtain ⟨i, hi, hiV⟩ := exists_ratBall hV hz
      exact ⟨i, hi, ball_subset_closedBall.trans hiV⟩)

/-- The rational times at which `η` visits its window domain are dense in `[r, u]`. -/
def WindowVisitsDense (a u b : ℝ) (η : C(ℝ, ℂ)) (r : ℝ) : Prop :=
  ∀ c d : ℚ, r ≤ c → (c : ℝ) < d → (d : ℝ) ≤ u →
    ∃ q : ℚ, (c : ℝ) < q ∧ (q : ℝ) < d ∧ η q ∈ windowDomain η a u b

theorem measurableSet_setOf_windowVisitsDense (a u b r : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | WindowVisitsDense a u b η r} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun c => Measurable.forall fun d =>
    measurable_const.imp (measurable_const.imp (measurable_const.imp (Measurable.exists fun q =>
      Measurable.and measurable_const (Measurable.and measurable_const ?_)))))
  exact measurableSet_setOfPred.1 (measurableSet_setOf_mem_windowDomain a u b (continuous_eval_const _).measurable)

open Classical in
/-- The term of rational index `r` in the infimum defining the intrinsic entry time. -/
noncomputable def windowEntryTerm (a u b : ℝ) (η : C(ℝ, ℂ)) (r : ℚ) : ℝ :=
  if (r : ℝ) ∈ Icc a u ∧ WindowVisitsDense a u b η r then r else u

/-- **The intrinsic entry time `α'` of the window**: the infimum of the rational `r ∈ [a, u]` such that the rational
visits of `η` to its window domain are dense in `[r, u]` (and `u` if there is none). -/
noncomputable def windowEntryIntr (a u b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  ⨅ r : ℚ, windowEntryTerm a u b η r

theorem measurable_windowEntryIntr (a u b : ℝ) : Measurable (windowEntryIntr a u b) := by
  classical
  refine Measurable.iInf fun r => ?_
  unfold windowEntryTerm
  exact Measurable.ite ((MeasurableSet.const _).inter (measurableSet_setOf_windowVisitsDense a u b r))
    measurable_const measurable_const

section Entry

variable {a u b : ℝ}

theorem windowEntryTerm_mem_Icc (hau : a ≤ u) (η : C(ℝ, ℂ)) (r : ℚ) : windowEntryTerm a u b η r ∈ Icc a u := by
  unfold windowEntryTerm
  split_ifs with h
  · exact h.1
  · exact ⟨hau, le_rfl⟩

theorem windowEntryTerm_of {η : C(ℝ, ℂ)} {r : ℚ} (h : (r : ℝ) ∈ Icc a u ∧ WindowVisitsDense a u b η r) :
    windowEntryTerm a u b η r = r := by
  unfold windowEntryTerm
  rw [ite_eq_left h]

theorem bddBelow_windowEntryTerm (hau : a ≤ u) (η : C(ℝ, ℂ)) : BddBelow (range (windowEntryTerm a u b η)) :=
  ⟨a, by
    rintro _ ⟨r, rfl⟩
    exact (windowEntryTerm_mem_Icc hau η r).1⟩

theorem windowEntryIntr_mem_Icc (hau : a ≤ u) (η : C(ℝ, ℂ)) : windowEntryIntr a u b η ∈ Icc a u :=
  ⟨le_ciInf fun r => (windowEntryTerm_mem_Icc hau η r).1,
    (ciInf_le (bddBelow_windowEntryTerm hau η) 0).trans (windowEntryTerm_mem_Icc hau η 0).2⟩

theorem windowEntryIntr_le_of {η : C(ℝ, ℂ)} (hau : a ≤ u) {r : ℚ}
    (h : (r : ℝ) ∈ Icc a u ∧ WindowVisitsDense a u b η r) : windowEntryIntr a u b η ≤ r :=
  (ciInf_le (bddBelow_windowEntryTerm hau η) r).trans (windowEntryTerm_of h).le

end Entry

/-! ### The entry point -/

/-- An enumeration of the rationals. -/
noncomputable def ratEnum : ℕ → ℚ :=
  (exists_surjective_nat ℚ).choose

theorem ratEnum_surjective : Surjective ratEnum :=
  (exists_surjective_nat ℚ).choose_spec

/-- `ratEnum n` is a rational visit of `η` to its window domain in `(α', α' + 1/(m+1))`, before `u`. -/
def IsEntryVisit (a u b : ℝ) (η : C(ℝ, ℂ)) (m n : ℕ) : Prop :=
  windowEntryIntr a u b η < ratEnum n ∧ (ratEnum n : ℝ) < windowEntryIntr a u b η + 1 / ((m : ℝ) + 1) ∧
    (ratEnum n : ℝ) ≤ u ∧ η (ratEnum n) ∈ windowDomain η a u b

theorem measurableSet_setOf_isEntryVisit (a u b : ℝ) (m n : ℕ) :
    MeasurableSet {η : C(ℝ, ℂ) | IsEntryVisit a u b η m n} := by
  have he := measurable_windowEntryIntr a u b
  exact (measurableSet_lt he measurable_const).inter ((measurableSet_lt measurable_const (he.add_const _)).inter
    ((MeasurableSet.const _).inter (measurableSet_setOf_mem_windowDomain a u b (continuous_eval_const _).measurable)))

/-- Selecting the first index at which measurable events occur is measurable. -/
theorem measurable_comp_sInf_index {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {E : α → ℕ → Prop}
    (hE : ∀ n, MeasurableSet {x | E x n}) {f : ℕ → α → β} (hf : ∀ n, Measurable (f n)) :
    Measurable fun x => f (sInf {n | E x n}) x := by
  intro s hs
  have heq : (fun x => f (sInf {n | E x n}) x) ⁻¹' s = ⋃ k : ℕ, {x | sInf {n | E x n} = k} ∩ f k ⁻¹' s := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨k, hk, h⟩ => by rw [hk]; exact h⟩
  rw [heq]
  refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ (hf k hs)
  have hk : {x | sInf {n | E x n} = k} =
      {x | E x k ∧ ∀ j, j < k → ¬E x j} ∪ {x | (∀ n, ¬E x n) ∧ k = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_union]
    have hemp : (∀ n, ¬E x n) → sInf {n | E x n} = 0 := fun hall => by
      have h0 : {n | E x n} = ∅ := Set.ext fun n => iff_of_false (hall n) id
      rw [h0, Nat.sInf_empty]
    constructor
    · intro h
      by_cases hex : ∃ n, E x n
      · left
        have hmem : sInf {n | E x n} ∈ {n | E x n} := Nat.sInf_mem hex
        rw [h] at hmem
        refine ⟨hmem, fun j hj hEj => ?_⟩
        have hle : sInf {n | E x n} ≤ j := Nat.sInf_le hEj
        rw [h] at hle
        exact absurd hj (not_lt.2 hle)
      · right
        have hall : ∀ n, ¬E x n := fun n hn => hex ⟨n, hn⟩
        exact ⟨hall, h.symm.trans (hemp hall)⟩
    · rintro (⟨hEk, hlt⟩ | ⟨hall, rfl⟩)
      · refine le_antisymm (Nat.sInf_le hEk) ?_
        by_contra hcon
        exact hlt _ (not_le.1 hcon) (Nat.sInf_mem ⟨k, hEk⟩)
      · exact hemp hall
  rw [hk]
  refine MeasurableSet.union (measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1 (hE k))
    (Measurable.forall fun j => measurable_const.imp (measurableSet_setOfPred.1 (hE j)).not)))
    (measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun n => (measurableSet_setOfPred.1 (hE n)).not)
      measurable_const))

/-- The index of the first rational visit of `(α', α' + 1/(m+1))`. -/
noncomputable def entryIdx (a u b : ℝ) (η : C(ℝ, ℂ)) (m : ℕ) : ℕ :=
  sInf {n | IsEntryVisit a u b η m n}

open Classical in
/-- The chart value `v(η(q_m))` at the first rational visit `q_m` of `(α', α' + 1/(m+1))` (`0` if there is none). -/
noncomputable def entryChartValue (a u b : ℝ) (η : C(ℝ, ℂ)) (m : ℕ) : ℂ :=
  if ∃ n, IsEntryVisit a u b η m n then openWindowDiscInv a u b η (η (ratEnum (entryIdx a u b η m))) else 0

theorem measurable_openWindowDiscInv_eval (a u b t : ℝ) :
    Measurable fun η : C(ℝ, ℂ) => openWindowDiscInv a u b η (η t) := by
  have h1 : Measurable fun η : C(ℝ, ℂ) => (η, η t) :=
    measurable_id.prodMk (continuous_eval_const t).measurable
  have h2 := (measurable_openWindowDiscInv a u b).comp h1
  simp only [Function.comp_def] at h2
  exact h2

theorem measurable_entryChartValue (a u b : ℝ) (m : ℕ) :
    Measurable fun η : C(ℝ, ℂ) => entryChartValue a u b η m := by
  classical
  unfold entryChartValue
  refine Measurable.ite (measurableSet_setOfPred.2 (Measurable.exists fun n =>
    measurableSet_setOfPred.1 (measurableSet_setOf_isEntryVisit a u b m n))) ?_ measurable_const
  exact measurable_comp_sInf_index (E := fun η n => IsEntryVisit a u b η m n)
    (fun n => measurableSet_setOf_isEntryVisit a u b m n)
    (f := fun n η => openWindowDiscInv a u b η (η (ratEnum n)))
    (fun n => measurable_openWindowDiscInv_eval a u b ((ratEnum n : ℚ) : ℝ))

/-- The sequence of chart values at the first rational visits converges. -/
def EntryConverges (a u b : ℝ) (η : C(ℝ, ℂ)) : Prop :=
  ∃ c, Tendsto (fun m => entryChartValue a u b η m) atTop (𝓝 c)

theorem measurableSet_setOf_entryConverges (a u b : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | EntryConverges a u b η} :=
  measurableSet_exists_tendsto fun m => measurable_entryChartValue a u b m

open Classical in
/-- **The intrinsic entry point `ξ`**: the limit of the chart values `v(η(q_m))` at the first rational visits `q_m`
of `(α', α' + 1/(m+1))` (`0` if it does not exist). -/
noncomputable def windowEntryPoint (a u b : ℝ) (η : C(ℝ, ℂ)) : ℂ :=
  if EntryConverges a u b η then limUnder atTop (fun m => entryChartValue a u b η m) else 0

theorem tendsto_windowEntryPoint {a u b : ℝ} {η : C(ℝ, ℂ)} (h : EntryConverges a u b η) :
    Tendsto (fun m => entryChartValue a u b η m) atTop (𝓝 (windowEntryPoint a u b η)) := by
  unfold windowEntryPoint
  rw [ite_eq_left h]
  exact tendsto_nhds_limUnder h

theorem measurable_windowEntryPoint (a u b : ℝ) : Measurable (windowEntryPoint a u b) := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun m η =>
      if EntryConverges a u b η then entryChartValue a u b η m else 0)
    (fun m => Measurable.ite (measurableSet_setOf_entryConverges a u b) (measurable_entryChartValue a u b m)
      measurable_const) (tendsto_pi_nhds.2 fun η => ?_)
  by_cases h : EntryConverges a u b η
  · simp only [ite_eq_left h]
    exact tendsto_windowEntryPoint h
  · simp only [ite_eq_right h]
    unfold windowEntryPoint
    rw [ite_eq_right h]
    exact tendsto_const_nhds

/-! ### The intrinsic chart -/

/-- **The success of the intrinsic construction**: the window has a conformal map of the open disc at `η(u)`, and the
chart values at the first rational visits after the entry time converge to a nonzero point. -/
def WindowGoodIntr (a u b : ℝ) (η : C(ℝ, ℂ)) : Prop :=
  HasOpenWindowDiscMap a u b η ∧ EntryConverges a u b η ∧ windowEntryPoint a u b η ≠ 0

theorem measurableSet_setOf_windowGoodIntr (a u b : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | WindowGoodIntr a u b η} :=
  (measurableSet_setOf_hasOpenWindowDiscMap a u b).inter ((measurableSet_setOf_entryConverges a u b).inter
    (measurableSet_eq_fun (measurable_windowEntryPoint a u b) measurable_const).compl)

/-- **The intrinsic inverse chart `ψ = unitRotation ξ · v` of the window** (the rotation taking `ξ` to the positive
half-line, as in `windowChartBG`). -/
noncomputable def windowChartIntr (a u b : ℝ) (η : C(ℝ, ℂ)) (x : ℂ) : ℂ :=
  unitRotation (windowEntryPoint a u b η) * openWindowDiscInv a u b η x

/-- **The intrinsic conformal map `w ↦ φ((unitRotation ξ)⁻¹ w)` of the open disc onto the window domain**, the
inverse of `windowChartIntr`. -/
noncomputable def windowDiscMapIntr (a u b : ℝ) (η : C(ℝ, ℂ)) (w : ℂ) : ℂ :=
  openWindowDiscMap a u b η ((unitRotation (windowEntryPoint a u b η))⁻¹ * w)

theorem unitRotation_ne_zero (c : ℂ) : unitRotation c ≠ 0 := fun h => by
  have h1 := norm_unitRotation c
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem norm_inv_unitRotation (c : ℂ) : ‖(unitRotation c)⁻¹‖ = 1 := by
  rw [norm_inv, norm_unitRotation, inv_one]

/-- The rotation of a rotated point. -/
theorem unitRotation_mul {c z : ℂ} (hc : ‖c‖ = 1) (hz : z ≠ 0) :
    unitRotation (c * z) = c⁻¹ * unitRotation z := by
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hcz : c * z ≠ 0 := mul_ne_zero hc0 hz
  unfold unitRotation
  rw [ite_eq_right hcz, ite_eq_right hz, norm_mul, hc, one_mul, mul_inv]
  ring

theorem measurable_windowChartIntr (a u b : ℝ) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => windowChartIntr a u b p.1 p.2 :=
  (measurable_unitRotation.comp ((measurable_windowEntryPoint a u b).comp measurable_fst)).mul
    (measurable_openWindowDiscInv a u b)

section Chart

variable {a u b : ℝ} {η : C(ℝ, ℂ)}

theorem WindowGoodIntr.isOpenDiscMap (h : WindowGoodIntr a u b η) :
    IsOpenDiscMap (windowDomain η a u b) (windowDiscMapIntr a u b η) :=
  (isNormalizedOpenDiscMap_openWindowDiscMap h.1).isOpenDiscMap.comp_mul (norm_inv_unitRotation _)

theorem WindowGoodIntr.windowDiscMapIntr_zero (h : WindowGoodIntr a u b η) : windowDiscMapIntr a u b η 0 = η u := by
  unfold windowDiscMapIntr
  rw [mul_zero]
  exact (isNormalizedOpenDiscMap_openWindowDiscMap h.1).apply_zero

theorem WindowGoodIntr.windowDiscMapIntr_windowChartIntr (h : WindowGoodIntr a u b η) {x : ℂ}
    (hx : x ∈ windowDomain η a u b) : windowDiscMapIntr a u b η (windowChartIntr a u b η x) = x := by
  unfold windowDiscMapIntr windowChartIntr
  rw [← mul_assoc, inv_mul_cancel₀ (unitRotation_ne_zero _), one_mul]
  exact openWindowDiscMap_openWindowDiscInv h.1 hx

theorem WindowGoodIntr.windowChartIntr_windowDiscMapIntr (h : WindowGoodIntr a u b η) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : windowChartIntr a u b η (windowDiscMapIntr a u b η w) = w := by
  have hw' : (unitRotation (windowEntryPoint a u b η))⁻¹ * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, norm_inv_unitRotation, one_mul]
    exact mem_ball_zero_iff.1 hw
  unfold windowDiscMapIntr windowChartIntr
  rw [openWindowDiscInv_openWindowDiscMap h.1 hw', ← mul_assoc, mul_inv_cancel₀ (unitRotation_ne_zero _), one_mul]

theorem windowChartIntr_mem_ball (a u b : ℝ) (η : C(ℝ, ℂ)) (x : ℂ) :
    windowChartIntr a u b η x ∈ ball (0 : ℂ) 1 := by
  unfold windowChartIntr
  rw [mem_ball_zero_iff, norm_mul, norm_unitRotation, one_mul]
  exact mem_ball_zero_iff.1 (openWindowDiscInv_mem_ball a u b η x)

end Chart

/-! ### Invariance under intrinsic re-embeddings -/

namespace IsIntrinsicCurveDecoratedReembedding

variable {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ} {a u b : ℝ}

theorem windowVisitsDense_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) {r : ℝ} (hr : a ≤ r) :
    WindowVisitsDense a u b η₁ r ↔ WindowVisitsDense a u b η₂ r := by
  have hv : ∀ c d q : ℚ, r ≤ c → (d : ℝ) ≤ u → (c : ℝ) < q → (q : ℝ) < d →
      (η₁ q ∈ windowDomain η₁ a u b ↔ η₂ q ∈ windowDomain η₂ a u b) := fun c d q hc hd hcq hqd =>
    hf.mem_windowDomain_iff hJ hu (hJ ⟨by linarith, by linarith [hu.2]⟩)
  constructor
  · intro h c d hc hcd hd
    obtain ⟨q, hcq, hqd, hq⟩ := h c d hc hcd hd
    exact ⟨q, hcq, hqd, (hv c d q hc hd hcq hqd).1 hq⟩
  · intro h c d hc hcd hd
    obtain ⟨q, hcq, hqd, hq⟩ := h c d hc hcd hd
    exact ⟨q, hcq, hqd, (hv c d q hc hd hcq hqd).2 hq⟩

theorem windowEntryIntr_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) : windowEntryIntr a u b η₁ = windowEntryIntr a u b η₂ := by
  unfold windowEntryIntr
  refine congrArg iInf (funext fun r => ?_)
  unfold windowEntryTerm
  by_cases hr : (r : ℝ) ∈ Icc a u
  · by_cases hd : WindowVisitsDense a u b η₂ r
    · rw [ite_eq_left ⟨hr, (hf.windowVisitsDense_iff hJ hu hr.1).2 hd⟩, ite_eq_left ⟨hr, hd⟩]
    · rw [ite_eq_right fun h => hd ((hf.windowVisitsDense_iff hJ hu hr.1).1 h.2), ite_eq_right fun h => hd h.2]
  · rw [ite_eq_right fun h => hr h.1, ite_eq_right fun h => hr h.1]

theorem isEntryVisit_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (m n : ℕ) : IsEntryVisit a u b η₁ m n ↔ IsEntryVisit a u b η₂ m n := by
  unfold IsEntryVisit
  rw [hf.windowEntryIntr_eq hJ hu]
  have ha : a ≤ windowEntryIntr a u b η₂ := (windowEntryIntr_mem_Icc hu.1 η₂).1
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (hf.mem_windowDomain_iff hJ hu (hJ ⟨by linarith, by linarith [hu.2]⟩)).1 h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, (hf.mem_windowDomain_iff hJ hu (hJ ⟨by linarith, by linarith [hu.2]⟩)).2 h4⟩

theorem entryIdx_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (m : ℕ) : entryIdx a u b η₁ m = entryIdx a u b η₂ m := by
  unfold entryIdx
  exact congrArg sInf (Set.ext fun n => hf.isEntryVisit_iff hJ hu m n)

theorem hasOpenWindowDiscMap_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) : HasOpenWindowDiscMap a u b η₁ ↔ HasOpenWindowDiscMap a u b η₂ := by
  rw [MatedCRT.hasOpenWindowDiscMap_iff, MatedCRT.hasOpenWindowDiscMap_iff]
  exact hf.exists_openDiscMap_iff hJ hu

/-- **The chart values at the first rational visits differ by a fixed rotation.** -/
theorem exists_entryChartValue_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) (h₁' : HasOpenWindowDiscMap a u b η₁)
    (h₂' : HasOpenWindowDiscMap a u b η₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (∀ w ∈ ball (0 : ℂ) 1, f (openWindowDiscMap a u b η₂ w) = openWindowDiscMap a u b η₁ (c * w)) ∧
      ∀ m, entryChartValue a u b η₁ m = c * entryChartValue a u b η₂ m := by
  obtain ⟨c, hc, hrot⟩ := hf.exists_rotation_of_normalized hJ hu (isNormalizedOpenDiscMap_openWindowDiscMap h₁')
    (isNormalizedOpenDiscMap_openWindowDiscMap h₂')
  refine ⟨c, hc, hrot, fun m => ?_⟩
  have hsub₂ := windowDomain_subset hJ η₂ u
  unfold entryChartValue
  by_cases hex : ∃ n, IsEntryVisit a u b η₂ m n
  · have hex₁ : ∃ n, IsEntryVisit a u b η₁ m n :=
      let ⟨n, hn⟩ := hex
      ⟨n, (hf.isEntryVisit_iff hJ hu m n).2 hn⟩
    rw [ite_eq_left hex, ite_eq_left hex₁, hf.entryIdx_eq hJ hu m]
    set q := ratEnum (entryIdx a u b η₂ m)
    have hvis : IsEntryVisit a u b η₂ m (entryIdx a u b η₂ m) := Nat.sInf_mem hex
    have hq₂ : η₂ q ∈ windowDomain η₂ a u b := hvis.2.2.2
    have ha : a ≤ windowEntryIntr a u b η₂ := (windowEntryIntr_mem_Icc hu.1 η₂).1
    have hqT : (q : ℝ) ∈ T := hJ ⟨by linarith [hvis.1], by linarith [hvis.2.2.1, hu.2]⟩
    have hfq : f (η₂ q) = η₁ q := hf.1 q hqT (hsub₂ hq₂)
    have hw : openWindowDiscInv a u b η₂ (η₂ q) ∈ ball (0 : ℂ) 1 := openWindowDiscInv_mem_ball a u b η₂ _
    have hcw : c * openWindowDiscInv a u b η₂ (η₂ q) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, hc, one_mul]
      exact mem_ball_zero_iff.1 hw
    have h1 : η₁ q = openWindowDiscMap a u b η₁ (c * openWindowDiscInv a u b η₂ (η₂ q)) := by
      rw [← hfq, ← hrot _ hw, openWindowDiscMap_openWindowDiscInv h₂' hq₂]
    rw [h1, openWindowDiscInv_openWindowDiscMap h₁' hcw]
  · have hex₁ : ¬∃ n, IsEntryVisit a u b η₁ m n := fun ⟨n, hn⟩ => hex ⟨n, (hf.isEntryVisit_iff hJ hu m n).1 hn⟩
    rw [ite_eq_right hex, ite_eq_right hex₁, mul_zero]

/-- **The success of the intrinsic construction is intrinsic**, and the intrinsic conformal maps of the open disc
correspond under `f`. -/
theorem windowGoodIntr_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) : WindowGoodIntr a u b η₁ ↔ WindowGoodIntr a u b η₂ := by
  by_cases hD : HasOpenWindowDiscMap a u b η₂
  · have hD₁ : HasOpenWindowDiscMap a u b η₁ := (hf.hasOpenWindowDiscMap_iff hJ hu).2 hD
    obtain ⟨c, hc, -, hval⟩ := hf.exists_entryChartValue_eq hJ hu hD₁ hD
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hc
      exact zero_ne_one hc
    have hseq : (fun m => entryChartValue a u b η₁ m) = fun m => c * entryChartValue a u b η₂ m := funext hval
    have hconv : EntryConverges a u b η₁ ↔ EntryConverges a u b η₂ := by
      unfold EntryConverges
      rw [hseq]
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨c⁻¹ * z, ?_⟩
        have := hz.const_mul c⁻¹
        simp only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
        exact this
      · rintro ⟨z, hz⟩
        exact ⟨c * z, hz.const_mul c⟩
    by_cases hC : EntryConverges a u b η₂
    · have hC₁ := hconv.2 hC
      have hpt : windowEntryPoint a u b η₁ = c * windowEntryPoint a u b η₂ := by
        have h1 := tendsto_windowEntryPoint hC₁
        rw [hseq] at h1
        exact tendsto_nhds_unique h1 ((tendsto_windowEntryPoint hC).const_mul c)
      unfold WindowGoodIntr
      rw [hpt]
      exact ⟨fun h => ⟨hD, hC, fun h0 => h.2.2 (by rw [h0, mul_zero])⟩,
        fun h => ⟨hD₁, hC₁, mul_ne_zero hc0 h.2.2⟩⟩
    · exact ⟨fun h => absurd (hconv.1 h.2.1) hC, fun h => absurd h.2.1 hC⟩
  · exact ⟨fun h => absurd ((hf.hasOpenWindowDiscMap_iff hJ hu).1 h.1) hD, fun h => absurd h.1 hD⟩

/-- **The intrinsic conformal maps of the open disc correspond under `f`.** -/
theorem windowDiscMapIntr_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (h₂' : WindowGoodIntr a u b η₂) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    windowDiscMapIntr a u b η₁ w = f (windowDiscMapIntr a u b η₂ w) := by
  have h₁' := (hf.windowGoodIntr_iff hJ hu).2 h₂'
  obtain ⟨c, hc, hrot, hval⟩ := hf.exists_entryChartValue_eq hJ hu h₁'.1 h₂'.1
  have hseq : (fun m => entryChartValue a u b η₁ m) = fun m => c * entryChartValue a u b η₂ m := funext hval
  have hpt : windowEntryPoint a u b η₁ = c * windowEntryPoint a u b η₂ := by
    have h1 := tendsto_windowEntryPoint h₁'.2.1
    rw [hseq] at h1
    exact tendsto_nhds_unique h1 ((tendsto_windowEntryPoint h₂'.2.1).const_mul c)
  have hw' : (unitRotation (windowEntryPoint a u b η₂))⁻¹ * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, norm_inv_unitRotation, one_mul]
    exact mem_ball_zero_iff.1 hw
  unfold windowDiscMapIntr
  rw [hrot _ hw', hpt, unitRotation_mul hc h₂'.2.2, mul_inv, inv_inv, mul_assoc]

end IsIntrinsicCurveDecoratedReembedding

end MatedCRT
