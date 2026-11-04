import MatedCRT.Defs.Setting

/-! # Jump times of increasing open clusters -/

namespace MatedCRT

open Set Topology

/-- For a family of open sets in a second-countable space, only
countably many positive times add points outside the closure of all earlier
positive-time sets. -/
theorem countable_open_cluster_jump_times
    {X : Type} [Nonempty X] [TopologicalSpace X] [SecondCountableTopology X]
    (D : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (D t)) :
    {t : ℝ | 0 < t ∧ ¬ D t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s)}.Countable := by
  classical
  obtain ⟨C, hC, hdense⟩ := TopologicalSpace.exists_countable_dense X
  let J : Set ℝ := {t : ℝ | 0 < t ∧ ¬ D t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s)}
  have hw : ∀ t ∈ J, ∃ z ∈ C, z ∈ D t ∧ z ∉ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s) := by
    intro t ht
    obtain ⟨x, hxD, hxnot⟩ := not_subset.mp ht.2
    exact hdense.exists_mem_open ((hopen t ht.1).inter isClosed_closure.isOpen_compl)
      ⟨x, hxD, hxnot⟩
  let f : ℝ → X := fun t => if ht : t ∈ J then Classical.choose (hw t ht) else Classical.choice inferInstance
  have hf : MapsTo f J C := by
    intro t ht
    simpa [f, ht] using (Classical.choose_spec (hw t ht)).1
  have hfprop : ∀ t ∈ J, f t ∈ D t ∧ f t ∉ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s) := by
    intro t ht
    simpa [f, ht] using (Classical.choose_spec (hw t ht)).2
  have hinj : InjOn f J := by
    intro s hs t ht heq
    rcases lt_trichotomy s t with hst | rfl | hts
    · exfalso
      have hmem : f s ∈ ⋃ r ∈ Ioo (0 : ℝ) t, D r := by
        simp only [mem_iUnion]
        exact ⟨s, ⟨hs.1, hst⟩, (hfprop s hs).1⟩
      exact (hfprop t ht).2 (heq ▸ subset_closure hmem)
    · rfl
    · exfalso
      have hmem : f t ∈ ⋃ r ∈ Ioo (0 : ℝ) s, D r := by
        simp only [mem_iUnion]
        exact ⟨t, ⟨ht.1, hts⟩, (hfprop t ht).1⟩
      exact (hfprop s hs).2 (heq.symm ▸ subset_closure hmem)
  exact hf.countable_of_injOn hinj hC

/-- An increasing regular-open family equals the regularization of its
earlier members at every positive time outside a countable set. -/
theorem regularOpen_cluster_eq_regularized_earlier_except_countably_many
    {X : Type} [Nonempty X] [TopologicalSpace X] [SecondCountableTopology X]
    (D : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (D t))
    (hregular : ∀ t, 0 < t → interior (closure (D t)) = D t)
    (hmono : ∀ s t, 0 < s → s ≤ t → D s ⊆ D t) :
    ∃ J : Set ℝ, J.Countable ∧ ∀ t, 0 < t → t ∉ J →
      D t = interior (closure (⋃ s ∈ Ioo (0 : ℝ) t, D s)) := by
  let J : Set ℝ := {t : ℝ | 0 < t ∧ ¬ D t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s)}
  refine ⟨J, countable_open_cluster_jump_times D hopen, ?_⟩
  intro t ht hnot
  have hsub : D t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, D s) := by
    by_contra h
    exact hnot ⟨ht, h⟩
  apply Subset.antisymm (interior_maximal hsub (hopen t ht))
  calc
    interior (closure (⋃ s ∈ Ioo (0 : ℝ) t, D s)) ⊆ interior (closure (D t)) := by
      apply interior_mono
      apply closure_mono
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      exact hmono s t hs.1 hs.2.le hx
    _ = D t := hregular t ht

/-- A cone harmonic-ball family has at most countably many times at which its
regular-open set differs from the regularization of all earlier sets. -/
theorem coneFamily_regularized_earlier_except_countably_many
    {μ : MeasureTheory.Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ) :
    ∃ J : Set ℝ, J.Countable ∧ ∀ t, 0 < t → t ∉ J →
      Λ t = interior (closure (⋃ s ∈ Ioo (0 : ℝ) t, Λ s)) := by
  apply regularOpen_cluster_eq_regularized_earlier_except_countably_many Λ
  · intro t ht
    rw [← hΛ.2.1.isRegularOpen t ht]
    exact isOpen_interior
  · exact hΛ.2.1.isRegularOpen
  · exact fun s t hs hst => hΛ.2.1.monotoneOn hs (hs.trans_le hst) hst

/-- Hausdorff continuity rules out jumps of the closures of cone harmonic
balls from earlier positive times. -/
theorem coneFamily_subset_closure_earlier
    {μ : MeasureTheory.Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {t : ℝ} (ht : 0 < t) :
    Λ t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, Λ s) := by
  intro x hx
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  have hevent : ∀ᶠ s in nhdsWithin t (Ioi (0 : ℝ)),
      Metric.hausdorffEDist (Λ s) (Λ t) < ε :=
    hΛ.2.1.hausdorffContinuousOn t ht ε hε
  have hevent' : ∀ᶠ s in 𝓝 t, s ∈ Ioi (0 : ℝ) →
      Metric.hausdorffEDist (Λ s) (Λ t) < ε := eventually_nhdsWithin_iff.mp hevent
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp hevent'
  let s : ℝ := t - min δ t / 2
  have hmin : 0 < min δ t := lt_min hδ ht
  have hs : 0 < s ∧ s < t := by
    dsimp [s]
    constructor <;> linarith [min_le_right δ t]
  have hdist : dist s t < δ := by
    rw [Real.dist_eq]
    have : s - t = -(min δ t / 2) := by dsimp [s]; ring
    rw [this, abs_neg, abs_of_pos (half_pos hmin)]
    linarith [min_le_left δ t]
  have hhaus := hδprop hdist hs.1
  rw [Metric.hausdorffEDist_comm] at hhaus
  obtain ⟨y, hy, hydist⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hx hhaus
  exact ⟨y, by simp only [mem_iUnion]; exact ⟨s, hs, hy⟩, hydist⟩

/-- Every cone harmonic ball is the regularization of the union of all
strictly earlier balls. -/
theorem coneFamily_eq_regularized_earlier
    {μ : MeasureTheory.Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {t : ℝ} (ht : 0 < t) :
    Λ t = interior (closure (⋃ s ∈ Ioo (0 : ℝ) t, Λ s)) := by
  have hopen : IsOpen (Λ t) := by
    rw [← hΛ.2.1.isRegularOpen t ht]
    exact isOpen_interior
  apply Subset.antisymm (interior_maximal (coneFamily_subset_closure_earlier hΛ ht) hopen)
  calc
    interior (closure (⋃ s ∈ Ioo (0 : ℝ) t, Λ s)) ⊆ interior (closure (Λ t)) := by
      apply interior_mono
      apply closure_mono
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      exact hΛ.2.1.monotoneOn hs.1 ht hs.2.le hx
    _ = Λ t := hΛ.2.1.isRegularOpen t ht

end MatedCRT
