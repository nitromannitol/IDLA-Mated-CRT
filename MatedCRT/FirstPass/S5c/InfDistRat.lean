import MatedCRT.FirstPass.S5c.NullContainment

/-!
# FIRST PASS, Lemma 5.3: null-measurable distance tests at rational points (B1a)

For a rational centre `z = (c.1, c.2)` and a rational `s`, the event `{s < infDist z (Λ_q)ᶜ}` is a countable union over rational
radii `r > s` of the rational containment events `{ratDisk c r ⊆ Λ_q}` (NullContainment.lean), hence null measurable from the
point memberships (the Gap 2 decoder input `hmem`). This is the measurable form of the open sets `{infDist > s}` used in the
density reduction of the compact core (DensityFloor.lean); it is not the floor measurability itself (B1b, B1c open).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- **Null-measurable distance tests at rational points** (B1a): `{ω | s < infDist z (Λ ω q)ᶜ}` is null measurable for rational
centre `c` and rational `s`, from the point memberships (`hmem`) and the a.s. regularity and nonemptiness of `Λ ω q`. -/
theorem nullMeasurableSet_infDist_gt_rat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Λ : Ω → ℝ → Set ℂ) (q : ℝ)
    (hreg : ∀ᵐ ω ∂P, interior (closure (Λ ω q)) = Λ ω q)
    (hne : ∀ᵐ ω ∂P, (Λ ω q)ᶜ.Nonempty)
    (hmem : ∀ j : ℕ, NullMeasurableSet {ω | densePoint j ∈ Λ ω q} P)
    (c : ℚ × ℚ) (s : ℚ) :
    NullMeasurableSet {ω | (s : ℝ) < infDist (⟨(c.1 : ℝ), (c.2 : ℝ)⟩ : ℂ) (Λ ω q)ᶜ} P := by
  have hU : NullMeasurableSet
      (⋃ r : {r : ℚ // (s : ℝ) < r}, {ω | ratDisk c r.1 ⊆ Λ ω q}) P :=
    NullMeasurableSet.iUnion fun r => nullMeasurableSet_ratDisk_containment P Λ q hreg hne hmem c r.1
  refine hU.congr ?_
  apply Filter.eventuallyEqSet_iff.2
  filter_upwards [hreg, hne] with ω hreg' hne'
  have hopen : IsOpen (Λ ω q) := hreg' ▸ isOpen_interior
  constructor
  · intro h
    obtain ⟨⟨r, hr1⟩, hsub⟩ := mem_iUnion.1 h
    have hsub' : ratDisk c r ⊆ Λ ω q := hsub
    have hlt : (r : ℝ) < infDist (⟨(c.1 : ℝ), (c.2 : ℝ)⟩ : ℂ) (Λ ω q)ᶜ :=
      (closedBall_subset_iff_lt_infDist hopen hne' _ _).1 hsub'
    exact lt_trans hr1 hlt
  · intro h
    have h' : (s : ℝ) < infDist (⟨(c.1 : ℝ), (c.2 : ℝ)⟩ : ℂ) (Λ ω q)ᶜ := h
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h'
    have hsub : ratDisk c r ⊆ Λ ω q :=
      (closedBall_subset_iff_lt_infDist hopen hne' _ _).2 hr2
    exact mem_iUnion.2 ⟨⟨r, hr1⟩, hsub⟩

/-- **Closure of the open floor set lies in `L`** (B1, deterministic): for `s > 0` and `Lᶜ` nonempty, the closure of
`S_s = {x ∈ B_ρ | s < infDist x Lᶜ}` lies in `L`, and it is compact. -/
theorem closure_floor_set_subset {L : Set ℂ} (ρ s : ℝ) (hs : 0 < s) :
    closure {x : ℂ | x ∈ ball (0 : ℂ) ρ ∧ s < infDist x Lᶜ} ⊆ L := by
  have hcl : closure {x : ℂ | x ∈ ball (0 : ℂ) ρ ∧ s < infDist x Lᶜ} ⊆
      {x : ℂ | s ≤ infDist x Lᶜ} :=
    closure_minimal (fun _ hx => le_of_lt hx.2)
      (isClosed_le continuous_const (continuous_infDist_pt Lᶜ))
  intro x hx
  by_contra hxL
  have h0 : infDist x Lᶜ = 0 := infDist_zero_of_mem hxL
  have h1 : s ≤ infDist x Lᶜ := hcl hx
  rw [h0] at h1
  linarith

/-- **The closed floor set is compact** (B1, deterministic). -/
theorem isCompact_closure_floor_set {L : Set ℂ} (ρ s : ℝ) :
    IsCompact (closure {x : ℂ | x ∈ ball (0 : ℂ) ρ ∧ s < infDist x Lᶜ}) :=
  (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset isClosed_closure
    (closure_minimal (fun _ hx => ball_subset_closedBall hx.1) isClosed_closedBall)

end MatedCRT.S5c
