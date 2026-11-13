import MatedCRT.FirstPass.Derived.ExitCouplingBoundary

/-!
# Near-boundary comparison of laws from a high-probability event

`levyProkhorovEDist_stoppedInterp_le_of_stay_near` (in `ExitCouplingBoundary`) bounds the
Lévy–Prokhorov distance between the laws of two stopped interpolated walks by the probabilities of the
events that the walks wander away from their starting vertices before the exit time from `B`.
Here the hypotheses are put in the form in which the cell-radius estimate of
Berestycki–Gwynne (2020), Lemma 6.13 (last assertion), is available: an event `E_x` of probability at
least `1 - a`, on which every vertex visited up to the exit time from `B` has its cell inside the disc
of radius `R` about the point of the starting vertex (`levyProkhorovEDist_stoppedInterp_le_of_cells_event`).
This is the near-boundary comparison of laws in Berestycki–Gwynne (2020), Proposition 6.12, Step 3.
The event need not be measurable: the bad event of the walk leaving the disc is measurable, disjoint from
`E_x`, and `μ E_x + μ (bad) ≤ 1`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingBoundary

open MeasureTheory Set LatticeProb Metric
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingGlue
attribute [local instance] LatticeProb.dUnifMetricSpace

/-- If an event `E` of probability at least `1 - a` is disjoint from a measurable set `S`, then
`μ S ≤ a`. The event `E` need not be measurable. -/
lemma measure_le_of_disjoint_of_le_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {E S : Set α} (hS : MeasurableSet S) (hd : Disjoint E S) (a : ℝ≥0)
    (hE : ENNReal.ofReal (1 - (a : ℝ)) ≤ μ E) : μ S ≤ a := by
  have h1 : μ E + μ S ≤ 1 := by
    rw [← measure_union hd hS]
    exact prob_le_one
  have hc : ENNReal.ofReal (1 - (a : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (a : ℝ)) + (a : ℝ≥0∞) := by
    have := ENNReal.ofReal_add_le (p := 1 - (a : ℝ)) (q := (a : ℝ))
    rw [ENNReal.ofReal_coe_nnreal, show 1 - (a : ℝ) + a = 1 by ring, ENNReal.ofReal_one] at this
    exact this
  have h3 : ENNReal.ofReal (1 - (a : ℝ)) + μ S ≤ ENNReal.ofReal (1 - (a : ℝ)) + (a : ℝ≥0∞) :=
    calc ENNReal.ofReal (1 - (a : ℝ)) + μ S ≤ μ E + μ S := by gcongr
      _ ≤ 1 := h1
      _ ≤ _ := h2
  exact (ENNReal.add_le_add_iff_left hc).1 h3

/-- **Near-boundary comparison of laws from an event.**  Let `A ⊆ B`, let `E_x` (resp. `E_y`) be an event
of probability at least `1 - a` for the walk from `x` (resp. `y`), on which every vertex visited up to
the exit time from `B` has its embedded point within `R` of `v x` (resp. `v y`).  If
`T0 (2 R + d) + exp (-T0) < r` for `d ≥ |v x - v y|` and `a + a ≤ r`, then the Lévy–Prokhorov edistance of
the laws of the interpolated walks stopped at their exit time from `A` is at most `r`. -/
theorem levyProkhorovEDist_stoppedInterp_le_of_event {mult : ℤ → ℤ → ℕ} (v : ℤ → ℂ)
    {m : ℝ≥0} (hm : 0 < m) {A B : Set ℤ} (hAB : A ⊆ B) {x y : ℤ} {R d : ℝ}
    (hd : dist (v x) (v y) ≤ d) (T0 a r : ℝ≥0) {Ex Ey : Set (ℕ → ℤ)}
    (hEx : Ex ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime B X → dist (v (X n)) (v x) ≤ R})
    (hEy : Ey ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime B X → dist (v (X n)) (v y) ≤ R})
    (hx : ENNReal.ofReal (1 - (a : ℝ)) ≤ srwLaw mult x Ex)
    (hy : ENNReal.ofReal (1 - (a : ℝ)) ≤ srwLaw mult y Ey)
    (hr : T0 * (2 * R + d) + Real.exp (-(T0 : ℝ)) < r) (ha : a + a ≤ r) :
    levyProkhorovEDist ((srwLaw mult x).map (stoppedInterp v m A))
      ((srwLaw mult y).map (stoppedInterp v m A)) ≤ r := by
  have hbad : ∀ (c : ℤ) (E : Set (ℕ → ℤ)),
      E ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime B X → dist (v (X n)) (v c) ≤ R} →
      ENNReal.ofReal (1 - (a : ℝ)) ≤ srwLaw mult c E →
      srwLaw mult c {X | ∃ n : ℕ, (n : ℕ∞) ≤ vExitTime B X ∧ R < dist (v (X n)) (v c)} ≤ a := by
    intro c E hE hμ
    refine measure_le_of_disjoint_of_le_measure (srwLaw mult c) ?_ ?_ a hμ
    · have : {X : ℕ → ℤ | ∃ n : ℕ, (n : ℕ∞) ≤ vExitTime B X ∧ R < dist (v (X n)) (v c)} =
          ⋃ n : ℕ, ({X | (n : ℕ∞) ≤ vExitTime B X} ∩ {X | R < dist (v (X n)) (v c)}) := by
        ext X; simp
      rw [this]
      refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
      · exact (measurable_vExitTime B) (MeasurableSet.of_discrete (s := {e : ℕ∞ | (n : ℕ∞) ≤ e}))
      · have hg : Measurable fun X : ℕ → ℤ => dist (v (X n)) (v c) :=
          (Measurable.of_discrete (f := fun k : ℤ => dist (v k) (v c))).comp (measurable_pi_apply n)
        exact measurableSet_lt measurable_const hg
    · refine Set.disjoint_left.2 fun X hXE hXS => ?_
      obtain ⟨n, hn, hlt⟩ := hXS
      exact absurd (hE hXE n hn) (not_le.2 hlt)
  have hr' : T0 * (2 * R + dist (v x) (v y)) + Real.exp (-(T0 : ℝ)) < r :=
    lt_of_le_of_lt (by gcongr) hr
  exact levyProkhorovEDist_stoppedInterp_le_of_stay_near v hm hAB T0 a r hr'
    (hbad x Ex hEx hx) (hbad y Ey hEy hy) ha

/-- **The same, for the cell-radius event of Lemma 6.13.**  Here the event `E_x` is contained in the set
where, up to the exit time from `B`, the cells of the visited vertices lie inside the disc of radius `R`
about the point `η(εx)` of the starting vertex. -/
theorem levyProkhorovEDist_stoppedInterp_le_of_cells_event {mult : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 ≤ ε) {m : ℝ≥0} (hm : 0 < m) {A B : Set ℤ} (hAB : A ⊆ B) {x y : ℤ} {R d : ℝ}
    (hd : dist (vertexPoint ε η x) (vertexPoint ε η y) ≤ d) (T0 a r : ℝ≥0) {Ex Ey : Set (ℕ → ℤ)}
    (hEx : Ex ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime B X → cell ε η (X n) ⊆ ball (vertexPoint ε η x) R})
    (hEy : Ey ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime B X → cell ε η (X n) ⊆ ball (vertexPoint ε η y) R})
    (hx : ENNReal.ofReal (1 - (a : ℝ)) ≤ srwLaw mult x Ex)
    (hy : ENNReal.ofReal (1 - (a : ℝ)) ≤ srwLaw mult y Ey)
    (hr : T0 * (2 * R + d) + Real.exp (-(T0 : ℝ)) < r) (ha : a + a ≤ r) :
    levyProkhorovEDist ((srwLaw mult x).map (stoppedInterp (vertexPoint ε η) m A))
      ((srwLaw mult y).map (stoppedInterp (vertexPoint ε η) m A)) ≤ r := by
  have hmem : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  refine levyProkhorovEDist_stoppedInterp_le_of_event (vertexPoint ε η) hm hAB hd T0 a r ?_ ?_ hx hy
    hr ha
  · intro X hX n hn
    exact (mem_ball.1 (hEx hX n hn (hmem (X n)))).le
  · intro X hX n hn
    exact (mem_ball.1 (hEy hX n hn (hmem (X n)))).le

end ExitCouplingBoundary
end MatedCRT
