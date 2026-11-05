import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.EventBounds
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalInitialMaximum

/-! Combining conditional probability bounds for spatial budgets. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Two random upper bounds which vanish in probability on an event have a
sum which also vanishes in probability on that event. -/
theorem tendsToOneOn_add_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (X Y : ℝ → Ω → ℝ)
    (hX : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω ≤ a}))
    (hY : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | Y ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω + Y ε ω ≤ a}) := by
  intro a ha
  have h := tendsToOneOn_inter P F (fun ε => {ω | X ε ω ≤ a / 2})
    (fun ε => {ω | Y ε ω ≤ a / 2}) (hX _ (by positivity)) (hY _ (by positivity))
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  rintro ω ⟨hF, hbad⟩
  refine ⟨hF, ?_⟩
  rintro ⟨hx, hy⟩
  apply hbad
  change X ε ω + Y ε ω ≤ a
  change X ε ω ≤ a / 2 at hx
  change Y ε ω ≤ a / 2 at hy
  linarith

/-- Multiplication by a fixed nonnegative constant preserves conditional
convergence of a random upper bound to zero. -/
theorem tendsToOneOn_const_mul_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (X : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hX : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | C * X ε ω ≤ a}) := by
  intro a ha
  let d := a / (C + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have h := hX d hd
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  rintro ω ⟨hF, hbad⟩
  refine ⟨hF, ?_⟩
  intro hx
  apply hbad
  change C * X ε ω ≤ a
  change X ε ω ≤ d at hx
  have hCd : C * d ≤ a := by
    dsimp [d]
    have hden : 0 < C + 1 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  exact (mul_le_mul_of_nonneg_left hx hC).trans hCd

/-- Conditional smallness of the initial radius, logarithmic initial term,
floor term and diameter term yields the full delayed dyadic budget. -/
theorem tendsToOneOn_delayed_dyadic_total_budget
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (x r₀ floorTerm diameterTerm : ℝ → Ω → ℝ) {α c C T : ℝ}
    (hα : 0 < α) (hc : 0 < c) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hxnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ x ε ω)
    (hx : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | x ε ω ≤ a}))
    (hr₀ : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | r₀ ε ω ≤ a}))
    (hfloor : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | floorTerm ε ω ≤ a}))
    (hdiam : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | diameterTerm ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      r₀ ε ω + (x ε ω ^ α * C *
        ((1 + |Real.log ((c / 8) * (x ε ω * (1 / 2 : ℝ)) ^ α)| +
          |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 * T) + floorTerm ε ω) +
        diameterTerm ε ω ≤ a}) := by
  let L : ℝ → Ω → ℝ := fun ε ω => x ε ω ^ α *
    (1 + |Real.log ((c / 8) * (x ε ω * (1 / 2 : ℝ)) ^ α)| +
      |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2
  have hL : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | L ε ω ≤ a}) :=
    tendsToOneOn_delayed_dyadic_initial_log_budget P F x hα hc G hG hxnonneg hx
  have hscaled := tendsToOneOn_const_mul_le P F L (C * T) (mul_nonneg hC hT) hL
  have hsum := tendsToOneOn_add_le P F r₀ (fun ε ω => (C * T) * L ε ω) hr₀ hscaled
  have hsum' := tendsToOneOn_add_le P F
    (fun ε ω => r₀ ε ω + (C * T) * L ε ω) floorTerm hsum hfloor
  have hsum'' := tendsToOneOn_add_le P F
    (fun ε ω => r₀ ε ω + (C * T) * L ε ω + floorTerm ε ω) diameterTerm hsum' hdiam
  intro a ha
  convert hsum'' a ha using 1
  funext ε
  ext ω
  dsimp [L]
  ring_nf

end MatedCRT.Sec7
