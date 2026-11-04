import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-!
# Integrating rescaled functions over SLE cells

Area parametrization gives each cell mass `ε`; distinct cells overlap only
on null sets. Thus the least-index convention in `vertexOf` agrees almost
everywhere with the index of a given cell. This identifies a cell integral
with the corresponding summand in the truncated graph Green sum.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Every cell has quantum mass equal to its time length. -/
theorem measure_cell_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (a : ℤ) :
    μ (cell ε η a) = ENNReal.ofReal ε := by
  have htime : ε * ((a : ℝ) - 1) < ε * a := by nlinarith
  change μ (η '' Icc (ε * ((a : ℝ) - 1)) (ε * a)) = _
  rw [hη.2.2.2 _ _ htime]
  congr 1
  ring

/-- The least cell containing a point agrees almost everywhere with the index
of any specified cell containing that point. -/
theorem ae_vertexOf_eq_on_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ) :
    ∀ᵐ x ∂μ.restrict (cell ε η a), vertexOf ε η x = a := by
  classical
  have hmeas : MeasurableSet (cell ε η a) :=
    (isCompact_Icc.image hη.1).isClosed.measurableSet
  have hnull : μ (⋃ k : ℤ, ⋃ (_ : k ≠ a), cell ε η a ∩ cell ε η k) = 0 := by
    refine measure_iUnion_null fun k => measure_iUnion_null fun hk => ?_
    rcases lt_or_gt_of_ne hk with hka | hak
    · rw [inter_comm]
      exact ConstantOrder.cell_inter_null hη hε hka
    · exact ConstantOrder.cell_inter_null hη hε hak
  have hnot : ∀ᵐ x ∂μ, x ∉ ⋃ k : ℤ, ⋃ (_ : k ≠ a), cell ε η a ∩ cell ε η k := by
    apply ae_iff.2
    simpa only [not_not, ofPred_mem_eq] using hnull
  apply (ae_restrict_iff' hmeas).2
  filter_upwards [hnot] with x hx hxa
  by_contra hne
  apply hx
  exact mem_iUnion.2 ⟨vertexOf ε η x, mem_iUnion.2 ⟨hne, hxa,
    Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε x⟩⟩

/-- The integral of a rescaled vertex function over one cell is its vertex
value multiplied by the cell mass. -/
theorem setIntegral_rescale_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ) (m : ℝ) (u : ℤ → ℝ) :
    (∫ x in cell ε η a, rescale m ε η u x ∂μ) = ε * (m⁻¹ * u a) := by
  have heq : (fun x => rescale m ε η u x) =ᵐ[μ.restrict (cell ε η a)]
      fun _ => m⁻¹ * u a := by
    filter_upwards [ae_vertexOf_eq_on_cell hη hp hε a] with x hx
    simp [rescale, hx]
  calc
    (∫ x in cell ε η a, rescale m ε η u x ∂μ) =
        ∫ _ in cell ε η a, m⁻¹ * u a ∂μ := integral_congr_ae heq
    _ = ε * (m⁻¹ * u a) := by
      simp [measureReal_def, measure_cell_of_area_parametrized hη hε,
        ENNReal.toReal_ofReal hε.le, mul_comm]

/-- A rescaled vertex function is integrable on each individual cell. -/
theorem integrableOn_rescale_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ) (m : ℝ) (u : ℤ → ℝ) :
    IntegrableOn (rescale m ε η u) (cell ε η a) μ := by
  have heq : (fun x => rescale m ε η u x) =ᵐ[μ.restrict (cell ε η a)]
      fun _ => m⁻¹ * u a := by
    filter_upwards [ae_vertexOf_eq_on_cell hη hp hε a] with x hx
    simp [rescale, hx]
  apply (integrable_congr heq).2
  exact integrableOn_const (by rw [measure_cell_of_area_parametrized hη hε]; exact ENNReal.ofReal_ne_top)

/-- Integration over finitely many cells is the corresponding finite sum of
vertex values times the cell mass. Overlaps between cells are null. -/
theorem setIntegral_rescale_finset_cells {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (F : Finset ℤ) (m : ℝ) (u : ℤ → ℝ) :
    (∫ x in ⋃ a ∈ F, cell ε η a, rescale m ε η u x ∂μ) =
      ∑ a ∈ F, ε * (m⁻¹ * u a) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union₀, setIntegral_rescale_cell hη hp hε, ih]
    · simp only [AEDisjoint.iUnion_right_iff]
      intro b hb
      show μ (cell ε η a ∩ cell ε η b) = 0
      have hne : a ≠ b := fun h => ha (h ▸ hb)
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact ConstantOrder.cell_inter_null hη hε hab
      · rw [inter_comm]
        exact ConstantOrder.cell_inter_null hη hε hba
    · exact (Finset.measurableSet_biUnion F fun b _ =>
        (isCompact_Icc.image hη.1).isClosed.measurableSet).nullMeasurableSet
    · exact integrableOn_rescale_cell hη hp hε a m u
    · exact integrableOn_finset_iUnion.2 (fun b _ => integrableOn_rescale_cell hη hp hε b m u)

/-- The ε-normalized cell integral equals the normalized finite vertex sum.
This is the exact sum-integral identity used for truncated Green kernels. -/
theorem setIntegral_rescale_inv_epsilon_finset_cells {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (F : Finset ℤ) (m : ℝ) (u : ℤ → ℝ) :
    (∫ x in ⋃ a ∈ F, cell ε η a, rescale m ε η (fun a => ε⁻¹ * u a) x ∂μ) =
      m⁻¹ * ∑ a ∈ F, u a := by
  rw [setIntegral_rescale_finset_cells hη hp hε, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  field_simp

end MatedCRT
