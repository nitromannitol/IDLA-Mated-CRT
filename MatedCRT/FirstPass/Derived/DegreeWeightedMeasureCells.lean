import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize

/-!
# The degree-weighted measure as a finite sum over cells

The measure `μ^ε_h` of Lemma 2.10 (BG20 Corollary A.6) restricts on each cell `H^ε_a` to
`deg^ε(a) μ_h|_{H^ε_a}` (`degreeWeightedMeasure`). For a continuous `f` vanishing on all cells outside a
finite set `t` of indices, the integral of `f` against `μ^ε_h` is the degree-weighted sum of the
integrals of `f` over the cells of `t`. For an area-parametrized curve each cell has `μ_h`-mass `ε`, so
this integral is `ε ∑_{a ∈ t} deg^ε(a) f(w_a)` for points `w_a ∈ H^ε_a`, up to `ε` times the
degree-weighted oscillations of `f` on the cells. This is the first step of the proof of BG20
Corollary A.6 from BG20 Lemma A.5.

* `integrable_degreeWeightedMeasure`, `integral_degreeWeightedMeasure_eq_sum`;
* `IsAreaParametrized.integrableOn_cell`, `IsAreaParametrized.abs_setIntegral_cell_sub_le`;
* `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_le`.
-/

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ} {f : ℂ → ℝ}

/-- A continuous function vanishing on every cell outside the finite set `t`, and integrable on the
cells of `t`, is integrable for the degree-weighted measure. -/
theorem integrable_degreeWeightedMeasure (hf : Continuous f) (hη : Continuous η) (t : Finset ℤ)
    (hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, f x = 0) (hint : ∀ k ∈ t, IntegrableOn f (cell ε η k) μ) :
    Integrable f (degreeWeightedMeasure m ε η μ) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, degreeWeightedMeasure, lintegral_sum_measure]
  have hzero : ∀ k ∉ t,
      ∫⁻ x, ‖f x‖ₑ ∂(((matedDeg m k : ℕ) : ℝ≥0∞) • μ.restrict (cell ε η k)) = 0 := by
    intro k hk
    rw [lintegral_smul_measure]
    have hs : MeasurableSet (cell ε η k) := (isCompact_cell hη ε k).isClosed.measurableSet
    rw [setLIntegral_congr_fun hs (g := fun _ => 0) (fun x hx => by simp [hvan k hk x hx])]
    simp
  rw [tsum_eq_sum (s := t) hzero]
  refine ENNReal.sum_lt_top.2 fun k hk => ?_
  rw [lintegral_smul_measure]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hint k hk).2

/-- The integral of `f` against the degree-weighted measure is the degree-weighted sum of its
integrals over the cells of `t`, when `f` vanishes on the other cells. -/
theorem integral_degreeWeightedMeasure_eq_sum (hf : Continuous f) (hη : Continuous η)
    (t : Finset ℤ) (hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, f x = 0)
    (hint : ∀ k ∈ t, IntegrableOn f (cell ε η k) μ) :
    ∫ x, f x ∂degreeWeightedMeasure m ε η μ =
      ∑ k ∈ t, (matedDeg m k : ℝ) * ∫ x in cell ε η k, f x ∂μ := by
  have hI := integrable_degreeWeightedMeasure (m := m) hf hη t hvan hint
  rw [degreeWeightedMeasure] at hI ⊢
  rw [integral_sum_measure hI, tsum_eq_sum (s := t)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure]
    simp
  · intro k hk
    rw [integral_smul_measure, setIntegral_eq_zero_of_forall_eq_zero (hvan k hk)]
    simp

/-- A continuous function is integrable on each cell of an area-parametrized curve. -/
theorem IsAreaParametrized.integrableOn_cell (hpar : IsAreaParametrized μ η) (hε : 0 < ε)
    (hf : Continuous f) (k : ℤ) : IntegrableOn f (cell ε η k) μ := by
  have hK := isCompact_cell hpar.1 ε k
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hfin : μ (cell ε η k) ≠ ∞ := by
    rw [hpar.measure_cell hε k]
    exact ENNReal.ofReal_ne_top
  exact Measure.integrableOn_of_bounded (M := C) hfin hf.aestronglyMeasurable
    ((ae_restrict_iff' hK.isClosed.measurableSet).2 (Eventually.of_forall hC))

/-- On a cell of `μ`-mass `ε`, the integral of `f` is `ε f(w)` up to `ε` times the oscillation bound
`K` of `f` around `w`. -/
theorem IsAreaParametrized.abs_setIntegral_cell_sub_le (hpar : IsAreaParametrized μ η)
    (hε : 0 < ε) (hf : Continuous f) (k : ℤ) {w : ℂ} {K : ℝ}
    (hK : ∀ x ∈ cell ε η k, |f x - f w| ≤ K) :
    |∫ x in cell ε η k, f x ∂μ - ε * f w| ≤ ε * K := by
  have hmeas := hpar.measure_cell hε k
  have hfin : μ (cell ε η k) < ∞ := by rw [hmeas]; exact ENNReal.ofReal_lt_top
  have hconst : ∫ _ in cell ε η k, f w ∂μ = ε * f w := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hmeas, ENNReal.toReal_ofReal hε.le]
  have hsub : ∫ x in cell ε η k, f x ∂μ - ε * f w = ∫ x in cell ε η k, (f x - f w) ∂μ := by
    rw [integral_sub (hpar.integrableOn_cell hε hf k) (integrableOn_const hfin.ne), hconst]
  rw [hsub]
  have h := norm_setIntegral_le_of_norm_le_const hfin
    (f := fun x => f x - f w) (fun x hx => by simpa [Real.norm_eq_abs] using hK x hx)
  rw [Real.norm_eq_abs, measureReal_def, hmeas, ENNReal.toReal_ofReal hε.le] at h
  linarith

/-- The integral of `f` against the degree-weighted measure is `ε ∑_{k ∈ t} deg(k) f(w_k)` up to
`ε ∑_{k ∈ t} deg(k) K_k`, where `K_k` bounds the oscillation of `f` on the cell `k` around `w_k`. -/
theorem IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_le
    (hpar : IsAreaParametrized μ η) (hε : 0 < ε) (hf : Continuous f) (t : Finset ℤ)
    (hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, f x = 0) (w : ℤ → ℂ) (K : ℤ → ℝ)
    (hK : ∀ k ∈ t, ∀ x ∈ cell ε η k, |f x - f (w k)| ≤ K k) :
    |∫ x, f x ∂degreeWeightedMeasure m ε η μ - ε * ∑ k ∈ t, (matedDeg m k : ℝ) * f (w k)| ≤
      ε * ∑ k ∈ t, (matedDeg m k : ℝ) * K k := by
  rw [integral_degreeWeightedMeasure_eq_sum hf hpar.1 t hvan
    (fun k _ => hpar.integrableOn_cell hε hf k), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hd : (0 : ℝ) ≤ (matedDeg m k : ℝ) := Nat.cast_nonneg _
  have h := hpar.abs_setIntegral_cell_sub_le hε hf k (hK k hk)
  calc |(matedDeg m k : ℝ) * ∫ x in cell ε η k, f x ∂μ - ε * ((matedDeg m k : ℝ) * f (w k))|
      = (matedDeg m k : ℝ) * |∫ x in cell ε η k, f x ∂μ - ε * f (w k)| := by
        rw [← abs_of_nonneg hd, ← abs_mul, abs_of_nonneg hd]; ring_nf
    _ ≤ (matedDeg m k : ℝ) * (ε * K k) := mul_le_mul_of_nonneg_left h hd
    _ = ε * ((matedDeg m k : ℝ) * K k) := by ring

end MatedCRT
