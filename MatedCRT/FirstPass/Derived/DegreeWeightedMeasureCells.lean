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
* `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_le`;
* `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le`: the deterministic step from the
  conclusion of BG20 Lemma A.5 to `|∫ f dμ^ε_h - 6 ∫ f dμ_h|` small;
* `abs_mul_sub_six_integral_le_of_bounds`: the two-sided bound of Lemma A.5 for an `f` vanishing near
  `∂D` gives `|ε ∑ deg^ε(k) f(w_k) - 6 ∫ f dμ_h| ≤ ε^α`.
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

/-- A sum over the vertices `V^ε(D)` whose cells meet `D` is a finite sum when `V^ε(D)` is the finite
set `t`. -/
theorem tsum_cellVertices_eq_sum {D : Set ℂ} (t : Finset ℤ)
    (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η D) (g : ℤ → ℝ) :
    ∑' k : cellVertices ε η D, g k = ∑ k ∈ t, g k := by
  classical
  rw [tsum_subtype (cellVertices ε η D) g, tsum_eq_sum (s := t)]
  · exact Finset.sum_congr rfl fun k hk => indicator_of_mem ((ht k).1 hk) _
  · intro k hk
    exact indicator_of_notMem (fun h => hk ((ht k).2 h)) _

/-- **Deterministic core of BG20 Corollary A.6.** Let `f` be `L`-Lipschitz and vanish off `D`, let
`t = V^ε(D)` be finite, with points `w_k ∈ H^ε_k`, cells of diameter at most `δ`, the degree-weighted
counting sum within `e` of `6 ∫ f dμ_h` (the conclusion of BG20 Lemma A.5) and the degree sum
`ε ∑_{k ∈ t} deg^ε(k)` at most `B`. Then `∫ f dμ^ε_h` is within `e + L δ B` of `6 ∫ f dμ_h`. -/
theorem IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le
    (hpar : IsAreaParametrized μ η) (hε : 0 < ε) (hf : Continuous f) {D : Set ℂ}
    (hDf : ∀ x ∉ D, f x = 0) (t : Finset ℤ) (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η D)
    (w : ℤ → ℂ) (hw : ∀ k ∈ t, w k ∈ cell ε η k) {L δ B e : ℝ} (hL0 : 0 ≤ L) (hδ : 0 ≤ δ)
    (hL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hdiam : ∀ k ∈ t, diam (cell ε η k) ≤ δ)
    (hsum : |ε * ∑ k ∈ t, (matedDeg m k : ℝ) * f (w k) - 6 * ∫ x, f x ∂μ| ≤ e)
    (hdeg : ε * ∑ k ∈ t, (matedDeg m k : ℝ) ≤ B) :
    |∫ x, f x ∂degreeWeightedMeasure m ε η μ - 6 * ∫ x, f x ∂μ| ≤ e + L * δ * B := by
  have hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, f x = 0 := by
    intro k hk x hx
    by_contra hfx
    exact hk ((ht k).2 ⟨x, hx, by_contra fun hxD => hfx (hDf x hxD)⟩)
  have hK : ∀ k ∈ t, ∀ x ∈ cell ε η k, |f x - f (w k)| ≤ L * δ := by
    intro k hk x hx
    have hb := (isCompact_cell hpar.1 ε k).isBounded
    have h1 : ‖x - w k‖ ≤ δ := by
      rw [← dist_eq_norm]
      exact (dist_le_diam_of_mem hb hx (hw k hk)).trans (hdiam k hk)
    exact (hL x (w k)).trans (mul_le_mul_of_nonneg_left h1 hL0)
  have h1 := hpar.abs_integral_degreeWeightedMeasure_sub_le (m := m) hε hf t hvan w
    (fun _ => L * δ) hK
  have h2 : ε * ∑ k ∈ t, (matedDeg m k : ℝ) * (L * δ) ≤ L * δ * B := by
    rw [← Finset.sum_mul, ← mul_assoc, mul_comm _ (L * δ)]
    exact mul_le_mul_of_nonneg_left hdeg (mul_nonneg hL0 hδ)
  have h3 := abs_sub_le (∫ x, f x ∂degreeWeightedMeasure m ε η μ)
    (ε * ∑ k ∈ t, (matedDeg m k : ℝ) * f (w k)) (6 * ∫ x, f x ∂μ)
  linarith

/-- The two-sided bound of BG20 Lemma A.5,
`6 ε⁻¹ ∫_{S₁} f dμ - ε^{-1+α} ≤ X ≤ 6 ε⁻¹ ∫_{S₂} f dμ + ε^{-1+α}`, for an `f` vanishing off `S₁` and
off `S₂` (in Lemma A.5, `S₁ = D \ B_{ε^α}(∂D)` and `S₂ = B_{ε^α}(D)`), gives `|ε X - 6 ∫ f dμ| ≤ ε^α`. -/
theorem abs_mul_sub_six_integral_le_of_bounds (hε : 0 < ε) {α X : ℝ} {S₁ S₂ : Set ℂ}
    (hf₁ : ∀ x ∉ S₁, f x = 0) (hf₂ : ∀ x ∉ S₂, f x = 0)
    (hlo : 6 * ε⁻¹ * ∫ x in S₁, f x ∂μ - ε ^ (-1 + α) ≤ X)
    (hhi : X ≤ 6 * ε⁻¹ * ∫ x in S₂, f x ∂μ + ε ^ (-1 + α)) :
    |ε * X - 6 * ∫ x, f x ∂μ| ≤ ε ^ α := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hf₁] at hlo
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hf₂] at hhi
  have he : ε * ε ^ (-1 + α) = ε ^ α := by
    rw [Real.rpow_add hε, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  have hc : ε * (6 * ε⁻¹ * ∫ x, f x ∂μ) = 6 * ∫ x, f x ∂μ := by
    field_simp
  have h1 := mul_le_mul_of_nonneg_left hlo hε.le
  have h2 := mul_le_mul_of_nonneg_left hhi hε.le
  rw [mul_sub, hc, he] at h1
  rw [mul_add, hc, he] at h2
  rw [abs_le]
  constructor <;> linarith

end MatedCRT
