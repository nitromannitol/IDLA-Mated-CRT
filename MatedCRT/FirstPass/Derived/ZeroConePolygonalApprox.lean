import MatedCRT.FirstPass.Derived.ZeroConePolygonalMatch

/-!
# Countably valued approximations of the polygonal configuration

The Borel measurability of the polygonal cell configuration `polygonalConfig H₀` (with the default
point `H₀` off the valid data) follows the written measurability argument (section 2): record, at
each stage `n`, a countably valued combinatorial description of the polygonal configuration; choose
one realized datum in each record class; the polygonal configurations of the chosen data are
measurable maps with countable range, and they converge to the polygonal configuration in the metric
of Gwynne–Miller–Sheffield (arXiv:1807.07515v3, (1.14)–(1.15), p. 15), whose pointwise limits of
measurable maps are measurable (`measurable_of_tendsto_dCC`).

This file proves the scheme for an arbitrary record map `code n` with countable values:

* `repData`, `approxConfig`: the chosen representative of a record class and the approximation.
* `measurable_approxConfig`: the approximations are measurable when the record classes are.
* `tendsto_dCC_approxConfig`: they converge in `d^CC` when equal records at stage `n ≥ R` give
  matched `R`-patches with vertex displacement `2 · 2⁻ⁿ` (`PatchMatch`), with the matched data of
  `w` depending only on `w` and `R`, by the estimate `PatchMatch.dCC_le`.
* `measurable_polygonalConfig_of_records`: hence `polygonalConfig H₀` is measurable.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

/-! ## Countably valued approximations from records -/

section Approx

variable {α : ℕ → Type*} (code : ∀ n, (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) → α n)

open Classical in
/-- **One realized representative of a record class**: a datum with record `c` at stage `n` (the zero
datum if there is none). -/
def repData (n : ℕ) (c : α n) : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  if h : ∃ w, code n w = c then h.choose else 0

theorem code_repData (n : ℕ) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    code n (repData code n (code n w)) = code n w := by
  have h : ∃ w', code n w' = code n w := ⟨w, rfl⟩
  rw [repData, dite_eq_left h]
  exact h.choose_spec

/-- **The countably valued approximation** at stage `n`: the polygonal configuration of the chosen
representative of the record class of `w`. -/
def approxConfig (H₀ : GMSSpace) (n : ℕ) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : GMSSpace :=
  polygonalConfig H₀ (repData code n (code n w))

/-- The approximations are measurable as soon as the record classes are measurable. -/
theorem measurable_approxConfig [∀ n, Countable (α n)]
    (hrec : ∀ n c, MeasurableSet {w | code n w = c}) (H₀ : GMSSpace) (n : ℕ) :
    Measurable (approxConfig code H₀ n) := by
  intro T _
  have h : approxConfig code H₀ n ⁻¹' T =
      ⋃ c ∈ {c : α n | polygonalConfig H₀ (repData code n c) ∈ T}, {w | code n w = c} := by
    ext w
    constructor
    · intro hw
      exact mem_iUnion₂.2 ⟨code n w, hw, rfl⟩
    · intro hw
      obtain ⟨c, hc, hwc⟩ := mem_iUnion₂.1 hw
      show polygonalConfig H₀ (repData code n (code n w)) ∈ T
      rw [show code n w = c from hwc]
      exact hc
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun c _ => hrec n c

/-- **The approximations converge in `d^CC`** when equal records at stage `n ≥ R` give matched
`R`-patches with vertex displacement `2 · 2⁻ⁿ`, the matched data of `w` depending only on `w` and
`R`, and invalid data have records of invalid data only. -/
theorem tendsto_dCC_approxConfig {N : Type*} (H₀ : GMSSpace)
    (hnone : ∀ n w w', ¬ UnitMeshValid w → code n w' = code n w → ¬ UnitMeshValid w')
    (hmatch : ∀ w, UnitMeshValid w → ∀ R : ℕ, 1 ≤ R → ∃ (L : Finset ℤ) (S : Set N)
      (pos : N → Plane) (Φ : ℤ → Set (Set N)), S.Finite ∧ ∀ n, R ≤ n → ∀ w', code n w' = code n w →
        ∃ pos' : N → Plane, PatchMatch w w' R (2 * (1 / 2) ^ n) L S pos pos' Φ)
    (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    Tendsto (fun n => CellConfig.dCC (approxConfig code H₀ n w).1 (polygonalConfig H₀ w).1) atTop
      (𝓝 0) := by
  by_cases hw : UnitMeshValid w
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, -, hδpos, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδpos
    obtain ⟨R, hR1, hRexp⟩ : ∃ R : ℕ, 1 ≤ R ∧ Real.exp (-(R : ℝ)) < δ / 2 := by
      have h1 : Tendsto (fun R : ℕ => Real.exp (-(R : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
      exact ((eventually_ge_atTop 1).and (h1.eventually (gt_mem_nhds (by linarith)))).exists
    obtain ⟨L, S, pos, Φ, hS, hM⟩ := hmatch w hw R hR1
    obtain ⟨h, hh, hmin⟩ := hw.isSiteSystem.exists_le_minHeight (hS.image pos)
    have hb : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
    have hK : 0 < (R : ℝ) + 2 * L.card + 1 := by positivity
    filter_upwards [eventually_ge_atTop R, hb.eventually (gt_mem_nhds (show (0 : ℝ) < h / 4 by
        linarith)), hb.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 / ((R : ℝ) + 2 * L.card + 1)
        by positivity))] with n hn hbh hbδ
    obtain ⟨pos', hM'⟩ := hM n hn _ (code_repData code n w)
    have hb0 : 0 ≤ 2 * (1 / 2 : ℝ) ^ n := by positivity
    rw [approxConfig, dCC_symm]
    refine (hM'.dCC_le H₀ hb0 hh hmin (by linarith)).trans ?_
    have h1 : 0 ≤ (R : ℝ) * (2 * (1 / 2 : ℝ) ^ n) := by positivity
    have h2 : 0 ≤ (L.card : ℝ) * (2 * (2 * (1 / 2 : ℝ) ^ n)) := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) (Real.exp_pos _).le]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le
    rw [lt_div_iff₀ hK] at hbδ
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) L.card) hb0]
  · have h : ∀ n, approxConfig code H₀ n w = polygonalConfig H₀ w := fun n => by
      rw [approxConfig, polygonalConfig_of_not_valid (hnone n w _ hw (code_repData code n w)),
        polygonalConfig_of_not_valid hw]
    simp only [h, CellConfig.dCC_self]
    exact tendsto_const_nhds

/-- **Measurability of the polygonal configuration from records** (the scheme of the written
measurability argument, section 2): countably valued record maps with measurable classes whose equal
values give matched patches. -/
theorem measurable_polygonalConfig_of_records [∀ n, Countable (α n)] {N : Type*} (H₀ : GMSSpace)
    (hrec : ∀ n c, MeasurableSet {w | code n w = c})
    (hnone : ∀ n w w', ¬ UnitMeshValid w → code n w' = code n w → ¬ UnitMeshValid w')
    (hmatch : ∀ w, UnitMeshValid w → ∀ R : ℕ, 1 ≤ R → ∃ (L : Finset ℤ) (S : Set N)
      (pos : N → Plane) (Φ : ℤ → Set (Set N)), S.Finite ∧ ∀ n, R ≤ n → ∀ w', code n w' = code n w →
        ∃ pos' : N → Plane, PatchMatch w w' R (2 * (1 / 2) ^ n) L S pos pos' Φ) :
    Measurable (polygonalConfig H₀) :=
  measurable_of_tendsto_dCC (measurable_approxConfig code hrec H₀)
    (tendsto_dCC_approxConfig code H₀ hnone hmatch)

end Approx

end MatedCRT.ZeroConePolygonal
