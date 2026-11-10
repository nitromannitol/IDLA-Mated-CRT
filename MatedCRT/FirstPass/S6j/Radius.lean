import MatedCRT.FirstPass.S6e.RadiusSelect
import MatedCRT.FirstPass.S6j.StateGood

/-!
# The radius inputs of the state test from the selection bound (fp-S6j; `hRs`, `hLR` of `hloc_of_goodState`)

The state radius is selected in `selectable (Delta p r)` (`Lemma68Radius.firstGood_cand_mem`, default `Δ(r)`).
Write-up (20) (`Lemma68Scales`): `Δ(r) ≤ r^p`, `r^p/2 < Δ(r)` and `√Δ(r) ≤ r^{p/2}`. Hence for a selectable `ρ`:
* `ρ ≤ r^{p/2}` (`selectable_le_rpow_half`);
* `c₀ ρ ≤ r` for `p ≥ 2` (`mul_le_of_selectable`): the printed hypothesis `hRr` (`ball(c₀R) ⊆ ball(r)`) of `printed_test_bound`;
* `1 + log(1/r) ≤ (1 + 2/p)(1 + log(1/ρ))` (`one_add_log_inv_le_of_selectable`): the scale conversion `hLR`, which turns
  the printed denominator `(1 + log(1/r))²` into the state denominator `(1 + log(1/R))²`.
`hloc_of_selected` is `hloc_of_goodState` with `hRs`, `hLR`, `qStar` discharged from the selection.
-/

open MeasureTheory Set Filter

namespace MatedCRT
open Lemma68Scales Lemma68Radius

namespace S6j

lemma delta_le_one_of {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) : Delta p r ≤ 1 :=
  (Delta_le_rpow hp hr0 hr1).trans (Real.rpow_le_one hr0.le hr1.le hp.le)

/-- A selectable radius is positive. -/
lemma selectable_pos_of {p r ρ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hρ : ρ ∈ selectable (Delta p r)) : 0 < ρ :=
  lt_of_lt_of_le (delta_pos p r) (selectable_bounds (delta_pos p r) (delta_le_one_of hp hr0 hr1) hρ).1

/-- A selectable radius lies below `r^{p/2}` (write-up (20): `ρ ≤ √Δ(r) ≤ r^{p/2}`). -/
lemma selectable_le_rpow_half {p r ρ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hρ : ρ ∈ selectable (Delta p r)) : ρ ≤ r ^ (p / 2) :=
  (selectable_bounds (delta_pos p r) (delta_le_one_of hp hr0 hr1) hρ).2.trans (sScale_le_rpow_half hp hr0 hr1)

/-- The printed hypothesis `hRr` of `printed_test_bound`: `c₀ ρ ≤ r` for a selectable `ρ`, when `p ≥ 2`. -/
lemma mul_le_of_selectable {p r ρ c0 : ℝ} (hp : 2 ≤ p) (hr0 : 0 < r) (hr1 : r < 1) (hc1 : c0 ≤ 1)
    (hρ : ρ ∈ selectable (Delta p r)) : c0 * ρ ≤ r := by
  have hp0 : 0 < p := by linarith
  have hρ0 : 0 < ρ := selectable_pos_of hp0 hr0 hr1 hρ
  have hpow : r ^ (p / 2) ≤ r := by
    calc r ^ (p / 2) ≤ r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le (by linarith)
      _ = r := Real.rpow_one r
  exact (mul_le_of_le_one_left hρ0.le hc1).trans ((selectable_le_rpow_half hp0 hr0 hr1 hρ).trans hpow)

/-- The scale conversion `hLR`: `1 + log(1/r) ≤ (1 + 2/p)(1 + log(1/ρ))` for a selectable `ρ` (from `ρ ≤ r^{p/2}`). -/
lemma one_add_log_inv_le_of_selectable {p r ρ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hρ : ρ ∈ selectable (Delta p r)) :
    1 + Real.log (1 / r) ≤ (1 + 2 / p) * (1 + Real.log (1 / ρ)) := by
  have hρ0 : 0 < ρ := selectable_pos_of hp hr0 hr1 hρ
  have hlog : Real.log ρ ≤ p / 2 * Real.log r := by
    calc Real.log ρ ≤ Real.log (r ^ (p / 2)) :=
          Real.log_le_log hρ0 (selectable_le_rpow_half hp hr0 hr1 hρ)
      _ = p / 2 * Real.log r := Real.log_rpow hr0 _
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div hr0).2 hr1.le)
  have e1 : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  have e2 : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
  have hM : p / 2 * Real.log (1 / r) ≤ Real.log (1 / ρ) := by
    rw [e1, e2]
    nlinarith
  have hpos : 0 < 2 / p := div_pos two_pos hp
  have hk : 2 / p * (p / 2) = 1 := by field_simp
  have hexp : (1 + 2 / p) * (1 + p / 2 * Real.log (1 / r))
      = 1 + p / 2 * Real.log (1 / r) + 2 / p + Real.log (1 / r) := by
    linear_combination Real.log (1 / r) * hk
  have h2 : 1 + Real.log (1 / r) ≤ (1 + 2 / p) * (1 + p / 2 * Real.log (1 / r)) := by
    rw [hexp]
    nlinarith [mul_nonneg (le_of_lt (half_pos hp)) hL]
  have h1 : (1 + 2 / p) * (1 + p / 2 * Real.log (1 / r)) ≤ (1 + 2 / p) * (1 + Real.log (1 / ρ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  exact h2.trans h1

/-- The printed-to-state constant: `q₀ / (1 + 2/p)²` with `q₀ = 1/(288 C_d² K²)`, `K = C_g(1+(log 4-1))/(1-log 2)`. -/
noncomputable def stateQStar (p Cd Cg : ℝ) : ℝ :=
  1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2) / (1 + 2 / p) ^ 2

/-- **`hloc` of `StateTestInputs` from the selection bound.** With the selected radii `Rs y ∈ selectable (Delta p r)` at the
good states, `p ≥ 2`, `p ≤ 3` (printed hypothesis), the thickening `δs y ≤ Rs y/100` and the good-event inputs `hGood`,
the local bound holds with `qStar = stateQStar p Cd Cg` in the denominator `(1 + log(1/Rs y))²`. -/
theorem hloc_of_selected {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε c0 C Cd Cg s1 β p r : ℝ} {Z : ℤ → ℂ} {Rs δs : ℤ → ℝ} {Good : ℤ → Prop}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hs1 : 0 < s1)
    (hp2 : 2 ≤ p) (hp3 : p ≤ 3) (hr0 : 0 < r) (hr1 : r < 1)
    (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hsel : ∀ y, Good y → Rs y ∈ selectable (Delta p r))
    (hδs : ∀ y, Good y → δs y ≤ Rs y / 100)
    (hGood : ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y),
      GoodVertexInputs μ η m A ε c0 C Cd Cg s1 β (δs y) r (Z y) (Rs y) v) :
    ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y),
      srwLaw m v (TestBound68.stayIn
        (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (Rs y / 4))) A v) ≤
        ENNReal.ofReal (1 - min (stateQStar p Cd Cg) 1 / (1 + Real.log (1 / Rs y)) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hKL : 0 < 1 + 2 / p := by have := div_pos two_pos hp0; linarith
  exact hloc_of_goodState (qStar := stateQStar p Cd Cg) (KL := 1 + 2 / p) hap hη hprop hε hs1 hr0 hr1.le
    hC hCd hCg hc0 hc0' hc0C hεc hp3 (fun y hy => by
      obtain ⟨h1, h2, h3⟩ := selectable_delta_bounds hp0 hr0 hr1 (hsel y hy)
      exact ⟨h1, h2, h3, mul_le_of_selectable hp2 hr0 hr1 (by linarith) (hsel y hy), hδs y hy⟩)
    hGood hKL (fun y hy => one_add_log_inv_le_of_selectable hp0 hr0 hr1 (hsel y hy)) (le_refl _)

end S6j

end MatedCRT
