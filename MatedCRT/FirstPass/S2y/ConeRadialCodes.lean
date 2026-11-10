import MatedCRT.Defs.QuantumCone
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Radial and sphere-average codes of a quantum cone (fp-S2y-cone-codes, chat 231 §§1-3)

Duplantier-Sheffield (arXiv:1409.7055, Definition 4.10) and Armstrong-Kuusi-Mourrat style decoders for the circle average
process: the pairings `(h, φ)` and the circle averages `h_r(z)` of a `γ`-quantum cone are recovered from countably many
circle coordinates, by finite Riemann sums followed by `limsup`.

Section 1 (this part): the shared countable reconstruction layer.
* `planeQuad n f`: the midpoint Riemann sum of `f` on the `N_n × N_n` grid of `[-R_n, R_n]²`, `N_n = 2^(n+1)`,
  `R_n = n + 1`, times `Δ_n²`. `planeQuad_tendsto_integral`: convergence to `∫ f` for continuous compactly supported `f`.
* `angleQuad n g`: the midpoint sum of `g` on `[0, 2π]` with `N_n` cells. `angleQuad_tendsto_circleAverage`.
* `measurable_planeQuad_eval`, `measurable_angleQuad_eval`: finite sums of constants times coordinates of `q` are Borel.

Only deterministic analysis is used here. The grid sums are finite sums, so the codes of sections 2-3 depend on countably many
coordinates of the circle process.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Real

namespace MatedCRT

noncomputable section

/-! ### Grid data -/

/-- Grid size `N_n = 2^(n+1)` of the level-`n` quadrature (chat 231, §1.1). -/
def planeN (n : ℕ) : ℕ := 2 ^ (n + 1)

/-- Half-width `R_n = n + 1` of the level-`n` plane box `[-R_n, R_n]²`. -/
def planeR (n : ℕ) : ℝ := (n : ℝ) + 1

/-- Mesh `Δ_n = 2 R_n / N_n` of the level-`n` grid. -/
def planeDelta (n : ℕ) : ℝ := 2 * planeR n / (planeN n : ℝ)

/-- The `i`-th grid line `-R_n + i Δ_n`, for `i = 0, …, N_n`. -/
def planeLine (n i : ℕ) : ℝ := -planeR n + (i : ℝ) * planeDelta n

/-- Midpoint `c_{ij}` of the `(i,j)`-th cell of the level-`n` grid. -/
def planeCenter (n i j : ℕ) : ℂ :=
  ⟨planeLine n i + planeDelta n / 2, planeLine n j + planeDelta n / 2⟩

/-- The half-open `(i,j)`-th cell `[L_i, L_{i+1}) × [L_j, L_{j+1})` of the level-`n` grid. -/
def planeCell (n i j : ℕ) : Set ℂ :=
  {z | z.re ∈ Ico (planeLine n i) (planeLine n (i + 1)) ∧ z.im ∈ Ico (planeLine n j) (planeLine n (j + 1))}

/-- **Midpoint Riemann sum on the plane grid** (chat 231, §1.1): `planeQuad n f = ∑_{i,j} Δ_n² f(c_{ij})`. Only the values
of `f` at the midpoints enter, which are countably many points. -/
def planeQuad (n : ℕ) (f : ℂ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (planeN n), ∑ j ∈ Finset.range (planeN n), planeDelta n ^ 2 * f (planeCenter n i j)

/-- **Midpoint sum on the circle** (chat 231, §1.1): `angleQuad n g = N_n⁻¹ ∑_j g(2π (j+1/2) / N_n)`. -/
def angleQuad (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  ((planeN n : ℝ))⁻¹ * ∑ j ∈ Finset.range (planeN n), g (2 * π * ((j : ℝ) + 1 / 2) / (planeN n : ℝ))

lemma planeN_pos (n : ℕ) : (0 : ℝ) < planeN n := by
  unfold planeN; positivity

lemma planeR_pos (n : ℕ) : 0 < planeR n := by
  unfold planeR; positivity

lemma planeDelta_pos (n : ℕ) : 0 < planeDelta n := by
  unfold planeDelta
  have := planeN_pos n
  have := planeR_pos n
  positivity

lemma planeDelta_eq (n : ℕ) : planeDelta n = ((n : ℝ) + 1) * (1 / 2) ^ n := by
  unfold planeDelta planeR planeN
  push_cast
  rw [pow_succ, one_div, inv_pow]
  field_simp

lemma planeN_mul_delta (n : ℕ) : (planeN n : ℝ) * planeDelta n = 2 * planeR n := by
  unfold planeDelta
  have := planeN_pos n
  field_simp

lemma planeLine_zero (n : ℕ) : planeLine n 0 = -planeR n := by
  simp [planeLine]

lemma planeLine_last (n : ℕ) : planeLine n (planeN n) = planeR n := by
  unfold planeLine
  have h := planeN_mul_delta n
  linarith

lemma planeLine_succ (n i : ℕ) : planeLine n (i + 1) = planeLine n i + planeDelta n := by
  unfold planeLine
  push_cast
  ring

lemma planeLine_monotone (n : ℕ) : Monotone (planeLine n) := by
  intro a b hab
  unfold planeLine
  have h1 : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h2 := planeDelta_pos n
  nlinarith

/-- Distinct cells are disjoint in each coordinate: a point of `Ico (L k) (L (k+1))` is not in `Ico (L i) (L (i+1))` for
`i ≠ k`, when `L` is monotone. -/
lemma not_mem_Ico_of_ne {L : ℕ → ℝ} (hL : Monotone L) {i k : ℕ} (hik : i ≠ k) {x : ℝ}
    (hx : x ∈ Ico (L k) (L (k + 1))) : x ∉ Ico (L i) (L (i + 1)) := by
  intro h
  rcases lt_or_gt_of_ne hik with h1 | h1
  · have : L (i + 1) ≤ L k := hL (Nat.succ_le_of_lt h1)
    linarith [h.2, hx.1]
  · have : L (k + 1) ≤ L i := hL (Nat.succ_le_of_lt h1)
    linarith [h.1, hx.2]

/-! ### Cells: measure and measurability -/

lemma planeCell_eq_preimage (n i j : ℕ) :
    planeCell n i j = Complex.measurableEquivRealProd ⁻¹'
      (Ico (planeLine n i) (planeLine n (i + 1)) ×ˢ Ico (planeLine n j) (planeLine n (j + 1))) := rfl

lemma measurableSet_planeCell (n i j : ℕ) : MeasurableSet (planeCell n i j) := by
  rw [planeCell_eq_preimage]
  exact (measurableSet_Ico.prod measurableSet_Ico).preimage Complex.measurableEquivRealProd.measurable

lemma volume_planeCell (n i j : ℕ) :
    volume (planeCell n i j) = ENNReal.ofReal (planeDelta n ^ 2) := by
  rw [planeCell_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ico, Real.volume_Ico]
  have h1 : planeLine n (i + 1) - planeLine n i = planeDelta n := by rw [planeLine_succ]; ring
  have h2 : planeLine n (j + 1) - planeLine n j = planeDelta n := by rw [planeLine_succ]; ring
  rw [h1, h2, ← ENNReal.ofReal_mul (planeDelta_pos n).le, sq]

/-! ### The step function of the midpoint sum -/

/-- The step function of the midpoint sum: on the cell `(i,j)` it equals `f(c_{ij})`, and it vanishes off the grid. -/
def planeStep (n : ℕ) (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∑ i ∈ Finset.range (planeN n), ∑ j ∈ Finset.range (planeN n),
    (planeCell n i j).indicator (fun _ => f (planeCenter n i j)) z

lemma integrable_planeCell_indicator (n i j : ℕ) (c : ℝ) :
    Integrable ((planeCell n i j).indicator (fun _ => c)) := by
  refine (integrableOn_const ?_).integrable_indicator (measurableSet_planeCell n i j)
  rw [volume_planeCell]
  exact ENNReal.ofReal_ne_top

lemma integrable_planeStep (n : ℕ) (f : ℂ → ℝ) : Integrable (planeStep n f) := by
  unfold planeStep
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_planeCell_indicator n i j _

/-- The integral of the step function is the midpoint sum. -/
lemma integral_planeStep (n : ℕ) (f : ℂ → ℝ) : ∫ z, planeStep n f z = planeQuad n f := by
  have hint : ∀ i j : ℕ, ∫ z, (planeCell n i j).indicator (fun _ => f (planeCenter n i j)) z
      = planeDelta n ^ 2 * f (planeCenter n i j) := by
    intro i j
    rw [integral_indicator_const _ (measurableSet_planeCell n i j), measureReal_def, volume_planeCell,
      ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]
  unfold planeStep planeQuad
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_planeCell_indicator n i j _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_planeCell_indicator n i j _]
  exact Finset.sum_congr rfl fun j _ => hint i j

/-- On a cell `(k,l)` of the grid the step function takes the value `f(c_{kl})`. -/
lemma planeStep_of_mem (n : ℕ) (f : ℂ → ℝ) {z : ℂ} {k l : ℕ} (hk : k < planeN n) (hl : l < planeN n)
    (hz : z ∈ planeCell n k l) : planeStep n f z = f (planeCenter n k l) := by
  have hz' : z.re ∈ Ico (planeLine n k) (planeLine n (k + 1)) ∧
      z.im ∈ Ico (planeLine n l) (planeLine n (l + 1)) := hz
  unfold planeStep
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · exact Set.indicator_of_mem hz _
    · intro j _ hjl
      refine Set.indicator_of_notMem (fun h => ?_) _
      have h' : z.im ∈ Ico (planeLine n j) (planeLine n (j + 1)) ∧
          z.re ∈ Ico (planeLine n k) (planeLine n (k + 1)) := ⟨h.2, hz'.1⟩
      exact not_mem_Ico_of_ne (planeLine_monotone n) hjl hz'.2 h'.1
    · intro h; exact absurd (Finset.mem_range.2 hl) h
  · intro i _ hik
    refine Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (fun h => ?_) _
    have h' : z.re ∈ Ico (planeLine n i) (planeLine n (i + 1)) := h.1
    exact not_mem_Ico_of_ne (planeLine_monotone n) hik hz'.1 h'
  · intro h; exact absurd (Finset.mem_range.2 hk) h

/-- Grid index of a coordinate in `[-R_n, R_n)`. -/
lemma exists_mem_Ico_planeLine (n : ℕ) {t : ℝ} (ht : t ∈ Ico (-planeR n) (planeR n)) :
    ∃ k : ℕ, k < planeN n ∧ t ∈ Ico (planeLine n k) (planeLine n (k + 1)) := by
  have hD := planeDelta_pos n
  have hNd := planeN_mul_delta n
  have hR := planeR_pos n
  set x := (t + planeR n) / planeDelta n with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [ht.1]) hD.le
  have hxN : x < (planeN n : ℝ) := by
    rw [hx, div_lt_iff₀ hD]
    linarith [ht.2]
  refine ⟨⌊x⌋₊, (Nat.floor_lt hx0).2 hxN, ?_, ?_⟩
  · have h1 := Nat.floor_le hx0
    have h2 : (⌊x⌋₊ : ℝ) * planeDelta n ≤ x * planeDelta n := mul_le_mul_of_nonneg_right h1 hD.le
    have h3 : x * planeDelta n = t + planeR n := by rw [hx, div_mul_cancel₀ _ hD.ne']
    unfold planeLine
    linarith
  · have h2 := Nat.lt_floor_add_one x
    have h3 : x * planeDelta n = t + planeR n := by rw [hx, div_mul_cancel₀ _ hD.ne']
    have h4 : x * planeDelta n < ((⌊x⌋₊ : ℝ) + 1) * planeDelta n := mul_lt_mul_of_pos_right h2 hD
    unfold planeLine
    push_cast
    linarith

/-- Every point of the open box `(-R_n, R_n)²`-type region `[-R_n, R_n)²` lies in a grid cell. -/
lemma exists_mem_planeCell (n : ℕ) {z : ℂ} (hre : z.re ∈ Ico (-planeR n) (planeR n))
    (him : z.im ∈ Ico (-planeR n) (planeR n)) :
    ∃ k l : ℕ, k < planeN n ∧ l < planeN n ∧ z ∈ planeCell n k l := by
  obtain ⟨k, hk, hkre⟩ := exists_mem_Ico_planeLine n hre
  obtain ⟨l, hl, hlim⟩ := exists_mem_Ico_planeLine n him
  exact ⟨k, l, hk, hl, ⟨hkre, hlim⟩⟩

/-- The step function vanishes off the box `[-R_n, R_n)²`, since no cell of the grid meets its complement. -/
lemma planeStep_eq_zero_of_not_box (n : ℕ) (f : ℂ → ℝ) {z : ℂ}
    (hz : ¬ (z.re ∈ Ico (-planeR n) (planeR n) ∧ z.im ∈ Ico (-planeR n) (planeR n))) :
    planeStep n f z = 0 := by
  unfold planeStep
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  have hi' : i < planeN n := Finset.mem_range.1 hi
  have hj' : j < planeN n := Finset.mem_range.1 hj
  refine Set.indicator_of_notMem (fun h => hz ⟨?_, ?_⟩) _
  · have h' : z.re ∈ Ico (planeLine n i) (planeLine n (i + 1)) := h.1
    have h0 : planeLine n 0 ≤ planeLine n i := planeLine_monotone n (Nat.zero_le i)
    have h1 : planeLine n (i + 1) ≤ planeLine n (planeN n) := planeLine_monotone n hi'
    rw [planeLine_zero] at h0
    rw [planeLine_last] at h1
    exact ⟨le_trans h0 h'.1, lt_of_lt_of_le h'.2 h1⟩
  · have h' : z.im ∈ Ico (planeLine n j) (planeLine n (j + 1)) := h.2
    have h0 : planeLine n 0 ≤ planeLine n j := planeLine_monotone n (Nat.zero_le j)
    have h1 : planeLine n (j + 1) ≤ planeLine n (planeN n) := planeLine_monotone n hj'
    rw [planeLine_zero] at h0
    rw [planeLine_last] at h1
    exact ⟨le_trans h0 h'.1, lt_of_lt_of_le h'.2 h1⟩

/-- Outside the box `[-R_n, R_n)²` the modulus of `z` is at least `R_n`. -/
lemma planeR_le_norm_of_not_box (n : ℕ) {z : ℂ}
    (hz : ¬ (z.re ∈ Ico (-planeR n) (planeR n) ∧ z.im ∈ Ico (-planeR n) (planeR n))) :
    planeR n ≤ ‖z‖ := by
  by_contra h
  rw [not_le] at h
  apply hz
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  exact ⟨⟨(abs_lt.1 (lt_of_le_of_lt hre h)).1.le, (abs_lt.1 (lt_of_le_of_lt hre h)).2⟩,
    ⟨(abs_lt.1 (lt_of_le_of_lt him h)).1.le, (abs_lt.1 (lt_of_le_of_lt him h)).2⟩⟩

/-- The grid centre is within `Δ_n` of every point of its cell. -/
lemma dist_planeCenter_le {n k l : ℕ} {z : ℂ} (hz : z ∈ planeCell n k l) :
    dist (planeCenter n k l) z ≤ planeDelta n := by
  have hz' : z.re ∈ Ico (planeLine n k) (planeLine n (k + 1)) ∧
      z.im ∈ Ico (planeLine n l) (planeLine n (l + 1)) := hz
  have hD := planeDelta_pos n
  have hsk := planeLine_succ n k
  have hsl := planeLine_succ n l
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |planeLine n k + planeDelta n / 2 - z.re| ≤ planeDelta n / 2 := by
    rw [abs_le]
    constructor <;> linarith [hz'.1.1, hz'.1.2]
  have him : |planeLine n l + planeDelta n / 2 - z.im| ≤ planeDelta n / 2 := by
    rw [abs_le]
    constructor <;> linarith [hz'.2.1, hz'.2.2]
  have e1 : (planeCenter n k l - z).re = planeLine n k + planeDelta n / 2 - z.re := by
    simp [planeCenter]
  have e2 : (planeCenter n k l - z).im = planeLine n l + planeDelta n / 2 - z.im := by
    simp [planeCenter]
  rw [e1, e2]
  linarith

/-! ### Convergence of the plane midpoint sums -/

/-- **Error of the plane midpoint sum.** If `f` vanishes off the ball of radius `S`, `Δ_n ≤ 1`, `S + 2 ≤ R_n`, and `f` varies
by at most `η` on distances `≤ Δ_n`, then `|planeQuad n f - ∫ f| ≤ η · vol(B(0, S+1))`. -/
lemma abs_planeQuad_sub_integral_le {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {S : ℝ}
    (hS : ∀ z : ℂ, S < ‖z‖ → f z = 0) {n : ℕ} (hΔ : planeDelta n ≤ 1) (hR : S + 2 ≤ planeR n)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ z w : ℂ, dist z w ≤ planeDelta n → |f z - f w| ≤ η) :
    |planeQuad n f - ∫ z, f z| ≤ η * (volume (closedBall (0 : ℂ) (S + 1))).toReal := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hsi := integrable_planeStep n f
  have hint : planeQuad n f - ∫ z, f z = ∫ z, (planeStep n f z - f z) := by
    rw [integral_sub hsi hfi, integral_planeStep]
  have hzero : ∀ z, z ∉ closedBall (0 : ℂ) (S + 1) → planeStep n f z - f z = 0 := by
    intro z hz
    rw [mem_closedBall_zero_iff, not_le] at hz
    by_cases hbox : z.re ∈ Ico (-planeR n) (planeR n) ∧ z.im ∈ Ico (-planeR n) (planeR n)
    · obtain ⟨k, l, hk, hl, hzc⟩ := exists_mem_planeCell n hbox.1 hbox.2
      rw [planeStep_of_mem n f hk hl hzc]
      have hd : dist (planeCenter n k l) z ≤ planeDelta n := dist_planeCenter_le hzc
      rw [dist_comm] at hd
      have hcS : S < ‖planeCenter n k l‖ := by
        have h1 : ‖z‖ - ‖planeCenter n k l‖ ≤ dist z (planeCenter n k l) := by
          rw [dist_eq_norm]; exact norm_sub_norm_le z _
        linarith
      rw [hS z (by linarith), hS _ hcS]
      ring
    · rw [planeStep_eq_zero_of_not_box n f hbox, hS z (by linarith [planeR_le_norm_of_not_box n hbox])]
      ring
  have hbound : ∀ z, |planeStep n f z - f z| ≤ η := by
    intro z
    by_cases hbox : z.re ∈ Ico (-planeR n) (planeR n) ∧ z.im ∈ Ico (-planeR n) (planeR n)
    · obtain ⟨k, l, hk, hl, hzc⟩ := exists_mem_planeCell n hbox.1 hbox.2
      rw [planeStep_of_mem n f hk hl hzc]
      exact hη _ _ (dist_planeCenter_le hzc)
    · rw [planeStep_eq_zero_of_not_box n f hbox,
        hS z (by linarith [planeR_le_norm_of_not_box n hbox])]
      simpa using hη0
  rw [hint]
  have hset : ∫ z, (planeStep n f z - f z) = ∫ z in closedBall (0 : ℂ) (S + 1), (planeStep n f z - f z) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hzero z hz).symm
  rw [hset]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := closedBall (0 : ℂ) (S + 1))
    (f := fun z => planeStep n f z - f z) (C := η) measure_closedBall_lt_top
    (fun z _ => by rw [Real.norm_eq_abs]; exact hbound z)
  rw [Real.norm_eq_abs] at this
  simpa [Measure.real] using this

/-- **Plane Riemann sums converge.** For continuous compactly supported `f`, the midpoint sums `planeQuad n f` converge to
`∫ f` (chat 231, §1.1). -/
theorem planeQuad_tendsto_integral {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n => planeQuad n f) atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨S, hS0⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hS : ∀ z : ℂ, S < ‖z‖ → f z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzt
    have := hS0 hzt
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hK : 0 ≤ (volume (closedBall (0 : ℂ) (S + 1))).toReal := ENNReal.toReal_nonneg
  have hunif := hfc.uniformContinuous_of_continuous hf
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := (volume (closedBall (0 : ℂ) (S + 1))).toReal with hKdef
  have hKp : 0 < K + 1 := by linarith
  have hη : 0 < ε / (K + 1) := div_pos hε hKp
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1 hunif (ε / (K + 1)) hη
  have hΔt : Tendsto planeDelta atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_abs_lt_one (r := (1 / 2 : ℝ))
      (by norm_num [abs_of_pos])
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun n => ?_
    rw [planeDelta_eq]
    ring
  have hev1 : ∀ᶠ n in atTop, planeDelta n < min δ 1 :=
    hΔt.eventually (gt_mem_nhds (lt_min hδ one_pos))
  have hev2 : ∀ᶠ n : ℕ in atTop, S + 2 ≤ planeR n := by
    rw [eventually_atTop]
    refine ⟨⌈S + 1⌉₊, fun n hn => ?_⟩
    unfold planeR
    have h1 := Nat.le_ceil (S + 1)
    have h2 : (⌈S + 1⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  filter_upwards [hev1, hev2] with n h1 h2
  have hΔ : planeDelta n ≤ 1 := (h1.trans_le (min_le_right _ _)).le
  have hΔδ : planeDelta n < δ := h1.trans_le (min_le_left _ _)
  have hb := abs_planeQuad_sub_integral_le hf hfc hS hΔ h2 hη.le
    (fun z w hzw => (hδf (lt_of_le_of_lt hzw hΔδ)).le)
  rw [Real.dist_eq]
  have hηK : ε / (K + 1) * (K + 1) = ε := div_mul_cancel₀ ε hKp.ne'
  have hlt : ε / (K + 1) * K < ε := by
    have := mul_lt_mul_of_pos_left (show K < K + 1 by linarith) hη
    linarith
  exact lt_of_le_of_lt hb hlt

/-! ### The circle midpoint sums -/

/-- **Error of the circle midpoint sum.** For continuous `g` on `ℝ`, if the modulus of `g` on `[0, 2π]` at distance
`2π/N_n` is at most `η`, then `|(2π)⁻¹ ∫_0^{2π} g - angleQuad n g| ≤ η`. -/
lemma abs_circle_integral_sub_angleQuad_le {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) {η : ℝ}
    (hη : ∀ x y : ℝ, x ∈ Icc 0 (2 * π) → y ∈ Icc 0 (2 * π) → |x - y| ≤ 2 * π / planeN n → |g x - g y| ≤ η) :
    |(2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, g θ) - angleQuad n g| ≤ η := by
  have hNpos := planeN_pos n
  set N : ℕ := planeN n with hNdef
  set Δt : ℝ := 2 * π / (N : ℝ) with hΔt
  have hΔpos : 0 < Δt := by rw [hΔt]; positivity
  have hNΔ : (N : ℝ) * Δt = 2 * π := by rw [hΔt]; field_simp
  -- the cell endpoints `t_j = 2π j / N`
  set t : ℕ → ℝ := fun j => 2 * π * (j : ℝ) / (N : ℝ) with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have htN : t N = 2 * π := by
    rw [htdef]; simp only; field_simp
  have htsucc : ∀ j : ℕ, t (j + 1) = t j + Δt := by
    intro j
    rw [htdef]; simp only [hΔt]
    push_cast
    ring
  have htmono : ∀ j : ℕ, j ≤ N → t j ∈ Icc 0 (2 * π) := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [htdef]; positivity
    · rw [← htN]
      rw [htdef]
      have : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
      have hπ := Real.pi_pos
      apply div_le_div_of_nonneg_right _ hNpos.le
      nlinarith
  -- the sum over cells
  have hsum : ∫ θ in (0 : ℝ)..2 * π, g θ = ∑ j ∈ Finset.range N, ∫ θ in t j..t (j + 1), g θ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := t) (n := N)
      (fun k _ => hg.intervalIntegrable _ _), ht0, htN]
  -- each cell is within `η Δt` of its midpoint value times `Δt`
  have hcell : ∀ j ∈ Finset.range N,
      |(∫ θ in t j..t (j + 1), g θ) - Δt * g (2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ))| ≤ η * Δt := by
    intro j hj
    have hj' : j < N := Finset.mem_range.1 hj
    set m : ℝ := 2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ) with hm
    have hmt : m = t j + Δt / 2 := by
      rw [hm, htdef, hΔt]; field_simp
    have hdiff : (∫ θ in t j..t (j + 1), g θ) - Δt * g m
        = ∫ θ in t j..t (j + 1), (g θ - g m) := by
      rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, htsucc, smul_eq_mul]
      ring
    rw [hdiff]
    have hle : t j ≤ t (j + 1) := by rw [htsucc]; linarith
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := t j) (b := t (j + 1))
      (C := η) (f := fun θ => g θ - g m) (by
        intro x hx
        rw [Set.uIoc_of_le hle] at hx
        have hxI : x ∈ Icc 0 (2 * π) := by
          constructor
          · exact le_trans (htmono j (Nat.le_of_lt hj')).1 hx.1.le
          · exact le_trans hx.2 (htmono (j + 1) hj').2
        have hmI : m ∈ Icc 0 (2 * π) := by
          rw [hmt]
          exact ⟨by linarith [(htmono j (Nat.le_of_lt hj')).1], by
            linarith [(htmono (j + 1) hj').2, htsucc j, hx.2, hx.1]⟩
        rw [Real.norm_eq_abs]
        exact hη x m hxI hmI (by
          rw [hmt]
          have h1 := hx.1
          have h2 := hx.2
          rw [htsucc] at h2
          have hΔ2 : |x - (t j + Δt / 2)| ≤ Δt / 2 := by
            rw [abs_le]; constructor <;> linarith
          rw [hΔt] at hΔ2 ⊢
          linarith [hΔ2, hΔpos]))
    rw [Real.norm_eq_abs] at hbound
    have hlen : |t (j + 1) - t j| = Δt := by
      rw [htsucc, show t j + Δt - t j = Δt by ring]
      exact abs_of_pos hΔpos
    rw [hlen] at hbound
    exact hbound
  -- the Riemann sum identity `angleQuad n g = (2π)⁻¹ ∑_j Δt g(m_j)`
  have hA : angleQuad n g = (2 * π)⁻¹ * ∑ j ∈ Finset.range N,
      Δt * g (2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ)) := by
    unfold angleQuad
    rw [← hNdef]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hπ : π ≠ 0 := Real.pi_ne_zero
    rw [hΔt]
    field_simp
  have hB : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, g θ) - angleQuad n g
      = (2 * π)⁻¹ * ∑ j ∈ Finset.range N,
        ((∫ θ in t j..t (j + 1), g θ) - Δt * g (2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ))) := by
    rw [hA, hsum, Finset.sum_sub_distrib, mul_sub]
  rw [hB, abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * π))]
  have hsumle : |∑ j ∈ Finset.range N,
      ((∫ θ in t j..t (j + 1), g θ) - Δt * g (2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ)))|
      ≤ ∑ j ∈ Finset.range N, η * Δt :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => hcell j hj)
  have hconst : ∑ j ∈ Finset.range N, η * Δt = η * (2 * π) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hNΔ]
    ring
  have hpos : (0 : ℝ) < 2 * π := by positivity
  calc (2 * π)⁻¹ * |∑ j ∈ Finset.range N,
          ((∫ θ in t j..t (j + 1), g θ) - Δt * g (2 * π * ((j : ℝ) + 1 / 2) / (N : ℝ)))|
      ≤ (2 * π)⁻¹ * (η * (2 * π)) :=
        mul_le_mul_of_nonneg_left (hsumle.trans hconst.le) (inv_nonneg.2 hpos.le)
    _ = η := by field_simp

/-- **Circle midpoint sums converge.** For `f` continuous on `ℂ`, the midpoint sums `angleQuad n` of `θ ↦ f(z + r e^{iθ})`
converge to the circle average `Real.circleAverage f z r` (chat 231, §1.1). -/
theorem angleQuad_tendsto_circleAverage {f : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hf : Continuous fun θ : ℝ => f (circleMap z r θ)) :
    Tendsto (fun n => angleQuad n (fun θ => f (circleMap z r θ))) atTop
      (𝓝 (Real.circleAverage f z r)) := by
  have hcav : Real.circleAverage f z r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f (circleMap z r θ) := by
    rw [Real.circleAverage_def, smul_eq_mul]
  rw [hcav, Metric.tendsto_nhds]
  intro ε hε
  have hunif := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 hunif (ε / 2) (half_pos hε)
  have hNt : Tendsto (fun n : ℕ => (planeN n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    unfold planeN
    have h1 : n < 2 ^ (n + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact_mod_cast h1.le
  have hΔt : Tendsto (fun n : ℕ => 2 * π / (planeN n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hNt
  filter_upwards [hΔt.eventually (gt_mem_nhds hδ)] with n hn
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_circle_integral_sub_angleQuad_le (g := fun θ => f (circleMap z r θ)) hf n
    (fun x y hx hy hxy => (hδf x hx y hy (lt_of_le_of_lt hxy hn)).le)).trans_lt (half_lt_self hε)

/-! ### Measurability in the countable coordinates -/

/-- **Grid sums are Borel in the coordinates** (chat 231, §1.1). For deterministic weights `a` and points `p` of an
index type `ι`, the map `q ↦ planeQuad n (x ↦ a x * q (p x))` is a finite sum of constants times coordinates of `q`,
hence measurable for the product σ-algebra on `ι → ℝ`. -/
theorem measurable_planeQuad_eval {ι : Type*} (n : ℕ) (p : ℂ → ι) (a : ℂ → ℝ) :
    Measurable fun q : ι → ℝ => planeQuad n (fun x => a x * q (p x)) := by
  unfold planeQuad
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.const_mul (Measurable.const_mul (measurable_pi_apply _) _) _

/-- **Sphere sums are Borel in the coordinates.** The circle analogue of `measurable_planeQuad_eval`: `q ↦
angleQuad n (θ ↦ a θ * q (p θ))` is measurable on `ι → ℝ`. -/
theorem measurable_angleQuad_eval {ι : Type*} (n : ℕ) (p : ℝ → ι) (a : ℝ → ℝ) :
    Measurable fun q : ι → ℝ => angleQuad n (fun θ => a θ * q (p θ)) := by
  unfold angleQuad
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply (p _)).const_mul _

end

end MatedCRT

#print axioms MatedCRT.planeQuad_tendsto_integral
#print axioms MatedCRT.angleQuad_tendsto_circleAverage
#print axioms MatedCRT.measurable_planeQuad_eval
#print axioms MatedCRT.measurable_angleQuad_eval
