import MatedCRT.Defs.QuantumCone
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import MarkovProcess.Examples.BrownianMotion

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

/-! ### Radial and sphere-average codes (chat 231, §2) -/

/-- The countable coordinates of a circle-average process: `(r, z) ↦ h_r(z)` on `(0,∞) × ℂ`. -/
abbrev ConeCircleCode := Set.Ioi (0 : ℝ) × ℂ → ℝ

/-- The cutoff scale `δ_m = (1/2)^(m+2)` (chat 231, §2). -/
def radialEps (m : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (m + 2)

lemma radialEps_pos (m : ℕ) : 0 < radialEps m := pow_pos (by norm_num) _

lemma radialEps_tendsto : Tendsto radialEps atTop (𝓝 0) := by
  have h : radialEps = fun m : ℕ => ((2 : ℝ)⁻¹) ^ 2 * ((2 : ℝ)⁻¹) ^ m := by
    funext m
    unfold radialEps
    rw [pow_add]
    ring
  rw [h]
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul
    (((2 : ℝ)⁻¹) ^ 2)
  simpa using this

/-- The continuous radial cutoff `χ_m(r) = max(0, min(1, r/δ_m - 1))`: it vanishes for `r ≤ δ_m` and equals `1` for
`r ≥ 2 δ_m` (chat 231, §2). -/
def radialCutoff (m : ℕ) (r : ℝ) : ℝ := max 0 (min 1 (r / radialEps m - 1))

lemma radialCutoff_mem_Icc (m : ℕ) (r : ℝ) : 0 ≤ radialCutoff m r ∧ radialCutoff m r ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma radialCutoff_eq_zero_of_le {m : ℕ} {r : ℝ} (h : r ≤ radialEps m) : radialCutoff m r = 0 := by
  have hδ := radialEps_pos m
  have : r / radialEps m - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hδ]
    exact h
  unfold radialCutoff
  rw [min_eq_right (by linarith : r / radialEps m - 1 ≤ 1), max_eq_left this]

lemma radialCutoff_eq_one_of_le {m : ℕ} {r : ℝ} (h : 2 * radialEps m ≤ r) : radialCutoff m r = 1 := by
  have hδ := radialEps_pos m
  have : 1 ≤ r / radialEps m - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδ]
    linarith
  unfold radialCutoff
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma continuous_radialCutoff (m : ℕ) : Continuous (radialCutoff m) := by
  unfold radialCutoff
  have hδ := radialEps_pos m
  fun_prop

/-- The cutoff is eventually `1` at each fixed positive radius, since `δ_m → 0`. -/
lemma radialCutoff_eventually_eq_one {r : ℝ} (hr : 0 < r) : ∀ᶠ m in atTop, radialCutoff m r = 1 := by
  filter_upwards [radialEps_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < r / 2 from half_pos hr))] with m hm
  apply radialCutoff_eq_one_of_le
  linarith

/-- The safe positive radius `max(|x|, δ_m)` (chat 231, §2). -/
def safeRadius (m : ℕ) (x : ℂ) : Set.Ioi (0 : ℝ) :=
  ⟨max ‖x‖ (radialEps m), lt_of_lt_of_le (radialEps_pos m) (le_max_right _ _)⟩

/-- **Radial pairing code** (chat 231, §2.1). The pairing `∫ φ(x) h_{|x|}(0) dx` is recovered from countably many circle
coordinates, at the safe radii `max(|x|, δ_m) > 0`, by midpoint sums in `n` and a `limsup` in `m`. It never queries the
origin `q(0, 0)`. -/
def radialPairingCode (φ : ℂ → ℝ) (q : ConeCircleCode) : ℝ :=
  limsup (fun m : ℕ => limsup (fun n : ℕ =>
    planeQuad n fun x => φ x * radialCutoff m ‖x‖ * q (safeRadius m x, 0)) atTop) atTop

/-- **Radial sphere-average code** (chat 231, §2.2). The circle average of `x ↦ h_{|x|}(0)` over `∂B_r(z)`, recovered from
countably many circle coordinates at the safe radii `max(|x|, δ_m) > 0`. -/
def radialSphereCode (r : ℝ) (z : ℂ) (q : ConeCircleCode) : ℝ :=
  limsup (fun m : ℕ => limsup (fun n : ℕ =>
    angleQuad n fun θ => radialCutoff m ‖circleMap z r θ‖ * q (safeRadius m (circleMap z r θ), 0)) atTop) atTop

/-- The radial pairing code is Borel in the countable circle coordinates (chat 231, §2.1). -/
theorem measurable_radialPairingCode (φ : ℂ → ℝ) : Measurable (radialPairingCode φ) := by
  unfold radialPairingCode
  refine Measurable.limsup fun m => Measurable.limsup fun n => ?_
  exact measurable_planeQuad_eval n (fun x => (safeRadius m x, (0 : ℂ))) (fun x => φ x * radialCutoff m ‖x‖)

/-- The radial sphere-average code is Borel in the countable circle coordinates (chat 231, §2.2). -/
theorem measurable_radialSphereCode (r : ℝ) (z : ℂ) : Measurable (radialSphereCode r z) := by
  unfold radialSphereCode
  refine Measurable.limsup fun m => Measurable.limsup fun n => ?_
  exact measurable_angleQuad_eval n (fun θ => (safeRadius m (circleMap z r θ), (0 : ℂ)))
    (fun θ => radialCutoff m ‖circleMap z r θ‖)


open ProbabilityTheory HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

/-! ### Correctness of the radial codes (chat 231, §3) -/

/-- The rescaled circle-average process `c` has the radial law of the `γ`-quantum cone: its radial process
`t ↦ c_{e^{-t}}(0)`, `s ↦ c_{e^s}(0)` has the law `quantumConeRadialLaw γ ν` for a conditioned Brownian motion `ν`
(Definition 2.1; chat 231, §3). -/
def HasConeRadialLaw (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (HarmonicBalls.lqgQ γ - γ) ν ∧
    P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν

/-- The radial process is measurable when the circle averages are measurable at each positive radius. -/
lemma measurable_radialProcess_circle {Ω : Type*} [MeasurableSpace Ω] {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) :
    Measurable fun ω => radialProcess (c ω) :=
  Measurable.prodMk (Measurable.of_eval fun t => hcm (Real.exp (-(t : ℝ))) 0 (Real.exp_pos _))
    (Measurable.of_eval fun s => hcm (Real.exp s) 0 (Real.exp_pos _))

/-- **One-time marginal of the radial process.** For `t ≥ 0`, `∫ |c_{e^{-t}}(0)| dP` is the integral of `|B_t + γ t|`
under the standard Brownian motion, because the radial law is `quantumConeRadialLaw`. -/
lemma lintegral_ofReal_radial_eq {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsProbabilityMeasure ν) (hrad : P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal |c ω (Real.exp (-(t : ℝ))) 0| ∂P
      = ∫⁻ w, ENNReal.ofReal |w t + γ * t| ∂(brownianMotion 0) := by
  have hR := measurable_radialProcess_circle hcm
  have hf : Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => ENNReal.ofReal |p.1 t| :=
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply t).comp measurable_fst).abs
  have hS : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * s :=
    Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).add_const _)
  have hT : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * s :=
    Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).sub_const _)
  have hg : Measurable fun q : (ℝ≥0 → ℝ) => ENNReal.ofReal |q t| :=
    ENNReal.measurable_ofReal.comp (measurable_pi_apply t).abs
  calc ∫⁻ ω, ENNReal.ofReal |c ω (Real.exp (-(t : ℝ))) 0| ∂P
      = ∫⁻ ω, (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => ENNReal.ofReal |p.1 t|) (radialProcess (c ω)) ∂P := rfl
    _ = ∫⁻ p, ENNReal.ofReal |p.1 t| ∂(P.map fun ω => radialProcess (c ω)) :=
        (lintegral_map hf hR).symm
    _ = ∫⁻ p, ENNReal.ofReal |p.1 t| ∂(quantumConeRadialLaw γ ν) := by rw [hrad]
    _ = ∫⁻ w, ENNReal.ofReal |w t + γ * t| ∂(brownianMotion 0) := by
        unfold quantumConeRadialLaw
        have : IsProbabilityMeasure (ν.map fun w (s : ℝ≥0) => w s - γ * s) :=
          (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hν
        calc ∫⁻ p, ENNReal.ofReal |p.1 t| ∂(((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s).prod
                (ν.map fun w (s : ℝ≥0) => w s - γ * s))
            = ∫⁻ a, ENNReal.ofReal |a t| ∂((((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s).prod
                (ν.map fun w (s : ℝ≥0) => w s - γ * s)).map Prod.fst) :=
              (lintegral_map hg measurable_fst).symm
          _ = ∫⁻ a, ENNReal.ofReal |a t| ∂(((ν.map fun w (s : ℝ≥0) => w s - γ * s) Set.univ) •
                ((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s)) := by
              rw [Measure.map_fst_prod]
          _ = ∫⁻ a, ENNReal.ofReal |a t| ∂((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s) := by
              rw [measure_univ, one_smul]
          _ = ∫⁻ w, ENNReal.ofReal |w t + γ * t| ∂(brownianMotion 0) :=
              lintegral_map hg hS

/-- **Second moment of the Brownian marginal.** Under `brownianMotion 0` the coordinate `B_t` is `N(0, t)`
(`IsBrownianReal.hasLaw_eval`), so `∫ B_t² = t`. -/
lemma lintegral_ofReal_sq_brownian (t : ℝ≥0) :
    ∫⁻ w, ENNReal.ofReal ((w t) ^ 2) ∂(brownianMotion 0) = ENNReal.ofReal t := by
  have hL := (isBrownianReal_brownianMotion 0).hasLaw_eval t
  have hm : Measurable fun w : ContinuousPath ℝ => w t - 0 := (ContinuousMap.measurable_eval t).sub_const _
  have hmap : (brownianMotion 0).map (fun w : ContinuousPath ℝ => w t - 0) = gaussianReal 0 t := hL.map_eq
  calc ∫⁻ w, ENNReal.ofReal ((w t) ^ 2) ∂(brownianMotion 0)
      = ∫⁻ w, ENNReal.ofReal ((w t - 0) ^ 2) ∂(brownianMotion 0) := by simp only [sub_zero]
    _ = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 t) := by
        rw [← hmap, lintegral_map (by fun_prop) hm]
    _ = ENNReal.ofReal (∫ x, x ^ 2 ∂(gaussianReal 0 t)) :=
        (ofReal_integral_eq_lintegral_ofReal (memLp_id_gaussianReal 2 |>.integrable_sq)
          (Eventually.of_forall fun x => sq_nonneg x)).symm
    _ = ENNReal.ofReal t := by
        congr 1
        have hv := variance_id_gaussianReal (μ := 0) (v := t)
        have hmean : ∫ x, id x ∂(gaussianReal 0 t) = 0 := integral_id_gaussianReal (μ := 0) (v := t)
        have h2 := ProbabilityTheory.variance_eq_sub (memLp_id_gaussianReal 2 (μ := 0) (v := t))
        rw [hv, hmean] at h2
        simpa using h2.symm

/-- **The one-time bound** `E|B_t + γ t| ≤ 1 + t + |γ| t` (chat 231, §3.1; `|x| ≤ 1 + x²` replaces Cauchy-Schwarz). -/
lemma lintegral_ofReal_abs_add_le (γ : ℝ) (t : ℝ≥0) :
    ∫⁻ w, ENNReal.ofReal |w t + γ * t| ∂(brownianMotion 0) ≤ ENNReal.ofReal (1 + t + |γ| * t) := by
  have hpt : ∀ w : ContinuousPath ℝ, ENNReal.ofReal |w t + γ * t|
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal ((w t) ^ 2) + ENNReal.ofReal (|γ| * t) := by
    intro w
    rw [← ENNReal.ofReal_add (by norm_num) (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |w t + γ * t| ≤ |w t| + |γ * t| := abs_add_le _ _
    have h2 : |w t| ≤ 1 + (w t) ^ 2 := by nlinarith [sq_abs (w t), sq_nonneg (|w t| - 1)]
    have h3 : |γ * (t : ℝ)| = |γ| * t := by rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg t)]
    rw [h3] at h1
    linarith
  have hmeas : Measurable fun w : ContinuousPath ℝ => ENNReal.ofReal ((w t) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((ContinuousMap.measurable_eval t).pow_const 2)
  calc ∫⁻ w, ENNReal.ofReal |w t + γ * t| ∂(brownianMotion 0)
      ≤ ∫⁻ w, (ENNReal.ofReal 1 + ENNReal.ofReal ((w t) ^ 2) + ENNReal.ofReal (|γ| * t)) ∂(brownianMotion 0) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal 1 + ENNReal.ofReal t + ENNReal.ofReal (|γ| * t) := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
          lintegral_ofReal_sq_brownian]
        simp only [lintegral_const, measure_univ, mul_one]
    _ = ENNReal.ofReal (1 + t + |γ| * t) := by
        rw [← ENNReal.ofReal_add (by norm_num) (NNReal.coe_nonneg t),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **A measurable full-measure set of good samples.** Off a null set `c` is continuous on `(0,∞) × ℂ`; the good set `T`
is measurable, has null complement, and `c` is continuous on `(0,∞) × ℂ` for every `ω ∈ T`. -/
lemma exists_measurable_good_set {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    ∃ T : Set Ω, MeasurableSet T ∧ P Tᶜ = 0 ∧
      ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  obtain ⟨t, hBt, hmt, hPt⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  refine ⟨tᶜ, hmt.compl, by rw [compl_compl]; exact hPt, fun ω hω => ?_⟩
  by_contra h
  exact hω (hBt h)

/-- **Joint measurability of the modified radial process.** For the good set `T`, the map `(t, ω) ↦
1_T(ω) c_{e^{-t}}(0)(ω)` is measurable on `ℝ × Ω`: it is continuous in `t` for every `ω` and measurable in `ω` for every
`t` (Carathéodory, `measurable_uncurry_of_continuous_of_measurable`). -/
lemma measurable_uncurry_radial {Ω : Type*} [MeasurableSpace Ω] {c : Ω → ℝ → ℂ → ℝ} {T : Set Ω}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) (hT : MeasurableSet T)
    (hgood : ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω) := by
  refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun t => ?_)
  · by_cases hω : ω ∈ T
    · simp only [Set.indicator_of_mem hω]
      have hc := hgood ω hω
      exact hc.comp_continuous (f := fun t : ℝ => ((Real.exp (-t)), (0 : ℂ)))
        (by fun_prop) (fun t => ⟨Real.exp_pos _, Set.mem_univ _⟩)
    · simp only [Set.indicator_of_notMem hω]
      exact continuous_const
  · exact (hcm (Real.exp (-t)) 0 (Real.exp_pos _)).indicator hT

/-- **Change of variables `y = e^{-t}` on `(0,1]`** (chat 231, §3.1; `lintegral_image_eq_lintegral_abs_deriv_mul`). -/
lemma lintegral_Ioc_eq_radial (g : ℝ → ℝ) :
    ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) =
      ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |g (Real.exp (-t))| := by
  have himg : (fun t : ℝ => Real.exp (-t)) '' Set.Ici 0 = Set.Ioc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by simp only [Set.mem_Ici] at ht; linarith)⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨-Real.log y, ?_, ?_⟩
      · simp only [Set.mem_Ici, neg_nonneg]
        exact Real.log_nonpos hy0.le hy1
      · simp only [neg_neg]
        exact Real.exp_log hy0
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) (Set.Ici 0) x := by
    intro x _
    have := ((hasDerivAt_id x).neg.exp).hasDerivWithinAt (s := Set.Ici 0)
    simpa using this
  have hinj : Set.InjOn (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ici hderiv hinj
    (fun y => ENNReal.ofReal (y * |g y|))
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ici fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    abs_neg, abs_of_pos (Real.exp_pos _)]
  congr 1
  rw [show -2 * t = -t + -t by ring, Real.exp_add]
  ring

/-- **One-time bound for the good modification.** For `t ≥ 0`, the `P`-integral of `|1_T c_{e^{-t}}(0)|` is at most
`1 + t + |γ| t` (`lintegral_ofReal_radial_eq` and `lintegral_ofReal_abs_add_le`). -/
lemma lintegral_radial_le {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsProbabilityMeasure ν) (hrad : P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν)
    {T : Set Ω} (hPT : P Tᶜ = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal |T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω| ∂P
      ≤ ENNReal.ofReal (1 + t + |γ| * t) := by
  have hae : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    exact hPT
  have h1 : ∫⁻ ω, ENNReal.ofReal |T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω| ∂P
      = ∫⁻ ω, ENNReal.ofReal |c ω (Real.exp (-t)) 0| ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [Set.indicator_of_mem hω]
  have hs : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  have h2 := lintegral_ofReal_radial_eq hcm hν hrad t.toNNReal
  rw [hs] at h2
  rw [h1, h2]
  have h3 := lintegral_ofReal_abs_add_le γ t.toNNReal
  rw [hs] at h3
  exact h3

/-- **Almost sure finiteness of the radial integral** (Tonelli; chat 231, §3.1): almost surely
`∫_{t ≥ 0} e^{-2t} |1_T c_{e^{-t}}(0)| dt < ∞`. -/
lemma ae_lintegral_radial_lt_top {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsProbabilityMeasure ν) (hrad : P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν)
    [IsFiniteMeasure P] {T : Set Ω} (hT : MeasurableSet T) (hPT : P Tᶜ = 0)
    (hgood : ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    ∀ᵐ ω ∂P, ∫⁻ t in Set.Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω| < ⊤ := by
  set u : ℝ → Ω → ℝ := fun t ω => T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω with hu_def
  have hmeas : Measurable (Function.uncurry u) := measurable_uncurry_radial hcm hT hgood
  have hu : Measurable fun p : Ω × ℝ => u p.2 p.1 := by
    have hpair : Measurable fun p : Ω × ℝ => ((p.2, p.1) : ℝ × Ω) := measurable_snd.prodMk measurable_fst
    exact hmeas.comp hpair
  have hF : Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-2 * p.2)) * ENNReal.ofReal |u p.2 p.1| := by
    have h1 : Measurable fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (-2 * p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
    have h2 : Measurable fun p : Ω × ℝ => ENNReal.ofReal |u p.2 p.1| :=
      ENNReal.measurable_ofReal.comp hu.abs
    exact h1.mul h2
  -- Tonelli: integrate in `ω` first
  have hswap : ∫⁻ ω, (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |u t ω|) ∂P
      = ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |u t ω| ∂P :=
    lintegral_lintegral_swap hF.aemeasurable
  have hbound : ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |u t ω| ∂P
      ≤ ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal ((1 + |γ|) * Real.exp (-t)) := by
    refine setLIntegral_mono' measurableSet_Ici fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := Set.mem_Ici.1 ht
    have hpair : Measurable fun ω : Ω => ((t, ω) : ℝ × Ω) := measurable_const.prodMk measurable_id
    have hm : Measurable fun ω => ENNReal.ofReal |u t ω| :=
      ENNReal.measurable_ofReal.comp (hmeas.comp hpair).abs
    rw [lintegral_const_mul _ hm]
    have hle := lintegral_radial_le hcm hν hrad hPT ht0
    have hpt : ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal (1 + t + |γ| * t)
        ≤ ENNReal.ofReal ((1 + |γ|) * Real.exp (-t)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have he2 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      have hE : Real.exp (-2 * t) * Real.exp t = Real.exp (-t) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpos := (Real.exp_pos (-2 * t)).le
      have hA : Real.exp (-2 * t) * (1 + t) ≤ Real.exp (-t) := by
        rw [← hE]; exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) hpos
      have hC : Real.exp (-2 * t) * t ≤ Real.exp (-t) := by
        rw [← hE]; exact mul_le_mul_of_nonneg_left he2 hpos
      calc Real.exp (-2 * t) * (1 + t + |γ| * t)
          = Real.exp (-2 * t) * (1 + t) + |γ| * (Real.exp (-2 * t) * t) := by ring
        _ ≤ Real.exp (-t) + |γ| * Real.exp (-t) :=
            add_le_add hA (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
        _ = (1 + |γ|) * Real.exp (-t) := by ring
    calc ENNReal.ofReal (Real.exp (-2 * t)) * ∫⁻ ω, ENNReal.ofReal |u t ω| ∂P
        ≤ ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal (1 + t + |γ| * t) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ ENNReal.ofReal ((1 + |γ|) * Real.exp (-t)) := hpt
  have hfin : ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal ((1 + |γ|) * Real.exp (-t)) < ⊤ := by
    have hint : IntegrableOn (fun t : ℝ => (1 + |γ|) * Real.exp (-t)) (Set.Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
        simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
      exact h1.const_mul (1 + |γ|)
    exact hint.lintegral_lt_top
  have hmeasω : Measurable fun ω => ∫⁻ t in Set.Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |u t ω| :=
    hF.lintegral_prod_right'
  have hI : ∫⁻ ω, (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |u t ω|) ∂P < ⊤ := by
    rw [hswap]
    exact lt_of_le_of_lt hbound hfin
  exact ae_lt_top hmeasω hI.ne

/-! ### Dominated convergence for the radial pairing code -/

/-- A continuous `g` on `(0,∞)` with `∫_{(0,1]} y |g y| dy < ∞` has `∫_{(0,R0]} y |g y| dy < ∞` for `R0 ≥ 1`. -/
lemma integrableOn_Ioc_mul_abs {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0)) {R0 : ℝ} (hR0 : 1 ≤ R0)
    (hfin : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) < ⊤) :
    IntegrableOn (fun y => y * |g y|) (Set.Ioc 0 R0) := by
  have hc : ContinuousOn (fun y => y * |g y|) (Set.Ioi 0) := continuousOn_id.mul hg.abs
  rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hR0]
  refine IntegrableOn.union ?_ ?_
  · refine ⟨(hc.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc, ?_⟩
    have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ‖y * |g y|‖ₑ = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) :=
      setLIntegral_congr_fun measurableSet_Ioc fun y hy => by
        rw [Real.enorm_eq_ofReal (mul_nonneg hy.1.le (abs_nonneg _))]
    exact h1.trans_lt hfin
  · have hcI : ContinuousOn (fun y => y * |g y|) (Set.Icc 1 R0) :=
      hc.mono fun y hy => Set.mem_Ioi.2 (lt_of_lt_of_le one_pos hy.1)
    exact (hcI.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- The radial integral on `ℂ`: `x ↦ 1_{|x| ≤ R0} |g(|x|)|` is integrable when `∫_{(0,R0]} y |g y| dy < ∞` (polar
coordinates, `integrable_fun_norm_addHaar`, `dim ℂ = 2`). -/
lemma integrable_radial_indicator {g : ℝ → ℝ} {R0 : ℝ}
    (hg : IntegrableOn (fun y => y * |g y|) (Set.Ioc 0 R0)) :
    Integrable (fun x : ℂ => (Set.Iic R0).indicator (fun y => |g y|) ‖x‖) := by
  have hdim : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  refine (integrable_fun_norm_addHaar (μ := volume) (f := (Set.Iic R0).indicator (fun y => |g y|))).2 ?_
  have h1 : IntegrableOn (fun y => (Set.Ioc 0 R0).indicator (fun y => y * |g y|) y) (Set.Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).2 hg).integrableOn
  refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := hy
  by_cases h : y ≤ R0
  · simp [Set.indicator, h, hy0]
  · simp [Set.indicator, h]

/-- **Pointwise domination of the radial term.** If `|φ| ≤ M`, `φ = 0` off `B(0,R0)`, the cutoff is in `[0,1]` and vanishes
at radii `≤ δ_m`, then `|φ(x) χ_m(|x|) g(max(|x|, δ_m))| ≤ M 1_{|x| ≤ R0} |g(|x|)|`. -/
lemma abs_radialTerm_le {φ : ℂ → ℝ} {M R0 : ℝ} {g : ℝ → ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |φ x| ≤ M)
    (hφ0 : ∀ x : ℂ, R0 < ‖x‖ → φ x = 0) (m : ℕ) (x : ℂ) :
    |φ x * radialCutoff m ‖x‖ * g (max ‖x‖ (radialEps m))| ≤ M * (Set.Iic R0).indicator (fun y => |g y|) ‖x‖ := by
  have hind : 0 ≤ (Set.Iic R0).indicator (fun y => |g y|) ‖x‖ := Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
  by_cases hx : R0 < ‖x‖
  · rw [hφ0 x hx]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg hM0 hind
  · rw [not_lt] at hx
    have hI : (Set.Iic R0).indicator (fun y => |g y|) ‖x‖ = |g ‖x‖| := Set.indicator_of_mem (Set.mem_Iic.2 hx) _
    rw [hI]
    by_cases hδ : radialEps m ≤ ‖x‖
    · rw [max_eq_left hδ, abs_mul, abs_mul]
      have hc := radialCutoff_mem_Icc m ‖x‖
      have hcabs : |radialCutoff m ‖x‖| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
      calc |φ x| * |radialCutoff m ‖x‖| * |g ‖x‖| ≤ M * 1 * |g ‖x‖| := by
            gcongr
            · exact hM x
        _ = M * |g ‖x‖| := by ring
    · rw [not_le] at hδ
      rw [radialCutoff_eq_zero_of_le hδ.le]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg hM0 (abs_nonneg _)

/-- The finite-measure property of `P`, from the radial law (the image of a probability measure). -/
lemma isFiniteMeasure_of_radial_law {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c : Ω → ℝ → ℂ → ℝ} (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsProbabilityMeasure ν) (hrad : P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) :
    IsFiniteMeasure P := by
  have hQ : IsProbabilityMeasure (quantumConeRadialLaw γ ν) := by
    unfold quantumConeRadialLaw
    have hS : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * s :=
      Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).add_const _)
    have hT : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * s :=
      Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).sub_const _)
    have : IsProbabilityMeasure ((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s) :=
      (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
    have : IsProbabilityMeasure (ν.map fun w (s : ℝ≥0) => w s - γ * s) :=
      (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hν
    infer_instance
  have h : P.map (fun ω => radialProcess (c ω)) Set.univ = 1 := by
    rw [hrad]
    exact measure_univ
  rw [Measure.map_apply (measurable_radialProcess_circle hcm) MeasurableSet.univ, Set.preimage_univ] at h
  exact ⟨by rw [h]; exact ENNReal.one_lt_top⟩

/-- **Radial pairing code is correct almost surely** (chat 231, §3.2). For the rescaled circle averages `c` with the radial
law of the quantum cone, almost surely the radial pairing code of the circle process is the pairing `∫ φ(x) h_{|x|}(0) dx`.
The inner `limsup` is the plane integral of a continuous compactly supported function (`planeQuad_tendsto_integral`); the
outer `limsup` is a dominated limit as the cutoff radius `δ_m → 0`. -/
theorem radialPairingCode_ae_eq {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hrad : HasConeRadialLaw γ P c) (φ : ℂ → ℝ) (hφ : IsTestFunction Set.univ φ) :
    (fun ω => radialPairingCode φ (circleProcess (c ω))) =ᵐ[P] (fun ω => ∫ x, φ x * c ω ‖x‖ 0) := by
  obtain ⟨ν, hν, hrad'⟩ := hrad
  obtain ⟨T, hT, hPT, hgood⟩ := exists_measurable_good_set hcont
  have : IsFiniteMeasure P := isFiniteMeasure_of_radial_law hcm hν.1 hrad'
  have hfin := ae_lintegral_radial_lt_top hcm hν.1 hrad' hT hPT hgood
  have hTc : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    exact hPT
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  obtain ⟨r0, hr0⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set R0 : ℝ := max r0 1 with hR0def
  have hR01 : 1 ≤ R0 := le_max_right _ _
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x, |φ x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]
    exact le_trans (hC x) (le_max_left _ _)
  have hφ0 : ∀ x : ℂ, R0 < ‖x‖ → φ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have h := hr0 hxt
    rw [mem_closedBall_zero_iff] at h
    linarith [le_max_left r0 1]
  filter_upwards [hfin, hTc] with ω hfinω hωT
  have hcω := hgood ω hωT
  have hgc : ContinuousOn (fun y : ℝ => c ω y 0) (Set.Ioi 0) :=
    hcω.comp (continuousOn_id.prodMk continuousOn_const) (fun y hy => ⟨hy, Set.mem_univ _⟩)
  have hfinY : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |c ω y 0|) < ⊤ := by
    have key := lintegral_Ioc_eq_radial (fun y => c ω y 0)
    rw [key]
    simpa only [Set.indicator_of_mem hωT] using hfinω
  have hgI : IntegrableOn (fun y => y * |c ω y 0|) (Set.Ioc 0 R0) :=
    integrableOn_Ioc_mul_abs hgc hR01 hfinY
  set F : ℕ → ℂ → ℝ := fun m x => φ x * radialCutoff m ‖x‖ * c ω (max ‖x‖ (radialEps m)) 0 with hFdef
  set f : ℂ → ℝ := fun x => φ x * c ω ‖x‖ 0 with hfdef
  have hcontF : ∀ m, Continuous (F m) := by
    intro m
    have hcm' : Continuous fun x : ℂ => c ω (max ‖x‖ (radialEps m)) 0 :=
      hcω.comp_continuous (f := fun x : ℂ => (max ‖x‖ (radialEps m), (0 : ℂ))) (by fun_prop)
        (fun x => ⟨lt_of_lt_of_le (radialEps_pos m) (le_max_right _ _), Set.mem_univ _⟩)
    exact (hφ.1.continuous.mul ((continuous_radialCutoff m).comp continuous_norm)).mul hcm'
  have hcsF : ∀ m, HasCompactSupport (F m) := by
    intro m
    exact (hφ.2.1.mul_right).mul_right
  have hinner : ∀ m : ℕ, limsup (fun n : ℕ => planeQuad n
      (fun x => φ x * radialCutoff m ‖x‖ * circleProcess (c ω) (safeRadius m x, 0))) atTop = ∫ x, F m x :=
    fun m => (planeQuad_tendsto_integral (hcontF m) (hcsF m)).limsup_eq
  have houter : Tendsto (fun m => ∫ x, F m x) atTop (𝓝 (∫ x, f x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => M * (Set.Iic R0).indicator (fun y => |c ω y 0|) ‖x‖)
      (fun m => (hcontF m).aestronglyMeasurable) ((integrable_radial_indicator hgI).const_mul M)
      (fun m => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact abs_radialTerm_le (g := fun y => c ω y 0) hM0 hM hφ0 m x
    · filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
      have hx0 : x ≠ 0 := hx
      have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [radialCutoff_eventually_eq_one hpos,
        radialEps_tendsto.eventually (gt_mem_nhds hpos)] with m hcut hδ
      simp only [hFdef, hfdef, hcut, max_eq_left hδ.le, mul_one]
  unfold radialPairingCode
  simp only [hinner]
  exact houter.limsup_eq

/-! ### The sphere-average code (chat 231, §3.2) -/

/-- **The circle meets the origin in at most one angle on `(0, 2π]`.** Hence the set of angles with `circleMap z r θ = 0`
is null for Lebesgue measure on `(0, 2π]` (the zero set of `circleMap` is discrete). -/
lemma ae_circleMap_ne_zero {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0 : ℝ) (2 * π))), circleMap z r θ ≠ 0 := by
  have hsub : {θ : ℝ | θ ∈ Set.Ioc (0 : ℝ) (2 * π) ∧ circleMap z r θ = 0}.Subsingleton := by
    rintro a ⟨⟨ha0, ha1⟩, ha⟩ b ⟨⟨hb0, hb1⟩, hb⟩
    have hexp : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I) := by
      have h1 : (r : ℂ) * Complex.exp (a * Complex.I) = (r : ℂ) * Complex.exp (b * Complex.I) := by
        unfold circleMap at ha hb
        linear_combination ha - hb
      exact mul_left_cancel₀ (by exact_mod_cast hr.ne') h1
    have hdiff : Complex.exp ((a - b : ℝ) * Complex.I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hdiff
    have hn' : (a - b : ℝ) = n * (2 * π) := by
      have h2 : ((a - b : ℝ) : ℂ) = ((n * (2 * π) : ℝ) : ℂ) := by
        have := hn
        push_cast at this ⊢
        apply mul_right_cancel₀ Complex.I_ne_zero
        linear_combination this
      exact_mod_cast h2
    have hn1 : (n : ℝ) < 1 := by
      have : (n : ℝ) * (2 * π) < 2 * π := by linarith
      nlinarith [Real.pi_pos]
    have hn2 : (-1 : ℝ) < n := by
      have : (-(2 * π)) < (n : ℝ) * (2 * π) := by linarith
      nlinarith [Real.pi_pos]
    have hnz : n = 0 := by
      have h1 : n < 1 := by exact_mod_cast hn1
      have h2 : -1 < n := by exact_mod_cast hn2
      omega
    rw [hnz] at hn'
    simp at hn'
    linarith
  have hcount : {θ : ℝ | θ ∈ Set.Ioc (0 : ℝ) (2 * π) ∧ circleMap z r θ = 0}.Countable := hsub.countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hnull : volume {θ : ℝ | θ ∈ Set.Ioc (0 : ℝ) (2 * π) ∧ circleMap z r θ = 0} = 0 :=
    hcount.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with θ hθ hIoc hzero
  exact hθ ⟨hIoc, hzero⟩

/-- The cutoff term is dominated by the unscaled value: `|χ_m(|x|) g(max(|x|, δ_m))| ≤ |g(|x|)|`. -/
lemma abs_radialCutoff_mul_le (m : ℕ) (x : ℂ) (g : ℝ → ℝ) :
    |radialCutoff m ‖x‖ * g (max ‖x‖ (radialEps m))| ≤ |g ‖x‖| := by
  by_cases hδ : radialEps m ≤ ‖x‖
  · rw [max_eq_left hδ, abs_mul]
    have hc := radialCutoff_mem_Icc m ‖x‖
    have hcabs : |radialCutoff m ‖x‖| ≤ 1 := by
      rw [abs_of_nonneg hc.1]
      exact hc.2
    calc |radialCutoff m ‖x‖| * |g ‖x‖| ≤ 1 * |g ‖x‖| := mul_le_mul_of_nonneg_right hcabs (abs_nonneg _)
      _ = |g ‖x‖| := one_mul _
  · rw [not_le] at hδ
    rw [radialCutoff_eq_zero_of_le hδ.le, zero_mul, abs_zero]
    exact abs_nonneg _

/-- **Sphere-average code is correct almost surely, conditional on the angular integrability** (chat 231, §3.2). The inner
`limsup` is the circle average of the continuous cutoff function (`angleQuad_tendsto_circleAverage`); the outer limit is a
dominated convergence of the circle integral, dominated by `|h_{|x|}(0)|` on the circle.

NAMED INPUT `hcircInt` (the a.s. angular integrability along `∂B_r(z)`). It is discharged, with no input, by
`MatedCRT.radialSphereCode_ae_eq` in `S2y/ConeCircInt240.lean` (chat 240 §1), which supplies `hcircInt` through
`ae_intervalIntegrable_radial_circle`. -/
theorem radialSphereCode_ae_eq_of_circInt {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (_hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (_hrad : HasConeRadialLaw γ P c)
    (hcircInt : ∀ r z, 0 < r → ∀ᵐ ω ∂P,
      IntervalIntegrable (fun θ : ℝ => |c ω ‖circleMap z r θ‖ 0|) volume 0 (2 * π))
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun ω => radialSphereCode r z (circleProcess (c ω))) =ᵐ[P]
      (fun ω => Real.circleAverage (fun x => c ω ‖x‖ 0) z r) := by
  filter_upwards [hcont, hcircInt r z hr] with ω hcω hint
  set F : ℕ → ℂ → ℝ := fun m x => radialCutoff m ‖x‖ * c ω (max ‖x‖ (radialEps m)) 0 with hFdef
  have hcontF : ∀ m, Continuous (F m) := by
    intro m
    have hc' : Continuous fun x : ℂ => c ω (max ‖x‖ (radialEps m)) 0 :=
      hcω.comp_continuous (f := fun x : ℂ => (max ‖x‖ (radialEps m), (0 : ℂ))) (by fun_prop)
        (fun x => ⟨lt_of_lt_of_le (radialEps_pos m) (le_max_right _ _), Set.mem_univ _⟩)
    exact ((continuous_radialCutoff m).comp continuous_norm).mul hc'
  have hinner : ∀ m : ℕ, limsup (fun n : ℕ => angleQuad n
      (fun θ => radialCutoff m ‖circleMap z r θ‖ * circleProcess (c ω) (safeRadius m (circleMap z r θ), 0))) atTop
      = Real.circleAverage (F m) z r := fun m =>
    (angleQuad_tendsto_circleAverage (f := F m) (z := z) (r := r)
      ((hcontF m).comp (continuous_circleMap z r))).limsup_eq
  -- a.e. non-vanishing of the circle
  have hae := (ae_restrict_iff' measurableSet_Ioc).1 (ae_circleMap_ne_zero (z := z) hr)
  have houter : Tendsto (fun m : ℕ => Real.circleAverage (F m) z r) atTop
      (𝓝 (Real.circleAverage (fun x => c ω ‖x‖ 0) z r)) := by
    simp only [Real.circleAverage_def, smul_eq_mul]
    refine Tendsto.const_mul _ ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => |c ω ‖circleMap z r θ‖ 0|) (Eventually.of_forall fun m => ?_)
      (Eventually.of_forall fun m => Eventually.of_forall fun θ => ?_) hint ?_
    · exact ((hcontF m).comp (continuous_circleMap z r)).aestronglyMeasurable
    · intro _
      rw [Real.norm_eq_abs]
      exact abs_radialCutoff_mul_le m (circleMap z r θ) (fun y => c ω y 0)
    · filter_upwards [hae] with θ hθ hIoc
      have hIoc' : θ ∈ Set.Ioc (0 : ℝ) (2 * π) := by
        rwa [Set.uIoc_of_le (by positivity)] at hIoc
      have hne : circleMap z r θ ≠ 0 := hθ hIoc'
      have hpos : 0 < ‖circleMap z r θ‖ := norm_pos_iff.2 hne
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [radialCutoff_eventually_eq_one hpos,
        radialEps_tendsto.eventually (gt_mem_nhds hpos)] with m hcut hδ
      show c ω ‖circleMap z r θ‖ 0
        = radialCutoff m ‖circleMap z r θ‖ * c ω (max ‖circleMap z r θ‖ (radialEps m)) 0
      rw [hcut, max_eq_left hδ.le, one_mul]
  simp only [radialSphereCode]
  simp only [hinner]
  exact houter.limsup_eq

end

end MatedCRT

#print axioms MatedCRT.planeQuad_tendsto_integral
#print axioms MatedCRT.angleQuad_tendsto_circleAverage
#print axioms MatedCRT.measurable_planeQuad_eval
#print axioms MatedCRT.measurable_angleQuad_eval
#print axioms MatedCRT.radialPairingCode_ae_eq
#print axioms MatedCRT.measurable_radialPairingCode
#print axioms MatedCRT.measurable_radialSphereCode
#print axioms MatedCRT.radialSphereCode_ae_eq_of_circInt
