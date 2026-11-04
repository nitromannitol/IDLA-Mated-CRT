import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationGreen

/-! Integrability for killed walk occupation sums. -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- Finite expected exit time makes the natural-valued exit time integrable. -/
theorem integrable_vExitTime_toNat (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (hmean : expectedExitTime m A a ≠ ⊤) :
    Integrable (fun x => ((vExitTime A x).toNat : ℝ)) (srwLaw m a) := by
  have hm : Measurable (fun x : ℕ → ℤ => (vExitTime A x : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_vExitTime A)
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmean
  apply hi.congr
  filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
  rw [← ENat.natCast_toNat hx]
  simp

/-- Under finite expected exit time, a bounded killed-walk occupation sum is
integrable when the killed domain lies in a finite set. -/
theorem integrable_killed_occupation (m : ℤ → ℤ → ℕ) (A : Set ℤ) (B : Finset ℤ)
    (hAB : A ⊆ B) (a : ℤ) (g : ℤ → ℝ) (hmean : expectedExitTime m A a ≠ ⊤) :
    Integrable (fun x => ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n))
      (srwLaw m a) := by
  have hi : Integrable (fun x => ∑ b ∈ B, (visitsBeforeExit A b x).toReal * g b)
      (srwLaw m a) := by
    apply integrable_finsetSum
    intro b hb
    exact (integrable_visitsBeforeExit_of_expectedExitTime_ne_top m A a b hmean).mul_const (g b)
  apply hi.congr
  filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
  exact sum_visitsBeforeExit_mul_eq_occupation A B hAB x g hx

/-- The exit-time tail is integrable whenever the expected exit time is finite. -/
theorem integrable_vExitTime_tail (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (M : ℝ) (N : ℕ) (hmean : expectedExitTime m A a ≠ ⊤) :
    Integrable (fun x => if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0)
      (srwLaw m a) := by
  have hm : Measurable (fun x : ℕ → ℤ => (vExitTime A x).toNat) :=
    (measurable_of_countable (fun n : ℕ∞ => n.toNat)).comp (measurable_vExitTime A)
  have hs : MeasurableSet {x : ℕ → ℤ | N < (vExitTime A x).toNat} :=
    measurableSet_lt measurable_const hm
  have hi := ((integrable_vExitTime_toNat m A a hmean).const_mul M).indicator hs
  apply hi.congr
  filter_upwards [] with x
  by_cases h : N < (vExitTime A x).toNat <;> simp [Set.indicator, h]

/-- The fixed-step killed occupation sum is integrable for bounded test
functions. -/
theorem integrable_truncated_killed_occupation (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (a : ℤ) (g : ℤ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ b ∈ A, |g b| ≤ M) (N : ℕ) :
    Integrable (fun x => ∑ n ∈ Finset.range N,
      if (n : ℕ∞) < vExitTime A x then g (x n) else 0) (srwLaw m a) := by
  apply integrable_finsetSum
  intro n hn
  have hs : MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x} :=
    measurableSet_natCast_lt_vExitTime A n
  have hm : Measurable (fun x : ℕ → ℤ => if (n : ℕ∞) < vExitTime A x then g (x n) else 0) :=
    Measurable.ite hs ((measurable_of_countable g).comp (measurable_pi_apply n)) measurable_const
  apply (integrable_const M).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  split_ifs with h
  · exact hg (x n) (mem_of_lt_vExitTime h)
  · simpa using hM

/-- A finite Green occupation sum differs from its fixed-step truncation by
at most the expected exit-time tail. -/
theorem abs_green_occupation_tail_le (m : ℤ → ℤ → ℕ) (A : Set ℤ) (B : Finset ℤ)
    (hAB : A ⊆ B) (a : ℤ) (g : ℤ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ b ∈ A, |g b| ≤ M) (N : ℕ) (hmean : expectedExitTime m A a ≠ ⊤) :
    |(∑ b ∈ B, greenFn m A a b * g b) -
      ∫ x, ∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0 ∂srwLaw m a| ≤
      ∫ x, if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0
        ∂srwLaw m a := by
  rw [sum_greenFn_mul_eq_integral_occupation_of_expectedExitTime_ne_top m A B hAB a g hmean]
  exact abs_integral_killed_occupation_tail_le (srwLaw m a) A g M hM hg N
    (ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean)
    (integrable_killed_occupation m A B hAB a g hmean)
    (integrable_truncated_killed_occupation m A a g M hM hg N)
    (integrable_vExitTime_tail m A a M N hmean)

/-- The real exit-time tail used in the occupation estimate agrees with the
extended-nonnegative expectation of the same tail. -/
theorem ofReal_integral_vExitTime_tail (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (M : ℝ) (hM : 0 ≤ M) (N : ℕ) (hmean : expectedExitTime m A a ≠ ⊤) :
    ENNReal.ofReal (∫ x, if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0
      ∂srwLaw m a) = ENNReal.ofReal M *
      ∫⁻ x in {x | N < (vExitTime A x).toNat}, (vExitTime A x : ℝ≥0∞) ∂srwLaw m a := by
  have hm : Measurable (fun x : ℕ → ℤ => (vExitTime A x).toNat) :=
    (measurable_of_countable (fun n : ℕ∞ => n.toNat)).comp (measurable_vExitTime A)
  have hs : MeasurableSet {x : ℕ → ℤ | N < (vExitTime A x).toNat} :=
    measurableSet_lt measurable_const hm
  have hnonneg : 0 ≤ᵐ[srwLaw m a] (fun x =>
      if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0) := by
    filter_upwards [] with x
    split_ifs <;> positivity
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_vExitTime_tail m A a M N hmean) hnonneg]
  rw [← lintegral_const_mul' (ENNReal.ofReal M) _ ENNReal.ofReal_ne_top]
  rw [← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
  by_cases h : N < (vExitTime A x).toNat
  · simp only [h, ↓reduceIte, Set.indicator_of_mem, Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_natCast, ← ENat.natCast_toNat hx]
    simp
  · simp [h]

/-- Scaling the occupation error turns it into the corresponding normalized
exit-time tail, provided the truncation threshold dominates `T`. -/
theorem scaled_green_occupation_tail_le (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (B : Finset ℤ) (hAB : A ⊆ B) (a : ℤ) (g : ℤ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ b ∈ A, |g b| ≤ M) (N : ℕ)
    (hmean : expectedExitTime m A a ≠ ⊤) (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0∞)
    (hT : T ≤ ENNReal.ofReal c * ((N + 1 : ℕ) : ℝ≥0∞)) :
    ENNReal.ofReal (c * |(∑ b ∈ B, greenFn m A a b * g b) -
      ∫ x, ∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0 ∂srwLaw m a|) ≤
      ENNReal.ofReal M * ∫⁻ x in {x | T ≤ ENNReal.ofReal c *
        (vExitTime A x : ℝ≥0∞)}, ENNReal.ofReal c * (vExitTime A x : ℝ≥0∞)
        ∂srwLaw m a := by
  let E : Set (ℕ → ℤ) := {x | N < (vExitTime A x).toNat}
  let F : Set (ℕ → ℤ) := {x | T ≤ ENNReal.ofReal c * (vExitTime A x : ℝ≥0∞)}
  have hEF : E ⊆ F := by
    intro x hx
    have hne : vExitTime A x ≠ ⊤ := by
      intro h
      simp [E, h] at hx
    have hx' : N + 1 ≤ (vExitTime A x).toNat := Nat.succ_le_of_lt hx
    have hcast : ((N + 1 : ℕ) : ℝ≥0∞) ≤ (vExitTime A x : ℝ≥0∞) := by
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hx'
    exact hT.trans (by gcongr)
  have hbound := abs_green_occupation_tail_le m A B hAB a g M hM hg N hmean
  calc
    _ ≤ ENNReal.ofReal (c * ∫ x,
        if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0
        ∂srwLaw m a) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbound hc)
    _ = ENNReal.ofReal c * (ENNReal.ofReal M *
        ∫⁻ x in E, (vExitTime A x : ℝ≥0∞) ∂srwLaw m a) := by
      rw [ENNReal.ofReal_mul hc, ofReal_integral_vExitTime_tail m A a M hM N hmean]
    _ = ENNReal.ofReal M * ∫⁻ x in E, ENNReal.ofReal c *
        (vExitTime A x : ℝ≥0∞) ∂srwLaw m a := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ac_rfl
    _ ≤ ENNReal.ofReal M * ∫⁻ x in F, ENNReal.ofReal c *
        (vExitTime A x : ℝ≥0∞) ∂srwLaw m a := by
      gcongr

/-- The natural-number truncation `⌊T m⌋` includes every time strictly
before `T` on the scale `m⁻¹`. -/
theorem normalized_floor_threshold (m T : ℝ) (hm : 0 < m) :
    ENNReal.ofReal T ≤ ENNReal.ofReal m⁻¹ *
      ((⌊T * m⌋₊ + 1 : ℕ) : ℝ≥0∞) := by
  have hf : T * m < (⌊T * m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (T * m)
  have hbound : T ≤ m⁻¹ * ((⌊T * m⌋₊ : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left hf.le (inv_nonneg.mpr hm.le)
    have heq : m⁻¹ * (T * m) = T := by field_simp
    rw [heq] at h
    exact h
  calc
    ENNReal.ofReal T ≤ ENNReal.ofReal (m⁻¹ * ((⌊T * m⌋₊ : ℝ) + 1)) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = _ := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
      congr 1
      convert ENNReal.ofReal_natCast (⌊T * m⌋₊ + 1) using 1; push_cast; rfl

/-- The Green-sum truncation error at time `T` is controlled by the
normalized exit-time tail at the same time. -/
theorem normalized_green_occupation_tail_le (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (B : Finset ℤ) (hAB : A ⊆ B) (a : ℤ) (g : ℤ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ b ∈ A, |g b| ≤ M)
    (hmean : expectedExitTime m A a ≠ ⊤) (scale T : ℝ) (hscale : 0 < scale) :
    ENNReal.ofReal |scale⁻¹ * (∑ b ∈ B, greenFn m A a b * g b) -
      scale⁻¹ * ∫ x, ∑ n ∈ Finset.range ⌊T * scale⌋₊,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0 ∂srwLaw m a| ≤
      ENNReal.ofReal M * ∫⁻ x in {x | ENNReal.ofReal T ≤ ENNReal.ofReal scale⁻¹ *
        (vExitTime A x : ℝ≥0∞)}, ENNReal.ofReal scale⁻¹ * (vExitTime A x : ℝ≥0∞)
        ∂srwLaw m a := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  exact scaled_green_occupation_tail_le m A B hAB a g M hM hg ⌊T * scale⌋₊ hmean
    scale⁻¹ (inv_nonneg.mpr hscale.le) (ENNReal.ofReal T) (normalized_floor_threshold scale T hscale)

end MatedCRT
