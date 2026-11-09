import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Cutoff tests and restricted moments (fp-S2h, z1)

Written argument: notes/fp-gaps/CHATGPT-cone-good-set.md, Section 1.2, (2)-(4) and Section 2.2, (13).
For an open set `U ⊆ ℂ` with nonempty complement, the cutoffs `θₙ(x) = min {1, n · dist(x, ℂ \ U)}` are continuous,
take values in `[0,1]`, increase in `n`, and converge pointwise to the indicator `1_U`. Hence, for a measurable
nonnegative `f`, `∫_U f dν = supₙ ∫ θₙ f dν` (monotone convergence). This is the identity used to read restricted
integrals `∫_U φ dν` off countably many moment coordinates.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The cutoff `x ↦ min {1, n · dist(x, ℂ \ U)}` (CHATGPT-cone-good-set.md (2)). -/
noncomputable def cutoffBall (U : Set ℂ) (n : ℕ) (x : ℂ) : ℝ :=
  min 1 (n * infDist x Uᶜ)

theorem continuous_cutoffBall (U : Set ℂ) (n : ℕ) : Continuous (cutoffBall U n) := by
  unfold cutoffBall
  exact continuous_const.min (continuous_const.mul (continuous_infDist_pt (s := Uᶜ)))

theorem cutoffBall_nonneg (U : Set ℂ) (n : ℕ) (x : ℂ) : 0 ≤ cutoffBall U n x :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) infDist_nonneg)

theorem cutoffBall_le_one (U : Set ℂ) (n : ℕ) (x : ℂ) : cutoffBall U n x ≤ 1 :=
  min_le_left _ _

theorem cutoffBall_mono (U : Set ℂ) {n m : ℕ} (h : n ≤ m) (x : ℂ) :
    cutoffBall U n x ≤ cutoffBall U m x :=
  min_le_min_left _ (mul_le_mul_of_nonneg_right (by exact_mod_cast h) infDist_nonneg)

theorem cutoffBall_eq_zero_of_notMem {U : Set ℂ} {x : ℂ} (hx : x ∉ U) (n : ℕ) :
    cutoffBall U n x = 0 := by
  have hmem : x ∈ Uᶜ := hx
  simp [cutoffBall, infDist_zero_of_mem hmem]

theorem exists_cutoffBall_eq_one {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) {x : ℂ} (hx : x ∈ U) :
    ∃ n : ℕ, cutoffBall U n x = 1 := by
  have hnot : x ∉ closure Uᶜ := by
    simpa [closure_compl, hU.interior_eq] using hx
  have hpos : 0 < infDist x Uᶜ := (infDist_pos_iff_notMem_closure hUc).1 hnot
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / infDist x Uᶜ)
  refine ⟨n, ?_⟩
  have h1 : 1 < (n : ℝ) * infDist x Uᶜ := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  unfold cutoffBall
  exact min_eq_left h1.le

/-- Pointwise limit of the cutoffs in `ℝ≥0∞`: `supₙ ofReal (θₙ x) * f x = 1_U(x) f(x)` for open `U` with nonempty
complement. -/
theorem iSup_cutoff_mul_eq_indicator {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (f : ℂ → ℝ≥0∞) (x : ℂ) :
    (⨆ n : ℕ, ENNReal.ofReal (cutoffBall U n x) * f x) = U.indicator f x := by
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun n => ?_
      exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (cutoffBall_le_one U n x))
    · obtain ⟨N, hN⟩ := exists_cutoffBall_eq_one hU hUc hx
      refine le_iSup_of_le N ?_
      rw [hN]
      simp
  · rw [indicator_of_notMem hx]
    have h0 : ∀ n : ℕ, ENNReal.ofReal (cutoffBall U n x) * f x = 0 := fun n => by
      simp [cutoffBall_eq_zero_of_notMem hx n]
    simp [h0]

/-- Restricted integrals as a supremum of countably many cutoff integrals (CHATGPT-cone-good-set.md (13), the
monotone-convergence step): for an open `U` with nonempty complement and a measurable `f`,
`∫⁻ x in U, f x ∂ν = supₙ ∫⁻ x, ofReal (θₙ x) * f x ∂ν`. -/
theorem lintegral_restrict_open_eq_iSup {ν : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in U, f x ∂ν = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (cutoffBall U n x) * f x ∂ν := by
  have hmeas : ∀ n : ℕ, Measurable fun x => ENNReal.ofReal (cutoffBall U n x) * f x := fun n =>
    (ENNReal.measurable_ofReal.comp (continuous_cutoffBall U n).measurable).mul hf
  have hmono : Monotone fun n : ℕ => fun x => ENNReal.ofReal (cutoffBall U n x) * f x := by
    intro n m h x
    have := ENNReal.ofReal_le_ofReal (cutoffBall_mono U h x)
    show ENNReal.ofReal (cutoffBall U n x) * f x ≤ ENNReal.ofReal (cutoffBall U m x) * f x
    gcongr
  rw [← lintegral_indicator hU.measurableSet]
  simp_rw [← iSup_cutoff_mul_eq_indicator hU hUc f]
  rw [lintegral_iSup hmeas hmono]

end MatedCRT
