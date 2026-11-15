import MatedCRT.FirstPass.Derived.AreaCellDegreeMoments
import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.FirstPass.Derived.AreaCellConductanceRows
import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Moments of the conductance rows at the root cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- The two root conductance rows admit a measurable square-integrable bound. -/
theorem MatedCRTEnv.IsValid.exists_twoRoot_row_bound
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Ω → ℝ≥0∞, Measurable D ∧
      (∫⁻ ω, D ω ^ (2 : ℝ) ∂S.P < ⊤) ∧
      ∀ᵐ ω ∂S.P,
        ENNReal.ofReal (∑' b : ℤ, (S.mult ε ω 0 b : ℝ)) +
          ENNReal.ofReal (∑' b : ℤ, (S.mult ε ω 1 b : ℝ)) ≤ D ω := by
  let X : ℤ → Ω → ℝ≥0∞ := fun k ω => (matedDeg (S.mult ε ω) k : ℝ≥0∞)
  have hm (k : ℤ) : Measurable (X k) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (hS.measurable_mdeg ε k)
  let D : Ω → ℝ≥0∞ := fun ω => 2 * max (X 0 ω) (X 1 ω)
  refine ⟨D, measurable_const.mul ((hm 0).max (hm 1)), ?_, ?_⟩
  · have h0 := hS.lintegral_matedDeg_pow_lt_top hε 0 2
    have h1 := hS.lintegral_matedDeg_pow_lt_top hε 1 2
    have hbound : ∀ ω, D ω ^ (2 : ℝ) ≤ 4 * (X 0 ω ^ (2 : ℕ) + X 1 ω ^ (2 : ℕ)) := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      dsimp [D]
      calc
        (2 * max (X 0 ω) (X 1 ω)) ^ 2 = 4 * (max (X 0 ω) (X 1 ω)) ^ 2 := by ring
        _ ≤ 4 * (X 0 ω ^ (2 : ℕ) + X 1 ω ^ (2 : ℕ)) := by
          gcongr
          rcases le_total (X 0 ω) (X 1 ω) with h | h
          · rw [max_eq_right h]
            exact le_add_left le_rfl
          · rw [max_eq_left h]
            exact le_add_right le_rfl
    refine (lintegral_mono hbound).trans_lt ?_
    change (∫⁻ ω, (4 : ℝ≥0∞) * (fun ω => X 0 ω ^ (2 : ℕ) + X 1 ω ^ (2 : ℕ)) ω ∂S.P) < ⊤
    rw [lintegral_const_mul 4 (f := fun ω => X 0 ω ^ (2 : ℕ) + X 1 ω ^ (2 : ℕ)) (((hm 0).pow_const 2).add ((hm 1).pow_const 2)),
      lintegral_add_left ((hm 0).pow_const 2)]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨h0, h1⟩)
  · filter_upwards [FirstPass.Derived.ae_isLocallyFiniteMult_of_isValid hS, hS.isAreaParametrized] with ω hlf ha
    have heq (k : ℤ) : (∑' b : ℤ, (S.mult ε ω k b : ℝ)) =
        (mdeg (S.mult ε ω) k : ℝ) := by
      rw [← areaCellConfig_pi_eq_tsum ha hε (S.mult ε ω) k]
      exact areaCellConfig_pi_eq_mdeg S ω ha hε (hlf ε hε) k
    rw [heq 0, heq 1]
    simp only [ENNReal.ofReal_natCast]
    dsimp [D, X, matedDeg]
    calc
      (mdeg (S.mult ε ω) 0 : ℝ≥0∞) + (mdeg (S.mult ε ω) 1 : ℝ≥0∞) ≤
          max (mdeg (S.mult ε ω) 0 : ℝ≥0∞) (mdeg (S.mult ε ω) 1 : ℝ≥0∞) +
          max (mdeg (S.mult ε ω) 0 : ℝ≥0∞) (mdeg (S.mult ε ω) 1 : ℝ≥0∞) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := by rw [two_mul]

end MatedCRT
