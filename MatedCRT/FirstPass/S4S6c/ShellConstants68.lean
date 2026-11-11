import MatedCRT.FirstPass.S6r.Constants

/-!
# The constants of the shell-chain core

`shellK68 γ ρ ω₀ ζ` is a `Constants68 γ ρ` (S6r/Constants.lean:41) with the mesh exponent `ω := ω₀` and the window
exponent `ζ`. Its ball ratio `c0 = exp(-2)/32` is a universal number, and its sparsity constant
`s1 = c0^βm/44` with `βm = (2+γ)²/2 + 1` depends on `γ` only. So `c0` and `s1` are fixed before `s₀` and before the
window constants `C, C'` of the prevalence bound (the order `∃ s₁, s₂ ∀ s₀` of `UniformConstantOrderLowerBoundStmt`,
S6d.lean:95).

Configuration choices, not relations stated in the sources: the Green, exit and good-annulus constants `C = Cd = Cg = 1`
of the record. They are NOT linked to the constants of the Draft inputs `hG, hE, hC` (Lemmas 2.16, 2.18, 2.8), nor to the
window constants `C_good = C_hprev` or the hone constant `C_hone` (named binders of the chain). The constraint
`c0 ≤ exp(-2C)/16` of the record holds for `C = 1`.
-/

namespace MatedCRT
namespace Lemma68ShellConstants

open MatedCRT.Lemma68Window

/-- **The shell-chain constants.** `c0 = exp(-2)/32 ∈ (0, 1/5)` (S6r/Constants.lean, `hc0'`, `hc0C`); `s1 = c0^βm/44`
(`hs1small`, `44 s1 ≤ c0^βm`). -/
noncomputable def shellK68 (γ ρ ω₀ ζ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) : Constants68 γ ρ where
  βm := (2 + γ) ^ 2 / 2 + 1
  ω := ω₀
  C := 1
  Cd := 1
  Cg := 1
  ζ := ζ
  c0 := Real.exp (-2) / 32
  s1 := (Real.exp (-2) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) / 44
  hγ0 := hγ0
  hγ2 := hγ2
  hρ0 := hρ0
  hρ1 := hρ1
  hβ := by linarith
  hω := hω0
  hC := one_pos
  hCd := one_pos
  hCg := one_pos
  hζ0 := hζ0
  hζ1 := hζ1
  hc0 := by positivity
  hc0' := by
    have h1 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    linarith
  hc0C := by
    have h1 : Real.exp (-(2 * (1 : ℝ))) = Real.exp (-2) := by norm_num
    have h2 : 0 < Real.exp (-2) := Real.exp_pos _
    rw [h1]
    linarith
  hs1 := by positivity
  hs1small := le_of_eq (by ring)

/-- The ball ratio of the shell-chain constants is `exp(-2)/32`, a universal number (independent of `ω₀, ζ, ρ`). -/
theorem shellK68_c0 (γ ρ ω₀ ζ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    (shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).c0 = Real.exp (-2) / 32 := rfl

/-- The sparsity constant of the shell-chain constants depends on `γ` only: `s1 = c0^βm/44` with `βm = (2+γ)²/2 + 1`. -/
theorem shellK68_s1 (γ ρ ω₀ ζ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    (shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).s1 =
      (Real.exp (-2) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) / 44 := rfl

/-- **The shell-chain constants at the Green constant `CG`.** `shellKCG … CG hCG` is a
`Constants68 γ ρ` with the Green constant `C := CG` (the constant of the leaf event `greenLowEvent68 S ω₀ ρ CG`), the ball
ratio `c0 := exp(-2CG)/32` (= `Lemma68ConstOrder.shellC0 CG`, which is `shellC068` at `CG = 1`) and the sparsity constant
`s1 := c0^βm/44`. The constraints `hc0'` (`c0 ≤ 1/24`) and `hc0C` (`c0 ≤ exp(-2C)/16`) hold for every `CG > 0`. `Cd = Cg = 1` as in
`shellK68`, which is kept unchanged. -/
noncomputable def shellKCG (γ ρ ω₀ ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG) : Constants68 γ ρ where
  βm := (2 + γ) ^ 2 / 2 + 1
  ω := ω₀
  C := CG
  Cd := 1
  Cg := 1
  ζ := ζ
  c0 := Real.exp (-(2 * CG)) / 32
  s1 := (Real.exp (-(2 * CG)) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) / 44
  hγ0 := hγ0
  hγ2 := hγ2
  hρ0 := hρ0
  hρ1 := hρ1
  hβ := by linarith
  hω := hω0
  hC := hCG
  hCd := one_pos
  hCg := one_pos
  hζ0 := hζ0
  hζ1 := hζ1
  hc0 := by positivity
  hc0' := by
    have h1 : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  hc0C := by
    have h2 : 0 < Real.exp (-(2 * CG)) := Real.exp_pos _
    linarith
  hs1 := by positivity
  hs1small := le_of_eq (by ring)

/-- The ball ratio of `shellKCG` is `exp(-2CG)/32`. -/
theorem shellKCG_c0 (γ ρ ω₀ ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG) :
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).c0 = Real.exp (-(2 * CG)) / 32 := rfl

/-- The Green constant of `shellKCG` is `CG` (the leaf `hGreen` constant agrees with `greenLowEvent68`). -/
theorem shellKCG_C (γ ρ ω₀ ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG) :
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).C = CG := rfl

/-- The sparsity constant of `shellKCG` is `c0^βm/44` with `βm = (2+γ)²/2 + 1`. -/
theorem shellKCG_s1 (γ ρ ω₀ ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG) :
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).s1 =
      (Real.exp (-(2 * CG)) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) / 44 := rfl

/-- **The walk exponent bound.** If
`0 < ε ≤ 1`, `2ω₀ < κ` and `100 ε^{2ω₀} ≤ R`, then `ε^κ ≤ R/8`. This is the second conjunct `ε^{K.ω} ≤ R/8` of hWalk, with the
separate walk exponent `κ` in place of `K.ω`; `R ≥ r² ≥ 100 ε^{2ω₀}` for `r ≥ 10 ε^{ω₀}`. Taking `κ = 2/(2+γ)² - ζ` is
allowed: `2ω₀ < κ` is the Eps antecedent `2 ω₀ < 2/(2+γ)² - ζ`. -/
theorem pow_le_div_eight_of_two_omega {ε ω₀ κ R : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hκ : 2 * ω₀ < κ)
    (hR : 100 * ε ^ (2 * ω₀) ≤ R) : ε ^ κ ≤ R / 8 := by
  have h1 : ε ^ κ ≤ ε ^ (2 * ω₀) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hκ.le
  have h2 : 0 ≤ ε ^ (2 * ω₀) := Real.rpow_nonneg hε0.le _
  linarith

end Lemma68ShellConstants
end MatedCRT
#print axioms MatedCRT.Lemma68ShellConstants.pow_le_div_eight_of_two_omega
