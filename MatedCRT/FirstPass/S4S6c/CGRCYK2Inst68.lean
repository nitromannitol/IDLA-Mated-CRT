import MatedCRT.FirstPass.S4S6c.ShellConstants68

/-!
# Bounded check of the doubled shell exponent `K.ω = 2 * ω₀` (fp-S4S6c-cgrcy-k2, z5)

Lead pointer (q3, reports/q3.md): take the leaf's shell exponent `K.ω := 2 * ω₀` (the mesh exponent stays `ω₀`), so that the
square premise `4 * ε ^ K.ω ≤ r ^ 2` of `CGResWalkG68.walkG_pt_sq` (CGResWalkG68.lean:117) follows from `10 * ε ^ ω₀ ≤ r`.

This file records the checks. The algebra of the pointer holds: `four_rpow_double_le_sq` (the walk square premise at `2 * ω₀`)
and `ten_rpow_double_le` (the leaf radius premise `hrε` at `2 * ω₀`). The walk `walkG_pt_sq` takes `K` as a free argument and
uses no property of `K` other than `hsq`, so the walk is not the obstacle. The one-test does not close without named inputs:

* `B1GoodEnvSplit68.shellOneTest_at_of_goodEnv_loc_split` (B1GoodEnvSplit68.lean:160) binds `hK : K = shellKCG γ ρ ω₀ …`
  (line 170). `shellKCG` sets `ω := ω₀` (ShellConstants68.lean:74-80), so the leaf cannot be applied at `K.ω = 2 * ω₀`
  (`shellKCG_omega_ne_double`). Using the pointer needs a copy of the leaf with the shell exponent decoupled from `ω₀`.
* Its binder `hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζ` (line 175) becomes `2 * (2 * ω₀) < 2 / (2 + γ) ^ 2 - ζ`. The Stmt
  premises do not give it (`four_omega_not_implied`: the Stmt has only `2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ`).
* Its binder `hα : 2 * K.ω * K.βm < α` (line 176) becomes `2 * (2 * ω₀) * ((2 + γ) ^ 2 / 2 + 1) < α`. The Stmt has only
  `2 * ω₀ * chosenBetaMinus γ < α` (LICGRCY68.lean:50, S6d.lean:30).

Terminology: Duplantier-Sheffield (walk exit of an annulus), Armitage-Gardiner (balls), Armstrong-Kuusi-Mourrat (shell order).
-/

namespace MatedCRT
namespace Lemma68CGRCYK2

open MatedCRT.Lemma68ShellConstants

/-- The square premise of `walkG_pt_sq` at the doubled exponent: `10 * ε ^ ω₀ ≤ r` gives `4 * ε ^ (2 * ω₀) ≤ r ^ 2`. -/
theorem four_rpow_double_le_sq {ε ω₀ r : ℝ} (hε : 0 < ε) (hr : 10 * ε ^ ω₀ ≤ r) :
    4 * ε ^ (2 * ω₀) ≤ r ^ 2 := by
  have hq : 0 ≤ ε ^ ω₀ := Real.rpow_nonneg hε.le ω₀
  have hpow : ε ^ (2 * ω₀) = (ε ^ ω₀) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hε.le, Real.rpow_two]
  have h10 : 0 ≤ 10 * ε ^ ω₀ := by linarith
  have hsq : (10 * ε ^ ω₀) * (10 * ε ^ ω₀) ≤ r * r := mul_le_mul hr hr h10 (le_trans h10 hr)
  rw [hpow]
  nlinarith [mul_nonneg hq hq]

/-- The leaf radius premise at the doubled exponent: `10 * ε ^ ω₀ ≤ r` gives `10 * ε ^ (2 * ω₀) ≤ r` (`hrε` at `K.ω = 2 * ω₀`). -/
theorem ten_rpow_double_le {ε ω₀ r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω₀ : 0 ≤ ω₀) (hr : 10 * ε ^ ω₀ ≤ r) :
    10 * ε ^ (2 * ω₀) ≤ r := by
  have h : ε ^ (2 * ω₀) ≤ ε ^ ω₀ := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  linarith

/-- The shell exponent of `shellKCG … ω₀ …` is `ω₀`, never `2 * ω₀` when `ω₀ > 0`: the leaf's `hK` pins `K.ω = ω₀`. -/
theorem shellKCG_omega_ne_double (γ ρ ω₀ ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG) :
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).ω ≠ 2 * ω₀ := by
  intro h
  have h' : ω₀ = 2 * ω₀ := h
  linarith

/-- The arithmetic premises of `ShellOneTestOrderAeCGRCYStmt` (`ω₀ < 2/(2+γ)²-ζ`, `2 ω₀ < 2/(2+γ)²-ζ`) do not give the leaf's
`2 * K.ω < 2/(2+γ)²-ζ` (hκ2, B1GoodEnvSplit68.lean:175) at `K.ω = 2 * ω₀`. Witness: γ = 1, ζ = 1/100, ω₀ = 1/10. -/
theorem four_omega_not_implied :
    ∃ γ ζ ω₀ : ℝ, 0 < γ ∧ γ < 2 ∧ 0 < ζ ∧ ζ < 1 / 2 ∧ 0 < ω₀ ∧
      ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧ 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
      ¬ (2 * (2 * ω₀) < 2 / (2 + γ) ^ 2 - ζ) :=
  ⟨1, 1 / 100, 1 / 10, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

#print axioms MatedCRT.Lemma68CGRCYK2.four_rpow_double_le_sq
#print axioms MatedCRT.Lemma68CGRCYK2.ten_rpow_double_le
#print axioms MatedCRT.Lemma68CGRCYK2.shellKCG_omega_ne_double
#print axioms MatedCRT.Lemma68CGRCYK2.four_omega_not_implied

end Lemma68CGRCYK2
end MatedCRT
