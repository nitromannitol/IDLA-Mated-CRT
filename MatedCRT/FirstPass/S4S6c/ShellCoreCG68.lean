import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.ShellConstants68

/-!
# The CG leaf thresholds of the hOne route (fp-S4S6c-b1-glue, z5)

For the leaf constant `K = shellKCG γ ρ ω₀ ζ CG` (`K.C = CG`, `K.c0 = c₀(CG) = exp(-2CG)/32 = shellC0 CG`,
`K.ω = ω₀`, `K.βm = (2+γ)²/2 + 1`), the threshold hypotheses of `shellOneTest_at_of_goodEnv_loc`
(B1Assembly68.lean, `hεc`, `hεs`, `hε1`, `hεcell`) follow from `ε ≤ shellEps0ZCG γ α ω₀ ζ CG` (Guard68S10.lean).
This is the CG version of the threshold facts of `shellOneTestPointwiseEps_of_goodEnv` (ShellCorePw68.lean).
-/

namespace MatedCRT
namespace Lemma68ShellCoreCG

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder

/-- The threshold facts `ε ≤ 16 K.c0`, `ε ≤ 1` and `ε ≤ ((100 K.c0)^K.βm/4)^(1/(α - 2 K.ω K.βm))` at the CG leaf. -/
theorem shellKCG_eps_le {γ ρ : ℝ} (K : Constants68 γ ρ) (ω₀ α ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    {ε : ℝ} (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) :
    ε ≤ 16 * K.c0 ∧ ε ≤ 1 ∧
      ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)) := by
  subst hK
  have h1 : shellEps0ZCG γ α ω₀ ζ CG ≤ shellEps0CG γ α ω₀ CG := min_le_left _ _
  have h2 : shellEps0CG γ α ω₀ CG ≤ Real.exp (-(2 * CG)) / 2 := min_le_left _ _
  have h3 : shellEps0CG γ α ω₀ CG ≤
      ((100 * shellC0 CG) ^ chosenBetaMinus γ / 4) ^ (1 / (α - 2 * ω₀ * chosenBetaMinus γ)) :=
    min_le_right _ _
  have hexp : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have h16 : 16 * (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG).c0 =
        Real.exp (-(2 * CG)) / 2 := by
      rw [shellKCG_c0]; ring
    rw [h16]
    linarith
  · linarith
  · exact le_trans (le_trans hεe h1) h3

/-- The cell entry at the CG leaf: `ε ^ (2/(2+γ)² - ζ) ≤ K.c0 r² / 100` from `ε ≤ shellEps0ZCG` and `10 ε^ω₀ ≤ r`
(the CG version of `hεcell` in `shellOneTestPointwiseEps_of_goodEnv`). -/
theorem shellKCG_eps_cell {γ ρ : ℝ} (K : Constants68 γ ρ) (ω₀ α ζ CG : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (hκ2 : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    {ε r : ℝ} (hε : 0 < ε) (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) (hr : 10 * ε ^ ω₀ ≤ r) :
    ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100 := by
  subst hK
  have hthr : ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ shellC0 CG :=
    shellEps0ZCG_pow_le hε (by linarith) hεe
  have hc0 : 0 ≤ shellC0 CG := by unfold shellC0; positivity
  have hpow : 0 ≤ ε ^ ω₀ := Real.rpow_nonneg hε.le _
  have h2 : ε ^ (2 * ω₀) = (ε ^ ω₀) ^ 2 := by
    rw [show 2 * ω₀ = ω₀ * 2 by ring, Real.rpow_mul hε.le, Real.rpow_two]
  have hsplit : ε ^ (2 / (2 + γ) ^ 2 - ζ) = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  have hsq : 100 * (ε ^ ω₀) ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul hr hr (by linarith) (by linarith)
    nlinarith
  show ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ shellC0 CG * r ^ 2 / 100
  calc ε ^ (2 / (2 + γ) ^ 2 - ζ)
      = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := hsplit
    _ ≤ shellC0 CG * ε ^ (2 * ω₀) := mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg hε.le _)
    _ = shellC0 CG * (ε ^ ω₀) ^ 2 := by rw [h2]
    _ ≤ shellC0 CG * (r ^ 2 / 100) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        linarith
    _ = shellC0 CG * r ^ 2 / 100 := by ring

end Lemma68ShellCoreCG
end MatedCRT

#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_le
#print axioms MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_cell
