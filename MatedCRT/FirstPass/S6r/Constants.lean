import Mathlib

/-!
# S0: the constants of Lemma 6.8 on the short-window route

The constants are
fixed once, as functions of `(γ, ρ)` only, before `s₀` and before `ε`:
* `βm`: the volume exponent `β⁻ > (2+γ)²/2` (Lemma 2.7, `VolumeGrowthStmt`, the lower bound `δ^{βm} ≤ μ(B_δ)`);
* `ω`: the mesh exponent `ω₀ > 0` of Lemma 6.8 (`10 ε^{ω₀} ≤ r`);
* `C`: the Green constant (Lemma 2.16); `Cd`: the exit-time constant (Lemma 2.18, `N = 2`);
  `Cg`: the corrected good-annulus constant (`IsGoodAnnulusEvent`, Lemma 6.4 as corrected in S1);
* `ζ ∈ (0, 1/2)`: the short-window exponent, with `a = shortExp ζ = (1 + ζ)/2 ∈ (1/2, 3/4)`;
* `c0`: the ball ratio, with `c0 ≤ 1/24` (so that the instance of Lemma 2.16 at radius `r = R/8` covers
  `V(B_{c0 R})`) and `c0 ≤ exp(-2C)/16` as in `perState_local_bound`;
* `s1`: the sparsity constant with `44 s1 ≤ c0^βm` (as in `perState_local_bound`); `s2 = 1/2`.

The exponent conditions on `ω` in §2 of the redesign (mesh errors of Lemmas 2.8, 2.9, 2.16, 2.18) concern the
counting lower bound `|V(B_{c0 R}) \ A| ≥ c ε⁻¹ μ(B_{c0 R})`, which the local window statement does not use; they
are not recorded here.
-/

open Real

namespace MatedCRT
namespace Lemma68Window

/-- The short-window exponent `a = (1 + ζ)/2` of the redesign (S2.2): test radii lie in `[d, d^a]`. -/
noncomputable def shortExp (ζ : ℝ) : ℝ := (1 + ζ) / 2

lemma shortExp_nonneg {ζ : ℝ} (hζ : 0 ≤ ζ) : 0 ≤ shortExp ζ := by
  unfold shortExp; linarith

lemma shortExp_le_one {ζ : ℝ} (hζ : ζ ≤ 1) : shortExp ζ ≤ 1 := by
  unfold shortExp; linarith

lemma two_mul_shortExp (ζ : ℝ) : 2 * shortExp ζ = 1 + ζ := by
  unfold shortExp; ring

/-- The constants of Lemma 6.8 fixed in S0 (redesign §2), as a record of the chosen values and their defining
inequalities. Only `(γ, ρ)` enter the choice; `s₁` and `s₂` are fixed before `s₀`. -/
structure Constants68 (γ ρ : ℝ) where
  /-- the volume exponent `β⁻` (Lemma 2.7) -/
  βm : ℝ
  /-- the mesh exponent `ω₀` of Lemma 6.8 -/
  ω : ℝ
  /-- the Green constant `C` (Lemma 2.16) -/
  C : ℝ
  /-- the exit-time constant `C_d` (Lemma 2.18) -/
  Cd : ℝ
  /-- the corrected good-annulus constant `C_G` (S1; `IsGoodAnnulusEvent`) -/
  Cg : ℝ
  /-- the window exponent `ζ`, with `a = (1 + ζ)/2` -/
  ζ : ℝ
  /-- the ball ratio `c₀` -/
  c0 : ℝ
  /-- the sparsity constant `s₁` -/
  s1 : ℝ
  hγ0 : 0 < γ
  hγ2 : γ < 2
  hρ0 : 0 < ρ
  hρ1 : ρ < 1
  hβ : (2 + γ) ^ 2 / 2 < βm
  hω : 0 < ω
  hC : 0 < C
  hCd : 0 < Cd
  hCg : 0 < Cg
  hζ0 : 0 < ζ
  hζ1 : ζ < 1 / 2
  hc0 : 0 < c0
  hc0' : c0 ≤ 1 / 24
  hc0C : c0 ≤ Real.exp (-(2 * C)) / 16
  hs1 : 0 < s1
  hs1small : 44 * s1 ≤ c0 ^ βm

namespace Constants68

variable {γ ρ : ℝ} (K : Constants68 γ ρ)

/-- The second constant of Lemma 6.8, `s₂ = 1/2` (S0). -/
noncomputable def s2 : ℝ := 1 / 2

lemma s2_pos : 0 < s2 := by unfold s2; norm_num

lemma s2_lt_one : s2 < 1 := by unfold s2; norm_num

/-- The volume exponent is at least `1` (from `β⁻ > (2+γ)²/2 ≥ 2`). -/
lemma one_le_βm : 1 ≤ K.βm := by
  have h2 : (2 : ℝ) ≤ (2 + γ) ^ 2 / 2 := by nlinarith [K.hγ0]
  linarith [K.hβ]

lemma c0_lt_eighth : K.c0 < 1 / 8 := by
  linarith [K.hc0']

lemma s1_lt_one : K.s1 < 1 := by
  have h : K.c0 ^ K.βm ≤ 1 :=
    Real.rpow_le_one K.hc0.le (by linarith [K.hc0']) (by linarith [K.one_le_βm])
  linarith [K.hs1small]

lemma shortExp_le_one_of : shortExp K.ζ ≤ 1 :=
  _root_.MatedCRT.Lemma68Window.shortExp_le_one (by linarith [K.hζ1])

lemma shortExp_nonneg_of : 0 ≤ shortExp K.ζ :=
  _root_.MatedCRT.Lemma68Window.shortExp_nonneg K.hζ0.le

end Constants68

end Lemma68Window
end MatedCRT
