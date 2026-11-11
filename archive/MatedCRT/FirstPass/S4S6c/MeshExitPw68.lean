import MatedCRT.FirstPass.S4S6c.HoneSetup239_68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S4S6c.Guard68S10

/-!
# The exit-cell mesh bound at the walk radius `ρ + dyadicD r / 100`

The binder `hmeshExit` of the goodEnv localisation (l.13-24) asks that the cells of mesh `ε` meeting
the ball `B(0, ρ + h)`, `h = dyadicD r / 100`, have diameter at most `h`. The walk stops at its exit vertex, which lies in a
cell meeting `B(0, ρ + h)` but not necessarily in `B(0, ρ)`. The bound at radius `ρ` is not enough.

Route.
* `hmesh_local_of_cellSize` (HoneSetup239_68.lean:197, Draft Lemma 2.8 at the mesh radius `(1+ρ)/2`) gives the mesh bound on
  `B(0, (1+ρ)/2)` from the cell-size event at `(1+ρ)/2 = rhoCell68 ρ`, under `ε ≤ 1`, `ε^κ ≤ 1/100` and `10 ε^{ω₀} ≤ r`.
* `ε ≤ 1` and `ε^κ ≤ 1/100` follow from the Eps hypothesis `ε ≤ shellEps0Z γ α ω₀ ζ` (Guard68S10.lean:372-390) and
  `2ω₀ < κ`, `κ = 2/(2+γ)² - ζ`: `ε^κ = ε^{κ-2ω₀} ε^{2ω₀} ≤ shellC068 = exp(-2)/32`.
* The radius inclusion `B(0, ρ + h) ⊆ B(0, (1+ρ)/2)` needs `h ≤ (1-ρ)/2`. Since `h ≤ dyadicD r ≤ dyadicD r ^ shortExp ζ`
  (`le_rpow_short68`, ShellWindowRf68.lean) and `dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ = (1-ρ)/2` by the radius cutoff
  `hRcut` of `ShellOneTestOrderAeEpsStmt` (ShellHoneInst68.lean, the cutoff clause next to `R ≤ rAmp q0 ζ`), it holds for every
  `0 < r ≤ R`. No further smallness condition on `r` is needed.

Terminology: Armstrong-Kuusi-Mourrat (cells `H^ε_a`, mesh), Duplantier-Sheffield (boundary-length parametrisation `η`),
Armitage-Gardiner (balls).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68MeshExitPw

open MatedCRT.Lemma68HoneSetup239 MatedCRT.Lemma68WindowRf MatedCRT.Lemma68Window
open MatedCRT.Lemma68HoneCellGood MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder

/-- `shellEps0Z ≤ 1`: `shellEps0 ≤ exp(-2)/2 ≤ 1`. -/
lemma shellEps0Z_le_one (γ α ω₀ ζ : ℝ) : shellEps0Z γ α ω₀ ζ ≤ 1 := by
  have h1 : shellEps0 γ α ω₀ ≤ Real.exp (-2) / 2 := min_le_left _ _
  have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h3 := shellEps0Z_le γ α ω₀ ζ
  linarith

/-- `shellC068 = exp(-2)/32 ≤ 1/100`: `exp 2 ≥ 4`, so `exp(-2) ≤ 1/4`. -/
lemma shellC068_le_hundredth : shellC068 ≤ 1 / 100 := by
  have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith
  have h4 : Real.exp (-2) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]; norm_num
  have h5 : Real.exp (-2) ≤ 1 / 4 := by
    nlinarith [Real.exp_pos (-2)]
  unfold shellC068
  linarith

/-- **The exit-cell mesh bound at the radius `ρ + dyadicD r / 100`.** From the cell-size
event at the cell-control radius `rhoCell68 ρ = (1+ρ)/2` and the Eps hypotheses of `ShellOneTestOrderAeEpsStmt`
(`0 < ω₀`, `2ω₀ < κ`, `0 < ε ≤ shellEps0Z`, the cutoff `hRcut`, `10 ε^{ω₀} ≤ r ≤ R`), every cell of mesh `ε` meeting
`B(0, ρ + dyadicD r / 100)` has diameter at most `dyadicD r / 100`. -/
theorem hmeshExit_of_cellSize {γ ζ ρ ω₀ α R r ε : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hω₀ : 0 < ω₀) (hκ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hζ1 : ζ < 1 / 2)
    (hε : 0 < ε) (hεS : ε ≤ shellEps0Z γ α ω₀ ζ)
    (hRcut : ∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < rhoCell68 ρ - ρ)
    (hrR : r ≤ R) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hω : ω ∈ cellSizeEvent68 S γ ζ (rhoCell68 ρ) ε) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball (0 : ℂ) (ρ + dyadicD r / 100)) := by
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hrε
  have hε1 : ε ≤ 1 := hεS.trans (shellEps0Z_le_one γ α ω₀ ζ)
  have hd : 0 < 2 / (2 + γ) ^ 2 - ζ - 2 * ω₀ := by linarith
  have hsplit : ε ^ (2 / (2 + γ) ^ 2 - ζ) = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  have hcut1 : ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ shellC068 := shellEps0Z_pow_le hε hd hεS
  have hcut2 : ε ^ (2 * ω₀) ≤ 1 := Real.rpow_le_one hε.le hε1 (by linarith)
  have hc0 : 0 < shellC068 := by unfold shellC068; positivity
  have hκ100 : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ 1 / 100 := by
    rw [hsplit]
    calc ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) ≤ shellC068 * 1 :=
          mul_le_mul hcut1 hcut2 (Real.rpow_nonneg hε.le _) hc0.le
      _ ≤ 1 / 100 := by rw [mul_one]; exact shellC068_le_hundredth
  have hmesh := hmesh_local_of_cellSize (ρ := ρ) S hω₀ hκ hε1 hκ100 hε le_rfl ω hω r hr hrε
  have hshort : dyadicD r ≤ dyadicD r ^ shortExp ζ :=
    le_rpow_short68 (dyadicD_pos r) (dyadicD_le_one r) (by unfold shortExp; linarith)
  have hcutR := hRcut r hr hrR
  have hgap : rhoCell68 ρ - ρ = (1 - ρ) / 2 := by unfold rhoCell68; ring
  have hsmall : dyadicD r / 100 ≤ (1 - ρ) / 2 := by
    have := dyadicD_pos r
    linarith
  have hsub : ball (0 : ℂ) (ρ + dyadicD r / 100) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) :=
    ball_subset_ball (by linarith)
  unfold CellDiamLe at hmesh ⊢
  intro k hk p hp q hq
  exact hmesh k (hk.mono (inter_subset_inter_right _ hsub)) p hp q hq

/-- The cell entry at a general window constant: `ε ≤ c₀W^{1/d}` with `0 < c₀W` and `0 < d` gives `ε^d ≤ c₀W`. -/
lemma rpow_le_c0W_of_le {ε c0W d : ℝ} (hε : 0 < ε) (hc : 0 < c0W) (hd : 0 < d) (hle : ε ≤ c0W ^ (1 / d)) :
    ε ^ d ≤ c0W := by
  calc ε ^ d ≤ (c0W ^ (1 / d)) ^ d := Real.rpow_le_rpow hε.le hle hd.le
    _ = c0W := by rw [← Real.rpow_mul hc.le, one_div_mul_cancel hd.ne', Real.rpow_one]

/-- **The exit-cell mesh bound with a general window constant.** `hmeshExit_of_cellSize` with
the Eps threshold `shellEps0Z` (its constant `shellC068`) replaced by the threshold `min (shellEps0CG γ α ω₀ CG) (c0W^(1/(κ-2ω₀)))`,
which is `shellEps0ZCG γ α ω₀ ζ CG` when `c0W = shellC0 CG`. Hypotheses on the window constant that the proof uses:
`0 < c0W` (sign in `mul_le_mul`) and `c0W ≤ 1/100` (the cut `ε^κ ≤ 1/100` of `hmesh_local_of_cellSize`). The Green constant
enters only through `0 ≤ CG` (for `ε ≤ 1`: `shellEps0CG ≤ exp(-2CG)/2 ≤ 1`). The sparsity exponent does not occur. -/
theorem hmeshExit_of_cellSize_g {γ ζ ρ ω₀ α R r ε CG c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (hω₀ : 0 < ω₀) (hκ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 ≤ CG) (hc0W : 0 < c0W) (hc0W1 : c0W ≤ 1 / 100)
    (hε : 0 < ε) (hεS : ε ≤ min (shellEps0CG γ α ω₀ CG) (c0W ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀))))
    (hRcut : ∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < rhoCell68 ρ - ρ)
    (hrR : r ≤ R) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hω : ω ∈ cellSizeEvent68 S γ ζ (rhoCell68 ρ) ε) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball (0 : ℂ) (ρ + dyadicD r / 100)) := by
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hrε
  have hd : 0 < 2 / (2 + γ) ^ 2 - ζ - 2 * ω₀ := by linarith
  have hε1 : ε ≤ 1 := by
    have h1 : shellEps0CG γ α ω₀ CG ≤ Real.exp (-(2 * CG)) / 2 := by
      unfold shellEps0CG; exact min_le_left _ _
    have h2 : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : shellEps0CG γ α ω₀ CG ≤ 1 := by linarith
    exact (hεS.trans (min_le_left _ _)).trans h3
  have hcut1 : ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ c0W :=
    rpow_le_c0W_of_le hε hc0W hd (hεS.trans (min_le_right _ _))
  have hsplit : ε ^ (2 / (2 + γ) ^ 2 - ζ) = ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  have hcut2 : ε ^ (2 * ω₀) ≤ 1 := Real.rpow_le_one hε.le hε1 (by linarith)
  have hκ100 : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ 1 / 100 := by
    rw [hsplit]
    calc ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) * ε ^ (2 * ω₀) ≤ c0W * 1 :=
          mul_le_mul hcut1 hcut2 (Real.rpow_nonneg hε.le _) hc0W.le
      _ ≤ 1 / 100 := by rw [mul_one]; exact hc0W1
  have hmesh := hmesh_local_of_cellSize (ρ := ρ) S hω₀ hκ hε1 hκ100 hε le_rfl ω hω r hr hrε
  have hshort : dyadicD r ≤ dyadicD r ^ shortExp ζ :=
    le_rpow_short68 (dyadicD_pos r) (dyadicD_le_one r) (by unfold shortExp; linarith)
  have hcutR := hRcut r hr hrR
  have hgap : rhoCell68 ρ - ρ = (1 - ρ) / 2 := by unfold rhoCell68; ring
  have hsmall : dyadicD r / 100 ≤ (1 - ρ) / 2 := by
    have := dyadicD_pos r
    linarith
  have hsub : ball (0 : ℂ) (ρ + dyadicD r / 100) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) :=
    ball_subset_ball (by linarith)
  unfold CellDiamLe at hmesh ⊢
  intro k hk p hp q hq
  exact hmesh k (hk.mono (inter_subset_inter_right _ hsub)) p hp q hq

/-- `shellC0 CG ≤ 1/100` for `1 ≤ CG`: `shellC0 CG = exp(-2CG)/32 ≤ exp(-2)/32 = shellC068 ≤ 1/100`. -/
lemma shellC0_le_hundredth {CG : ℝ} (hCG : 1 ≤ CG) : Lemma68ConstOrder.shellC0 CG ≤ 1 / 100 := by
  have h1 : Real.exp (-(2 * CG)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  have h2 := shellC068_le_hundredth
  unfold shellC068 at h2
  unfold Lemma68ConstOrder.shellC0
  linarith

/-- **The exit-cell mesh bound at the CG leaf.** `hmeshExit_of_cellSize_g` at the exact threshold
`shellEps0ZCG γ α ω₀ ζ CG` (Guard68S10.lean) and the window constant
`c0W = shellC0 CG`, for `1 ≤ CG`. -/
theorem hmeshExit_of_cellSize_CG {γ ζ ρ ω₀ α R r ε CG : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (hω₀ : 0 < ω₀) (hκ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hζ1 : ζ < 1 / 2) (hCG : 1 ≤ CG)
    (hε : 0 < ε) (hεS : ε ≤ shellEps0ZCG γ α ω₀ ζ CG)
    (hRcut : ∀ r' : ℝ, 0 < r' → r' ≤ R → (dyadicD r') ^ shortExp ζ < rhoCell68 ρ - ρ)
    (hrR : r ≤ R) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hω : ω ∈ cellSizeEvent68 S γ ζ (rhoCell68 ρ) ε) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball (0 : ℂ) (ρ + dyadicD r / 100)) :=
  hmeshExit_of_cellSize_g (c0W := Lemma68ConstOrder.shellC0 CG) S ω hω₀ hκ hζ1 (by linarith)
    (shellC0_bounds CG (by linarith)).1 (shellC0_le_hundredth hCG) hε hεS hRcut hrR hrε hω

end Lemma68MeshExitPw
end MatedCRT

#print axioms MatedCRT.Lemma68MeshExitPw.shellEps0Z_le_one
#print axioms MatedCRT.Lemma68MeshExitPw.shellC068_le_hundredth
#print axioms MatedCRT.Lemma68MeshExitPw.hmeshExit_of_cellSize
#print axioms MatedCRT.Lemma68MeshExitPw.rpow_le_c0W_of_le
#print axioms MatedCRT.Lemma68MeshExitPw.hmeshExit_of_cellSize_g
#print axioms MatedCRT.Lemma68MeshExitPw.shellC0_le_hundredth
#print axioms MatedCRT.Lemma68MeshExitPw.hmeshExit_of_cellSize_CG
