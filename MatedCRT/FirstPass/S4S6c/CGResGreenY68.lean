import MatedCRT.FirstPass.S4S6c.CGResWalkLoc68

/-!
# Pointwise producers of the split-leaf Green and walk binders at the Green exponent `ωG`
 (residual 75a)

`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` takes a Green exponent `ωG`, independent of the shell exponent `ω₀`,
with the event `greenLowEvent68 S ωG ρ CG ε`. The split leaf `B1Assembly68.shellOneTest_at_of_goodEnv_loc_g`
has two binders whose domain is `ball 0 (ρ - ε ^ K.ω)`: `hGreen` and `hWalk`. This file gives their pointwise
producers with `K.ω` replaced by `ωG`. Writing `e := 2 / (2 + γ) ^ 2 - ζ` (the shell radius exponent):

* `greenY_pt` (`hGreen`): the event `greenLowEvent68 S ωG ρ CG ε` gives the bound for `ε ^ ωG ≤ r'`. The body needs
  it for `ε ^ e ≤ r'`, which follows when `ε ^ ωG ≤ ε ^ e`, i.e. `e ≤ ωG` (for `0 < ε ≤ 1`).
  **Named hypothesis `hGe : e ≤ ωG`, not in the list of premises** (`2 * ω₀ < ωG` alone is not enough:
  for `ωG < e` the radii `r' ∈ [ε ^ e, ε ^ ωG)` are not covered by the event).
* `walkY_pt` (`hWalk`): the walk producer `Lemma68CGResWalkLoc.hWalk_pw_g_loc` at the exponent `e` (`K.ω := e`,
  `ωm := ω₀`; its hypotheses are `2 * ω₀ < e`, `ShellPtPremCG` clause 8, and `10 * ε ^ ω₀ ≤ r`). Its first conjunct
  lives on `ball 0 (ρ - ε ^ e)`, which lies in `ball 0 (ρ - ε ^ ωG)` when `e ≤ ωG`. Its second conjunct is already
  the split form `ε ^ e ≤ winRf / 8`.
* `shellEpsG68` is the constant `εG` of `LICGRCY68` (`0 < shellEpsG68 …`; `ε ≤ shellEpsG68 … → ε ≤ 1`).
-/

namespace MatedCRT
namespace Lemma68CGResGreenY

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly
open Lemma68ShellCoreCG

/-- **The mesh-range constant `εG` of `LICGRCY68`.** `εG := min 1 (shellEps0ZCG …)`:
positive, at most `1`, and at most `shellEps0ZCG`. Depends only on the constants `γ α ω₀ ζ CG`. -/
noncomputable def shellEpsG68 (γ α ω₀ ζ CG : ℝ) : ℝ :=
  min 1 (Lemma68Guard10.shellEps0ZCG γ α ω₀ ζ CG)

/-- `shellEpsG68` is positive. -/
lemma shellEpsG68_pos (γ α ω₀ ζ CG : ℝ) : 0 < shellEpsG68 γ α ω₀ ζ CG :=
  lt_min one_pos (Lemma68Guard10.shellEps0ZCG_pos γ α ω₀ ζ CG)

/-- A scale `ε ≤ shellEpsG68` is at most `1`. -/
lemma le_one_of_le_shellEpsG68 {γ α ω₀ ζ CG ε : ℝ} (h : ε ≤ shellEpsG68 γ α ω₀ ζ CG) : ε ≤ 1 :=
  le_trans h (min_le_left _ _)

/-- **`hGreen` at the Green exponent `ωG` (`greenY_pt`).** The body of the split-leaf binder `hGreen`
(`B1Assembly68.shellOneTest_at_of_goodEnv_loc_g`) with `K.ω` replaced by `ωG` and `K.C = CG`, pointwise at `ω`.
From the event `greenLowEvent68 S ωG ρ CG ε`, whose domain is `ball 0 (ρ - ε ^ ωG)` and whose range is `ε ^ ωG ≤ r'`,
and `ε ^ ωG ≤ ε ^ e` (`hGe : e ≤ ωG`, `0 < ε ≤ 1`). -/
theorem greenY_pt {γ ζ ρ CG ε ωG : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hGe : 2 / (2 + γ) ^ 2 - ζ ≤ ωG) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hG : ω ∈ greenLowEvent68 S ωG ρ CG ε) :
    ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ωG)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
      r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
      ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
        CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
            else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
          ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b := by
  have hle : ε ^ ωG ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hGe
  intro a ha r' hr' hrinf b hb
  exact hG a ha r' (le_trans hle hr') hrinf b hb

/-- **`hWalk` at the Green exponent `ωG` (`walkY_pt`).** The body of the split-leaf binder `hWalk`
(`B1Assembly68.shellOneTest_at_of_goodEnv_loc_g`) with `K.ω` replaced by `ωG`, pointwise at `ω`. The walk
producer `hWalk_pw_g_loc` is used at the exponent `e` (`K.ω := e`, `ωm := ω₀`), and its domain
`ball 0 (ρ - ε ^ e)` lies in `ball 0 (ρ - ε ^ ωG)` since `e ≤ ωG`. -/
theorem walkY_pt {γ ω₀ α ζ ρ CG CE C s₀ ε r ωG c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hω0 : 0 < ω₀) (hωe : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hGe : 2 / (2 + γ) ^ 2 - ζ ≤ ωG)
    (hε0 : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (hrε : 10 * ε ^ ω₀ ≤ r)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ) :
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ωG)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat))
                (sphere 0 ρ) := by
  have he0 : 0 < 2 / (2 + γ) ^ 2 - ζ := by linarith
  have hε1 : ε ≤ 1 := Lemma68CGResGreenWalk.eps_le_one_of_ten_rpow hω0 hrε hrρ hρ1
  have hle : ε ^ ωG ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hGe
  have hsub : ball (0 : ℂ) (ρ - ε ^ (2 / (2 + γ) ^ 2 - ζ)) ⊆ ball (0 : ℂ) (ρ - ε ^ ωG) :=
    Metric.ball_subset_ball (by linarith)
  have hW := Lemma68CGResWalkLoc.hWalk_pw_g_loc (ω₀ := ω₀) (ωm := ω₀) (C := C) (CG := CG) (α := α) (CE := CE)
    (s1 := shellS1CG γ CG) (c0W := c0W) S
    (shellKCG γ ρ (2 / (2 + γ) ^ 2 - ζ) ζ CG hγ0 hγ2 hρ0 hρ1 he0 hζ0 hζ1 hCG) ω i
    hρ0 hρ1 hζ0 hζ1 hr0 hrρ hrz hε0 hε1 hs₀ hreg hmesh hgapM hωe hrε
  intro hFA k hk
  filter_upwards [hW hFA k hk] with x hx hP
  obtain ⟨h1, h2, h3⟩ := hx hP
  exact ⟨cellVertices_mono_ball68 hsub h1, h2, h3⟩

/-- **`hGreen` on the walk ball at `kω`, Green exponent `ωG` (`greenG_pt`; no `hGe`).** The body of the split-leaf
binder `hGreen` (`B1GoodEnvSplit68.shellOneTest_at_of_goodEnv_loc_split`, the `hωG`-derived block), with `K.C = CG`
and the walk ball `ball 0 (ρ - ε ^ kω)`, `kω = K.ω`. The event `greenLowEvent68 S ωG ρ CG ε` has domain
`ball 0 (ρ - ε ^ ωG)` and range `ε ^ ωG ≤ r'`. From `kω ≤ ωG` and `0 < ε ≤ 1`, `ε ^ ωG ≤ ε ^ kω`, so
`ball 0 (ρ - ε ^ kω) ⊆ ball 0 (ρ - ε ^ ωG)` and `cellVertices` is monotone in its set. -/
theorem greenG_pt {ρ CG ε ωG kω : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hkω : kω ≤ ωG) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hG : ω ∈ MatedCRT.greenLowEvent68 S ωG ρ CG ε) :
    ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ kω)), ∀ r' : ℝ, ε ^ ωG ≤ r' →
      r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
      ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
        CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
            else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
          ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b := by
  have hle : ε ^ ωG ≤ ε ^ kω := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hkω
  have hball : ball (0 : ℂ) (ρ - ε ^ kω) ⊆ ball (0 : ℂ) (ρ - ε ^ ωG) :=
    Metric.ball_subset_ball (by linarith)
  intro a ha r' hr' hrinf b hb
  exact hG a (MatedCRT.cellVertices_mono_ball68 hball ha) r' hr' hrinf b hb

end Lemma68CGResGreenY
end MatedCRT

#print axioms MatedCRT.Lemma68CGResGreenY.shellEpsG68_pos
#print axioms MatedCRT.Lemma68CGResGreenY.le_one_of_le_shellEpsG68
#print axioms MatedCRT.Lemma68CGResGreenY.greenY_pt
#print axioms MatedCRT.Lemma68CGResGreenY.walkY_pt
#print axioms MatedCRT.Lemma68CGResGreenY.greenG_pt
