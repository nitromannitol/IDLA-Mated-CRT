import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68
import MatedCRT.FirstPass.S4S6c.HoneCellGoodSelPw68
import MatedCRT.FirstPass.S4S6c.HVolFullPw68

/-!
# `shellOneTest_at_of_goodEnv_loc_g2`: the `_g` leaf with the landed producers discharged (fp-S4S6c-goodenv-local, q4)

`shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean:1216) with the landed producers applied inside:
* `hmesh` (CellDiamLe on `ball 0 (rhoCell68 ρ)`) from the cell clause of `meshEventR` (`cellDiamLe_rhoCell_of_cellSize`);
* `hCellGood` from `hCellGood_fixedOmega_s1` (HoneCellGoodSelPw68), `hsel` from `hsel_fixedOmega_g` (needs `hKc0`, `hwin`, `hCCG`);
* `hRr` from `hRr_fixedOmega_loc_g` (HoneRrLocal68, at the radius `ball 0 ρ ⊆ ball 0 (rhoCell68 ρ)`), `hcap` from `hcap_of_continuous_g`;
* `hVolC` from `hVolC_pw_g` and `hVolY` from `hVolY_pw_g` (HVolFullPw68), the `hVolY` ball `ball 0 (1 - W/4)` included in `ball 0 (rhoCell68 ρ - W/4)`;
* `hfull` from the full-support binder `hωFull` (the guard `FullAdmAt` is ignored, as in `hfull_pw`).

Kept as named binders (inputs of the producers that have not landed): `hShellLoc` (z1), `hadm`, `hEl` (`hEl_fixedOmega_g`
needs the univ mesh, HoneElAe68.lean:247), `hstopFin` (z10), `hc` (74a, the exit-vertex centre bound of `hVolC_pw_g`),
`hGreen`, `hCountGood`, `hcutR` (z12), `hx1`, `hmomS` (q3), `hWalk`, and the volume cutoff `t`, `ht`, `hrt`, `hcut`.

This file imports the producers, which import `B1Assembly68` (so they cannot be imported there). `K.c0 = exp(-(2CG))/32`
(`shellKCG`, ShellConstants68.lean:74) gives `0 < K.c0 ≤ 1/4` by unfolding.
Terminology: Armstrong-Kuusi-Mourrat (shells, one-test bound), Armitage-Gardiner (exit times of balls).
-/

namespace MatedCRT
namespace Lemma68B1Assembly

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- **The cell-diameter mesh at `rhoCell68 ρ` from the cell-size event (fp-S4S6c-goodenv-local, q4).** On the event
`cellSizeEvent68 … (rhoCell68 ρ) ε`, a cell meeting `ball 0 (rhoCell68 ρ)` has diameter at most `ε ^ κ`, and
`ε ^ κ ≤ c₀ r² / 100 ≤ dyadicD r / 100` (`hεcell`, `c₀ ≤ 1`, `r² ≤ dyadicD r`). This is the argument of
`cellDiamLe_ball_of_meshEvent` (HoneSetupAdapt68.lean:78) with `ball 0 ρ` replaced by `ball 0 (rhoCell68 ρ)`. -/
theorem cellDiamLe_rhoCell_of_cellSize {γ ζ ρ ε c0 r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (hω : ω ∈ cellSizeEvent68 S γ ζ (Lemma68HoneCellGood.rhoCell68 ρ) ε)
    (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1) (hc0 : c0 ≤ 1)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ c0 * r ^ 2 / 100) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) := by
  have hcell : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := hω
  have hbdd : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
      Bornology.IsBounded (cell ε (S.η ω) k) := by
    intro k hk
    by_contra hnb
    have hlow := (hcell k hk).1
    rw [diam_eq_zero_of_unbounded hnb] at hlow
    exact absurd hlow (not_le.mpr (Real.rpow_pos_of_pos hε _))
  have hbound : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ dyadicD r / 100 := by
    have hsq : r ^ 2 ≤ dyadicD r := sq_le_dyadicD hr hr1
    have hc : c0 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (sq_nonneg r) hc0
    linarith
  intro k hk p hp q hq
  calc dist p q ≤ diam (cell ε (S.η ω) k) := Metric.dist_le_diam_of_mem (hbdd k hk) hp hq
    _ ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := (hcell k hk).2
    _ ≤ dyadicD r / 100 := hbound

/-- **`shellOneTest_at_of_goodEnv_loc_g` with the landed producers discharged (fp-S4S6c-goodenv-local, q4).**
Same conclusion as `shellOneTest_at_of_goodEnv_loc_g`. Binders: the mesh event `hωR : ω ∈ meshEventR …` (radius
`rhoCell68 ρ`) replaces `hmesh`; `hKc0`, `hwin`, `hCCG` are the premises of `hsel_fixedOmega_g`; `hωFull` is the
full-support statement at `ω` (HVolFullPw68.hfull_pw without its guard); `t`, `ht`, `hrt`, `hcut` are the cutoff of
`hVolC_pw_g`; `hc` is the (74a) exit-vertex centre bound of `hVolC_pw_g`. -/
theorem shellOneTest_at_of_goodEnv_loc_g2 {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (c0W : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the mesh event `meshEventR` (its cell clause is at radius `rhoCell68 ρ = (1 + ρ)/2`, chat 252)
    (hωR : ω ∈ Lemma68Guard10.meshEventR S γ ω₀ ρ CG ζ α CE ε)
    -- named localized producer (z1 ShellOrderLoc68 pointwise form), at the mesh `CellDiamLe … (ball 0 (rhoCell68 ρ))`
    (hShellLoc : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) →
      Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a)
    (hadm : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (hEl : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hstopFin : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
        ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x < ⊤ →
            x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat ∈ F)
    -- the volume cutoff `t` and the volume bound at `ω` (inputs of `hVolC_pw_g`, `hVolY_pw_g`)
    (t : ℝ) (ht : 0 < t)
    (hrt : r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ K.βm) ≤ S.μ ω (ball z δ))
    -- (74a) the exit-vertex centre bound of `hVolC_pw_g` (named)
    (hc : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat)‖ <
            1 - windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hGreen : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hcutR : dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hx1 : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat)‖
            < Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ) →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hWalk : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat)) (sphere 0 ρ))
    -- the window constant is the cutoff of the window `K.c0` (used by `hsel_fixedOmega_g`)
    (hKc0 : K.c0 = c0W)
    (hwin : ω ∉ Lemma68ShellChain.badWindowOf S.μ ρ (shortExp ζ) c0W C (dyadicD r))
    (hCCG : C ≤ CG)
    -- the full support at `ω` (HVolFullPw68.hfull_pw, guard removed)
    (hωFull : ∀ (w : ℂ) (τ : ℝ), 0 < τ → 0 < S.μ ω (ball w τ)) :
    ∃ Rf : ℂ → ℝ,
      ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
        (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hreg' := hreg
  unfold RegularEnvAt68 at hreg'
  have hωS : ω ∈ cellSizeEvent68 S γ ζ (Lemma68HoneCellGood.rhoCell68 ρ) ε := by
    have h := hωR
    unfold Lemma68Guard10.meshEventR at h
    exact h.1.2
  have hr1 : r ≤ 1 := by linarith
  have hc0 : 0 < K.c0 := by
    rw [hK]
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hc0' : K.c0 ≤ 1 / 4 := by
    have h1 : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [hK]
    show Real.exp (-(2 * CG)) / 32 ≤ 1 / 4
    linarith
  have hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) :=
    cellDiamLe_rhoCell_of_cellSize S ω hωS hε hr0 hr1 (by linarith) hεcell
  have hηω : Continuous (S.η ω) := hreg'.2.2.2.1
  have hball : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ) :=
    Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith)
  have hRr := Lemma68HoneRrLocal.hRr_fixedOmega_loc_g (γ := γ) (ρ := ρ) (s1 := shellS1CG γ CG)
    (c0W := c0W) (C := C) S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω
    (Lemma68HoneRrLocal.cellDiamLe_mono_set hball hmesh) hηω
    (Lemma68Geometry.tendsto_cocompact_of_escapes hreg'.2.1)
    (fun j k h => hreg'.2.2.2.2.2.2.2.2 ε hε j k h) (hreg'.2.2.1 ε hε)
  have hcap := Lemma68HoneSetupAdapt.hcap_of_continuous_g (γ := γ) (ρ := ρ) (s₀ := s₀) (ε := ε) (r := r)
    (s1 := shellS1CG γ CG) S ω hηω hε hr0 i
  have hsel := Lemma68HoneCellGoodSelPw.hsel_fixedOmega_g (γ := γ) (ρ := ρ) (ζ := ζ) (C := C) (r := r)
    (CG := CG) (s₀ := s₀) (ε := ε) (s1 := shellS1CG γ CG) (c0W := c0W) S K hKc0 ω i hwin hCCG
  have hCellGood := Lemma68HoneCellGoodSelPw.hCellGood_fixedOmega_s1 (s₀ := s₀) (r := r)
    (s1 := shellS1CG γ CG) S ω i hωR
  have hVolC := Lemma68HVolFullPw.hVolC_pw_g (γ := γ) (ρ := ρ) (ζ := ζ) (C := C) (s₀ := s₀) (ε := ε) (r := r)
    (t := t) (s1 := shellS1CG γ CG) (c0W := c0W) S K ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut hRr hEl hc
  have hVolY := Lemma68HVolFullPw.hVolY_pw_g (γ := γ) (ρ := ρ) (ζ := ζ) (C := C) (s₀ := s₀) (ε := ε) (r := r)
    (t := t) (s1 := shellS1CG γ CG) (c0W := c0W) S K ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut hEl hRr
  exact shellOneTest_at_of_goodEnv_loc_g hγ0 hγ2 c0W S hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0c hε hs₀ hr0 hrρ hrz hRA
    ω₀ hω0 K hK ω hreg i hεc hεcell hκ2 hα hεs hrε hε1 hmesh hShellLoc hadm hEl hstopFin hRr hcap
    (fun hA k hk => (hVolC hA k hk))
    (fun hA k hk => (hVolY hA k hk).mono fun x hx hxl y hy =>
      hx hxl y (Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith) hy))
    hGreen hCountGood hCellGood hcutR hx1 hmomS hWalk hsel (fun _ => hωFull)

end Lemma68B1Assembly
end MatedCRT
