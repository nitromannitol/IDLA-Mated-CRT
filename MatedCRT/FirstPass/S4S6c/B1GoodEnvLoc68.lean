import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68
import MatedCRT.FirstPass.S4S6c.HoneCellGoodSelPw68
import MatedCRT.FirstPass.S4S6c.HVolFullPw68
import MatedCRT.FirstPass.S4S6c.StopFinPw68
import MatedCRT.FirstPass.S4S6c.HoneX1Loc68
import MatedCRT.FirstPass.S4S6c.CGResElSel68
import MatedCRT.FirstPass.S4S6c.ShellHdePw68

/-!
# `shellOneTest_at_of_goodEnv_loc_g2`: the `_g` leaf with the landed producers discharged (fp-S4S6c-goodenv-local, q4)

`shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean:1216) with the landed producers applied inside:
* `hmesh` (CellDiamLe on `ball 0 (rhoCell68 ρ)`) from the cell clause of `meshEventR` (`cellDiamLe_rhoCell_of_cellSize`);
* `hCellGood` from `hCellGood_fixedOmega_s1` (HoneCellGoodSelPw68), `hsel` from `hsel_fixedOmega_g` (needs `hKc0`, `hwin`, `hCCG`);
* `hRr` from `hRr_fixedOmega_loc_g` (HoneRrLocal68, at the radius `ball 0 ρ ⊆ ball 0 (rhoCell68 ρ)`), `hcap` from `hcap_of_continuous_g`;
* `hVolC` from `hVolC_pw_g` and `hVolY` from `hVolY_pw_g` (HVolFullPw68), the `hVolY` ball `ball 0 (1 - W/4)` included in `ball 0 (rhoCell68 ρ - W/4)`;
* no full support: the walk positivity `hpos` is `hpos_ae_narrow` (eligibility of the shell centres, the radius cap `4 R < t`, the cutoff `hcut`), so `hωFull` is dropped (chat 246 Q3 items 3-5).

Kept as named binders (inputs of the producers that have not landed): `hShellLoc` (z1), `hadm`, `hEl` (`hEl_fixedOmega_g`
needs the univ mesh, HoneElAe68.lean:247), `hstopFin` (z10), `hc` (74a, the exit-vertex centre bound of `hVolC_pw_g`),
`hGreen`, `hCountGood`, `hcutR` (z12), `hx1`, `hmomS` (q3), `hWalk`, and the volume cutoff `t`, `ht`, `hrt`, `hcut`.

This file imports the producers, which import `B1Assembly68` (so they cannot be imported there). `K.c0 = exp(-(2CG))/32`
(`shellKCG`, ShellConstants68.lean:74) gives `0 < K.c0 ≤ 1/4` by unfolding.
Terminology: Armstrong-Kuusi-Mourrat (shells, one-test bound), Armitage-Gardiner (exit times of balls).
-/

open HarmonicBalls (annulus)

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

/-- **The narrow walk positivity `hpos` (chat 246 Q3 step 4), without full support.** Path-level form of
`HoneGoodEventAe68.hpos_ae` (HoneGoodEventAe68.lean:174): the full-support binder `hfull` is replaced by the a.s.
eligibility of the shell centres (`hEl`) and the radius bound `R ≤ d ^ a`; the annulus infimum is positive by
`Lemma68Cutoff239.pos_iInf_annulus_of_eligible` (HVolCutoff239_68.lean:301), which needs only the cutoff below `t`
and `4 R < t`. Terminology: Armitage-Gardiner (annuli of potential theory), Armstrong-Kuusi-Mourrat (good annuli). -/
theorem hpos_ae_narrow {γ ρc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ}
    {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ} {ρ a t : ℝ}
    (hc0' : K.c0 ≤ 1 / 4) (hρ1 : ρ < 1)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ K.βm) ≤ μ (ball z δ))
    (hradCap : ∀ R : ℝ, 0 < R → R ≤ d ^ a → 4 * R < t)
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        shellCentre ε η Kset r s d k x ∈ shortEligible ρ d a)
    (hRf : ∀ z ∈ shortEligible ρ d a, Rf z ≤ d ^ a)
    (hr : 0 < r) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        0 < ⨅ w ∈ annulus (shellCentre ε η Kset r s d k x) (Rf (shellCentre ε η Kset r s d k x))
          (2 * Rf (shellCentre ε η Kset r s d k x)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k x))) := by
  intro k hk
  filter_upwards [hRr k hk, hEl k hk] with x hx hE hmem
  have hR : 0 < Rf (shellCentre ε η Kset r s d k x) := lt_of_lt_of_le (by positivity) (hx hmem).1
  have hRs : Rf (shellCentre ε η Kset r s d k x) ≤ d ^ a := hRf _ (hE hmem)
  exact Lemma68Cutoff239.pos_iInf_annulus_of_eligible K.hc0 hc0' hρ1 (hE hmem) hR hRs
    (by linarith [hradCap _ hR hRs]) hcut

open Classical in
/-- **`shellOneTest_at_of_goodEnv_loc_g` with the narrow walk positivity (no full support).** The copy of
`shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean:1216) in which the full-support binder `hfull` is
replaced by the cutoff data `t`, `ht`, `hrt`, `hcut` and `hc0'`; the walk positivity `hpos` is `hpos_ae_narrow`
(the radius cap `hradCap` comes from `four_mul_lt_of_radius_cap`). Otherwise the proof is the same. -/
theorem shellOneTest_at_of_goodEnv_loc_gN {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (c0W : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (_hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (_hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
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
    -- the exit mesh on the cell-size event of `meshEventR` (radius `rhoCell68 ρ = (1 + ρ)/2`, chat 252)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    -- named localized producer (z1 ShellOrderLoc68 pointwise form; z8 ShellPathLoc68), at `hmesh`
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
    (hRr : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          r ^ 2 ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hcap : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    (hVolC : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ENNReal.ofReal ((K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
              (K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ∀ y ∈ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal (((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
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
    (hCellGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
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
    -- the walk second conjunct at the split exponent κ = 2/(2+γ)^2 - ζ (q1 `_split` leaf; not `K.ω`)
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
    (hsel : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z) z)
    (t : ℝ) (ht : 0 < t)
    (hrt : r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ K.βm) ≤ S.μ ω (ball z δ))
    (hc0' : K.c0 ≤ 1 / 4) :
    ∃ Rf : ℂ → ℝ,
      ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
        (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  obtain ⟨-, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, -⟩ := hreg
  have hr1 : r ≤ 1 := by linarith
  have hd0 : 0 < dyadicD r := lt_of_lt_of_le (pow_pos hr0 2) (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd1 : dyadicD r ≤ 1 := by
    have h4 : r ≤ 1 / 4 := by linarith
    have h5 : r ^ 2 ≤ 1 / 16 := by nlinarith
    linarith [(Lemma68ChainGlue.dyadicD_mem hr0 hr1).2]
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hC0 : 0 < shellChone68 CE CG := lt_of_lt_of_le one_pos (one_le_shellChone68 CE CG)
  have hρm0 : 0 < Lemma68HoneCellGood.rhoCell68 ρ := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hρm1 : Lemma68HoneCellGood.rhoCell68 ρ < 1 := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hKs1 : K.s1 = shellS1CG γ CG := by subst hK; rfl
  have hKβ : K.βm = (2 + γ) ^ 2 / 2 + 1 := by subst hK; rfl
  have hKω : K.ω = ω₀ := by subst hK; rfl
  have hs1 : 0 < K.s1 := by rw [hKs1]; exact shellS1CG_pos γ CG
  have hβ1 : 1 ≤ K.βm := by rw [hKβ]; have := sq_nonneg (2 + γ); linarith
  have hω1 : 0 ≤ K.ω := by rw [hKω]; exact hω0.le
  have hα2 : 2 * K.ω ≤ α := le_trans (le_mul_of_one_le_right (by linarith) hβ1) hα.le
  have hαm : 2 * K.ω * K.βm ≤ α := hα.le

  have hTend := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hmω := hmult ε hε
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hd0 hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd0 _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hd0 hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hRw : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
        dyadicD r ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) := fun k hk =>
    (hEl hadm k hk).mono fun x hx hxm =>
      (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1
  -- the walk bound `hb` at `ω`: the localized copy of `hb_ae_of_walk` (WalkLoc68, z12), on the mesh `hmesh`;
  -- its gap `dyadicD r / 100 ≤ rhoCell68 ρ - ρ` follows from `dyadicD r / 100 ≤ dyadicD r ^ shortExp ζ` and `hcutR`
  have hbω := Lemma68WalkLoc.hb_ae_of_walk_loc (ρ := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (r := r)
    (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω))
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    hcont hε (fillCells ε (S.η ω) ↑i.Θ) (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hdeg hadj (fun _ _ => rfl) hd0 ⟨0, hadm.1.2.2 (mem_ball_self hs₀)⟩ (subset_closure.trans hadm.1.2.1)
    hr0 hrρ hspos.le hNs (by linarith [hds, hcutR, hd0]) hmesh (fun k hk => hRw k hk)
  have hShell := hShellLoc hmesh hadm
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω hz).2
  have hRr' := hRr hadm
  have hr1 : r ≤ 1 := by linarith
  have hradCap : ∀ R : ℝ, 0 < R → R ≤ dyadicD r ^ shortExp ζ → 4 * R < t := fun R _ hRd =>
    Lemma68Cutoff239.four_mul_lt_of_radius_cap (a := shortExp ζ) rfl hζ0 ht hr0 hd0 (dyadicD_lt_two_mul_sq hr0 hr1) hRd hrt
  have hpos := hpos_ae_narrow K hc0' hρ1 hcut hradCap hRr' (hEl hadm) hRf hr0
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (hsel := hsel hadm) (hEl := hEl hadm)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hZ := fun _ _ => rfl)
  have hεα := Lemma68HoneGoodEventAe.hεα_ae K hε hε1 hα2 hrε hRr'
  have hεmass := Lemma68HoneGoodEventAe.hεmass_ae K hε hε1 hαm hrε hRr'
  have hsc := Lemma68HoneGoodEventAe.hsc_ae_threshold K (μ := S.μ ω) hε hrε hα hεs hRr' (hVolC hadm)
  have hdbl : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
        (S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
          (3 * K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal
          ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 CG * (S.μ ω (ball (vertexPoint ε (S.η ω) (x
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
            (K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal := fun k hk => by
    filter_upwards [hbω k hk, hWalk hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
    intro hxm
    exact Lemma68HoneExitGeom.hdbl_of_exit_geom_path_split K hcont hε (μ := S.μ ω)
      (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) (C_good := CG) (hr := hr0) k x
      (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
      (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCellGood hadm) hεcell
      (hgx hxm) (hbx hxm)
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by
      obtain ⟨-, hAd⟩ := hadm
      obtain ⟨-, -, hcl⟩ := hAd
      rw [hKs1, hKβ]; exact hcl) (hcap hadm)
  refine ⟨(windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω), ?_, hShell⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_split
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) hρm0 hρm1 (K := K) (ε := ε) (η := S.η ω) (hη := hcont)
    (hprop := hTend) (hε := hε) (hεc := hεc) (μ := S.μ ω) (hμNull := hμN) (m := S.mult ε ω) (a := i.a)
    (A := (↑i.A : Set ℤ)) (hA := i.A.finite_toSet.measurableSet)
    (n := shellCount r (dyadicD r ^ shortExp ζ) - 1) (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) (r := r) (s := dyadicD r ^ shortExp ζ)
    (d := dyadicD r) (q0 := q0) (α := α) (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG)
    (N_cov := shellNcov68) (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0)
    (hCw := shellChone68_hCw CE CG) (hCg := hCG.le) (hlf := hmω.1) (hcons := hmω.2)
    (hstopFin := hstopFin hadm)
    (hRbd := fun k _ => by
      obtain ⟨t, ht⟩ := Lemma68WindowRfGlobal.windowRfT_hRbd_global S.μ ρ (shortExp ζ) c0W C (dyadicD r)
        hd0 hd1 ha1 ω ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k
      exact ⟨t, Filter.Eventually.of_forall fun x hx => ht x hx⟩)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k hk => (hRr' k hk).mono fun x hx hxm => mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le)
    (hVolC := hVolC hadm) (hVolY := hVolY hadm) (hGreen := hGreen hadm) (hWalk := hWalk hadm)
    (hCountGood := hCountGood hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCellGood hadm) (hd := hd0) (aW := shortExp ζ) (hRf := hRf) (hEl := hEl hadm)
    (hcut := hcutR) (hκ2 := hκ2) (hεcell := hεcell) (hsc := hsc) (hεα := hεα) (hεmass := hεmass)
    (hb := hbω) (hx1 := hx1 hadm) (hmomS := hmomS hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos) (hdbl := hdbl)

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_g

/-- **`shellOneTest_at_of_goodEnv_loc_g` with the landed producers discharged (fp-S4S6c-goodenv-local, q4).**
Same conclusion as `shellOneTest_at_of_goodEnv_loc_g`, with no full-support binder (`hωFull` is dropped: the walk
positivity is `hpos_ae_narrow`, from the eligibility of the shell centres and the cutoff). Discharged here: `hmesh`
(from the mesh event `hωR : ω ∈ meshEventR …` at radius `rhoCell68 ρ`), `hRr` (`hRr_fixedOmega_loc_g`), `hcap`,
`hsel` (`hsel_fixedOmega_g`; premises `hKc0`, `hwin`, `hCCG`), `hCellGood`, `hVolC`, `hVolY` (`hVolC_pw_g`,
`hVolY_pw_g`), `hEl` (`CGResElSel68.hEl_fixedOmega_ball`), `hstopFin` (`hstopFin_pw_g`, with `htend` from
`Lemma68Geometry.tendsto_cocompact_of_escapes`), `hx1` (`hx1_fixedOmega_loc_s1_g` at `ρmom = ρmesh = rhoCell68 ρ`),
and `hShellLoc` (`ShellOrderPw68.hShellLoc_pw_g`, with `hkill` from `WalkBridge68.srw_killed_top_null`, `hstart` from
`HoneRrLocal68.hstart_of_fullAdmAt_s1`, `hde` from `ShellHdePw68.shellHde_pw68_s1` and `hTest`).
Named binders: `hωR`, `hadm`, `hTest` (a.s. finiteness of the test end, the input of `ShellCGTestEndLoc`), `hmomS` (needs
`exitTimeEvent68 S α (rhoCell68 ρ) CE ε`, which `meshEventR` does not contain), the cutoff `t`, `ht`, `hrt`, `hcut`,
`hc` (74a), `hGreen` (κ-form), `hCountGood`, `hcutR`, `hWalk` (κ-form), `hKc0`, `hwin`, `hCCG`. -/
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
    (hadm : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (hTest : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x ≠ ⊤)
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
    (hCCG : C ≤ CG) :
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
  have hd0 : 0 < dyadicD r := lt_of_lt_of_le (pow_pos hr0 2) (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd1 : dyadicD r ≤ 1 := by
    have h4 : r ≤ 1 / 4 := by linarith
    have h5 : r ^ 2 ≤ 1 / 16 := by nlinarith
    linarith [(Lemma68ChainGlue.dyadicD_mem hr0 hr1).2]
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
  have hgapMesh : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by linarith [hds, hcutR, hd0]
  have hElPw := Lemma68CGResElSel.hEl_fixedOmega_ball (γ := γ) (ρ := ρ) (s1 := shellS1CG γ CG) (c0W := c0W)
    (ζ := ζ) (C := C) (s₀ := s₀) (ε := ε) (r := r) (q0 := q0) (CE := CE) (CG := CG) S
    hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω hmesh hgapMesh hηω hreg'.2.1 hreg'.2.2.2.2.2.2.2.1
    (hreg'.2.2.1 ε hε)
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
    (t := t) (s1 := shellS1CG γ CG) (c0W := c0W) S K ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut hRr hElPw hc
  have hVolY := Lemma68HVolFullPw.hVolY_pw_g (γ := γ) (ρ := ρ) (ζ := ζ) (C := C) (s₀ := s₀) (ε := ε) (r := r)
    (t := t) (s1 := shellS1CG γ CG) (c0W := c0W) S K ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut hElPw hRr
  have hloc : IsLocallyFiniteMult (S.mult ε ω) := (hreg'.2.2.1 ε hε).1
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := (hreg'.2.2.1 ε hε).2
  have hkillW : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ :=
    ae_iff.2 (by simpa using Lemma68WalkBridge.srw_killed_top_null hloc hcons i.a ε (S.η ω) i.Θ i.F0 r)
  have hstartW : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    fun hFA => Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1 (γ := γ) (ρ := ρ) (s₀ := s₀) (ε := ε)
      (s1 := shellS1CG γ CG) S hε hs₀ ω hηω r hr0 i hFA
  have hmesh0 : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    Lemma68ShellOrderPw.cellDiamLe_mono_set hball hmesh
  have hShellDeW := Lemma68ShellHdePw68.shellHde_pw68_s1 (γ := γ) (shellS1CG γ CG) S hε hs₀ hζ0 hζ1 hr0 hrz hrρ i
    (ω := ω) (Rf := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
    (Elig := fun w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ))
    hηω (hreg'.2.2.2.2.2.2.2.2 ε hε) hkillW
    (fun w hw => windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω hw)
    (fun w hw => hw) hmesh0 hstartW
  have hShellLocPw := Lemma68ShellOrderPw.hShellLoc_pw_g (γ := γ) (shellS1CG γ CG) S ω c0W C
    (ε := ε) (ρ := ρ) (s₀ := s₀) (ζ := ζ) (r := r) hε hs₀ hζ0 hζ1 hr0 hrz hrρ i hgapMesh hηω
    (hreg'.2.2.2.2.2.2.2.2 ε hε) hreg'.2.2.2.2.2.2.1 hkillW hstartW (fun hFA => by filter_upwards [hShellDeW hFA, hTest hFA] with x hx hT; exact ⟨fun k hk => ⟨hx.1 k hk, hT k hk⟩, hx.2⟩)
  have htend : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hreg'.2.1
  have hstopFinPw := Lemma68StopFinPw.hstopFin_pw_g (γ := γ) (ρ := ρ) (s₀ := s₀) (ε := ε)
    (s1 := shellS1CG γ CG) (r := r) (ζ := ζ) (C := C) (c0W := c0W) S ω i hε hs₀ htend
    (hreg'.2.2.1 ε hε).1 hreg'.2.2.2.2.2.2.1
  have hx1Pw := HoneX1Loc68.hx1_fixedOmega_loc_s1_g (γ := γ) (ω₀ := ω₀) (ρ := ρ) (CG := CG) (ζ := ζ)
    (α := α) (CE := CE) (C := C) (ε := ε) (s₀ := s₀) (r := r) (ρmom := Lemma68HoneCellGood.rhoCell68 ρ)
    (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (s1 := shellS1CG γ CG) (c0W := c0W) S hreg hρ1 hζ0 hζ1
    hε hs₀ hr0 hrρ hrz (by unfold Lemma68HoneCellGood.rhoCell68; linarith)
    (by linarith [hds, hcutR, hd0]) hmesh i
  exact shellOneTest_at_of_goodEnv_loc_gN hγ0 hγ2 c0W S hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0c hε hs₀ hr0 hrρ hrz hRA
    ω₀ hω0 K hK ω hreg i hεc hεcell hκ2 hα hεs hrε hε1 hmesh hShellLocPw hadm hElPw hstopFinPw hRr hcap
    (fun hA k hk => (hVolC hA k hk))
    (fun hA k hk => (hVolY hA k hk).mono fun x hx hxl y hy =>
      hx hxl y (Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith) hy))
    hGreen hCountGood hCellGood hcutR hx1Pw hmomS hWalk hsel t ht hrt hcut hc0'

#print axioms MatedCRT.Lemma68B1Assembly.hpos_ae_narrow
#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_gN
#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_g2

end Lemma68B1Assembly
end MatedCRT
