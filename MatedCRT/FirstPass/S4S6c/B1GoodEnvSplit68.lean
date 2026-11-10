import MatedCRT.FirstPass.S4S6c.B1GoodEnvLoc68
import MatedCRT.FirstPass.S4S6c.HoneLeafGexp68
import MatedCRT.FirstPass.S4S6c.HoneMomSPw68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.HoneCellGoodSelPw68

/-!
# `shellOneTest_at_of_goodEnv_loc_split`: the split-constant one-test leaf, free Green exponent (fp-S4S6c-goodenv-split, q4)

Codex Q4 (notes/fp-gaps/CODEX-idla-hOne-residuals-sol-20261110.md l.257-347): the good-annulus constant of the
selector is the prevalence witness `C`, not `CG`; the Green constant `K.C = CG` and `K.c0 = shellC0 CG` are kept.
Changes from `shellOneTest_at_of_goodEnv_loc_g2` (B1GoodEnvLoc68.lean:360):

* no `hCCG`: the selector is `IsGoodAnnulusEvent (S.μ ω) K.c0 C (windowRfT … C …) z`, from
  `hsel_fixedOmega_g (CG := C) … le_rfl`;
* `C_good := C` in `hgood_ae`, in `hdbl_of_exit_geom_path_gexp` and in the leaf
  `Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_gexp` (`C_exit := CE`, `C := shellChone68 CE C`);
  `hq0c` and `hC : 0 < C` are stated in `C`;
* the Green range and the walk second conjunct use a free real exponent `ωG` (`2 * ω₀ < ωG`, operator 75a), passed as
  `ωg` of the leaf; the walk first conjunct keeps `ε ^ K.ω`; the cell-size and `hεcell` exponents keep `κ = 2/(2+γ)²-ζ`;
* `hmomS` is derived from the exit membership `hωX : ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε`
  (`HoneMomSPw68.hmomS_pointwise_rhoMom_s1_g`);
* the radius cap `t`, `ht`, `hrt`, `hcut` stays an explicit argument.

`hdbl_of_exit_geom_path_gexp` (below) is the copy of `hdbl_of_exit_geom_path_split` (HoneExitGeom68.lean:556) with the
walk second conjunct at `ωG`; its proof uses only the first conjunct of the walk, so the copy is verbatim otherwise.
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

/-- **The one-test doubling bound, split exponent with a free walk exponent `ωG` (fp-S4S6c-goodenv-split, q4).**
Copy of `hdbl_of_exit_geom_path_split` (HoneExitGeom68.lean:556); the walk second conjunct is `ε ^ ωG ≤ R/8`. -/
theorem hdbl_of_exit_geom_path_gexp {γ ρc ζc ωG : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {C_good : ℝ} (hr : 0 < r) (k : ℕ) (ω : ℕ → ℤ) (ρ' : ℝ) (hρ' : ρc ≤ ρ')
    (hRr_x : r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (rmin : ℝ)
    (hRmin_x : rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hWalk_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
      ε ^ ωG ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
      Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
        infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ').Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hgood_x : IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hb_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
      cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3))) :
    (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
        (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  have hR0 : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (pow_pos hr 2) hRr_x.1
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  have hWv : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc - ε ^ K.ω)).Nonempty := hWalk_x.1
  have hmeet : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) ρ').Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hWv
    exact ⟨p, hp1, ball_subset_ball (by linarith) hp2⟩
  have hdiam : diam (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h1 := hCellGood _ hmeet
    have h2 := hRmin_x
    linarith
  obtain ⟨p, hpc, hps⟩ : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)).Nonempty := hb_x
  have hdist_p : dist p (Z k ω) = 4 * Rf (shellCentre ε η Kset r s d k ω) / 3 := mem_sphere.1 hps
  have hx : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) :=
    MatedCRT.Lemma68C12Geom.vertexPoint_mem_cell hε.le _
  have hbdd : Bornology.IsBounded (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) :=
    (MatedCRT.Lemma68C12Geom.cell_isCompact hη _).isBounded
  have hxp : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 :=
    (dist_le_diam_of_mem hbdd hx hpc).trans hdiam
  have habs : |dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) -
      4 * Rf (shellCentre ε η Kset r s d k ω) / 3| ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h := abs_dist_sub_le (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p (Z k ω)
    rw [hdist_p] at h
    exact h.trans hxp
  obtain ⟨hl, hu⟩ := abs_le.1 habs
  have ht : K.c0 * Rf (shellCentre ε η Kset r s d k ω) ≤ Rf (shellCentre ε η Kset r s d k ω) / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR0.le
    linarith
  have ht0 : 0 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := mul_nonneg K.hc0.le hR0.le
  have hx_ann : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    show _ ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hsub : ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ⊆
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    intro w hw
    rw [mem_ball] at hw
    have h3 : 3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω) =
        3 * (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) := by ring
    have h1 := dist_triangle w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω)
    have h2 : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) ≤
        dist w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) + dist w (Z k ω) := by
      have := dist_triangle (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w (Z k ω)
      rwa [dist_comm (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w] at this
    show w ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hD0 : 0 ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good := by
    unfold MatedCRT.Lemma68ConstOrder.shellDbl68
    exact le_trans zero_le_one (le_max_left _ _)
  have hm := MatedCRT.Lemma68ShellDbl.measure_three_le_shellDbl68 K.hc0
    (by linarith [K.hc0']) hR0 (hgood_x) hx_ann hsub
  have hfin : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  calc (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ (ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C_good) *
          μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hm
    _ = MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
          (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0]



/-- **`shellOneTest_at_of_goodEnv_loc_split` (fp-S4S6c-goodenv-split, q4).** The one-test leaf for the CG route with the
good-annulus constant `C` split from the Green constant `CG` (Codex Q4). Named inputs (producers not landed):
`hTest` (test-end finiteness, `ShellCGTestEndLoc`), `hc` (74a), `hGreen`, `hWalk` (free exponent `ωG`), `hCountGood`,
`hcutR`, and the radius cap `t ht hrt hcut`. The exit membership `hωX` replaces the moment premise `hmomS`. -/
theorem shellOneTest_at_of_goodEnv_loc_split {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (c0W : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG) (hC : 0 < C)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C))
    -- the second numerical bound on `q0` (Green constant `CG`; the split pointwise producer gives both, CGRCYCore68.lean:192)
    (hq0cG : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀) (ωG : ℝ) (_hωG : 2 * ω₀ < ωG)
    (K : Constants68 γ ρ) (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the mesh event `meshEventR` (cell clause at radius `rhoCell68 ρ = (1 + ρ)/2`)
    (hωR : ω ∈ Lemma68Guard10.meshEventR S γ ω₀ ρ CG ζ α CE ε)
    -- the exit membership at the cell radius (the premise of `hmomS_pointwise_rhoMom_s1_g`)
    (hωX : ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε)
    (hadm : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (hTest : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x ≠ ⊤)
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
    -- the Green range at the free exponent `ωG` (the leaf's `hGreen` with `ωg := ωG`)
    (hGreen : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ ωG ≤ r' →
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
    -- the walk bound at the free exponent `ωG` (second conjunct), first conjunct at `K.ω`
    (hWalk : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ ωG ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat)) (sphere 0 ρ))
    (hKc0 : K.c0 = c0W)
    (hwin : ω ∉ Lemma68ShellChain.badWindowOf S.μ ρ (shortExp ζ) c0W C (dyadicD r)) :
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
    hρ1 hζ0 hζ1 hq0 hq0cG hs₀ hε hr0 hrρ hRA i ω hmesh hgapMesh hηω hreg'.2.1 hreg'.2.2.2.2.2.2.2.1
    (hreg'.2.2.1 ε hε)
  have hRr := Lemma68HoneRrLocal.hRr_fixedOmega_loc_g (γ := γ) (ρ := ρ) (s1 := shellS1CG γ CG)
    (c0W := c0W) (C := C) S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω
    (Lemma68HoneRrLocal.cellDiamLe_mono_set hball hmesh) hηω
    (Lemma68Geometry.tendsto_cocompact_of_escapes hreg'.2.1)
    (fun j k h => hreg'.2.2.2.2.2.2.2.2 ε hε j k h) (hreg'.2.2.1 ε hε)
  have hcap := Lemma68HoneSetupAdapt.hcap_of_continuous_g (γ := γ) (ρ := ρ) (s₀ := s₀) (ε := ε) (r := r)
    (s1 := shellS1CG γ CG) S ω hηω hε hr0 i
  -- the good-annulus constant is `C` (no `C ≤ CG`): `hsel_fixedOmega_g` with its target constant `CG := C`
  have hsel := Lemma68HoneCellGoodSelPw.hsel_fixedOmega_g (γ := γ) (ρ := ρ) (ζ := ζ) (C := C) (r := r)
    (CG := C) (s₀ := s₀) (ε := ε) (s1 := shellS1CG γ CG) (c0W := c0W) S K hKc0 ω i hwin le_rfl
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
    (hreg'.2.2.2.2.2.2.2.2 ε hε) hreg'.2.2.2.2.2.2.1 hkillW hstartW
    (fun hFA => by filter_upwards [hShellDeW hFA, hTest hFA] with x hx hT; exact ⟨fun k hk => ⟨hx.1 k hk, hT k hk⟩, hx.2⟩)
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
  -- the moment premise from the exit membership at the cell radius (q3, `hmomS_pointwise_rhoMom_s1_g`)
  have hmomS := MatedCRT.HoneMomSPw68.hmomS_pointwise_rhoMom_s1_g (γ := γ) (ρ := ρ) (s₀ := s₀) (α := α)
    (CE := CE) (ε := ε) (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) (C := C) (ζ := ζ) (r := r)
    (s1 := shellS1CG γ CG) (c0W := c0W) S hωX i
  -- the walk-positivity and the Green-scale inputs of the leaf: the gN body with `C` in place of `CG`
  obtain ⟨-, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, -⟩ := hreg
  have hC0 : 0 < shellChone68 CE C := lt_of_lt_of_le one_pos (one_le_shellChone68 CE C)
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
    (hElPw hadm k hk).mono fun x hx hxm =>
      (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1
  have hbω := Lemma68WalkLoc.hb_ae_of_walk_loc (ρ := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (r := r)
    (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω))
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    hcont hε (fillCells ε (S.η ω) ↑i.Θ) (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hdeg hadj (fun _ _ => rfl) hd0 ⟨0, hadm.1.2.2 (mem_ball_self hs₀)⟩ (subset_closure.trans hadm.1.2.1)
    hr0 hrρ hspos.le hNs (by linarith [hds, hcutR, hd0]) hmesh (fun k hk => hRw k hk)
  have hShell := hShellLocPw hmesh hadm
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω hz).2
  have hRr' := hRr hadm
  have hradCap : ∀ R : ℝ, 0 < R → R ≤ dyadicD r ^ shortExp ζ → 4 * R < t := fun R _ hRd =>
    Lemma68Cutoff239.four_mul_lt_of_radius_cap (a := shortExp ζ) rfl hζ0 ht hr0 hd0 (dyadicD_lt_two_mul_sq hr0 hr1) hRd hrt
  have hpos := hpos_ae_narrow K hc0' hρ1 hcut hradCap hRr' (hElPw hadm) hRf hr0
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (C_good := C) (hsel := hsel hadm) (hEl := hElPw hadm)
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
          ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C * (S.μ ω (ball (vertexPoint ε (S.η ω) (x
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
            (K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal := fun k hk => by
    filter_upwards [hbω k hk, hWalk hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
    intro hxm
    exact hdbl_of_exit_geom_path_gexp K hcont hε (μ := S.μ ω)
      (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω))
      (C_good := C) (hr := hr0) (ωG := ωG) k x
      (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
      (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCellGood hadm) hεcell
      (hgx hxm) (hbx hxm)
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by
      obtain ⟨-, hAd⟩ := hadm
      obtain ⟨-, -, hcl⟩ := hAd
      rw [hKs1, hKβ]; exact hcl) (hcap hadm)
  refine ⟨(windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω), ?_, hShell⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_gexp
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) hρm0 hρm1 (K := K) (ε := ε) (η := S.η ω) (hη := hcont)
    (hprop := hTend) (hε := hε) (hεc := hεc) (μ := S.μ ω) (hμNull := hμN) (m := S.mult ε ω) (a := i.a)
    (A := (↑i.A : Set ℤ)) (hA := i.A.finite_toSet.measurableSet)
    (n := shellCount r (dyadicD r ^ shortExp ζ) - 1) (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) (r := r)
    (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (q0 := q0) (α := α) (C_exit := CE) (C_good := C)
    (C := shellChone68 CE C) (N_cov := shellNcov68) (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0)
    (hCw := shellChone68_hCw CE C) (hCg := hC.le) (hlf := hmω.1) (hcons := hmω.2)
    (hstopFin := hstopFinPw hadm)
    (hRbd := fun k _ => by
      obtain ⟨t, ht⟩ := Lemma68WindowRfGlobal.windowRfT_hRbd_global S.μ ρ (shortExp ζ) c0W C (dyadicD r)
        hd0 hd1 ha1 ω ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k
      exact ⟨t, Filter.Eventually.of_forall fun x hx => ht x hx⟩)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k hk => (hRr' k hk).mono fun x hx hxm => mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le)
    (hVolC := hVolC hadm)
    (hVolY := fun k hk => (hVolY hadm k hk).mono fun x hx hxl y hy =>
      hx hxl y (Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith) hy))
    (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith) (ωg := ωG)
    (hGreen := hGreen hadm) (hWalk := hWalk hadm)
    (hCountGood := hCountGood hadm) (ρcell := Lemma68HoneCellGood.rhoCell68 ρ)
    (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCellGood hadm) (hd := hd0) (aW := shortExp ζ) (hRf := hRf) (hEl := hElPw hadm)
    (hcut := hcutR) (hκ2 := hκ2) (hεcell := hεcell) (hsc := hsc) (hεα := hεα) (hεmass := hεmass)
    (hb := hbω) (hx1 := hx1Pw hadm) (hmomS := hmomS hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos) (hdbl := hdbl)

#print axioms MatedCRT.Lemma68B1Assembly.hdbl_of_exit_geom_path_gexp
#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_split

end Lemma68B1Assembly
end MatedCRT
