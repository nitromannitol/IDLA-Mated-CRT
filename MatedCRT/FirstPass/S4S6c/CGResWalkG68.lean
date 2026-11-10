import MatedCRT.FirstPass.S4S6c.CGResWalkLoc68

/-!
# The split-leaf walk binder `hWalk` with the Green exponent `ωG` (fp-S4S6c-walk-omegaG, z11)

The split leaf `B1GoodEnvSplit68.shellOneTest_at_of_goodEnv_loc_split` takes the walk binder `hWalk` with
first conjunct on `ball 0 (ρ - ε ^ K.ω)` and second conjunct `ε ^ ωG ≤ winRf / 8`. Two producers:

* `walkG_full_pt`: the walk producer `Lemma68CGResWalkLoc.hWalk_pw_g_loc` at the exponent `ωG`
  (`K.ω := ωG`, `ωm := ω₀`; hypotheses `2 * ω₀ < ωG`, `10 * ε ^ ω₀ ≤ r`). It proves both conjuncts at `ωG`
  with no named input. The second conjunct is `eps_pow_le_eighth_of_radius` (`ε ^ ωG ≤ r² / 100 ≤ winRf / 8`).
  No `εG` is needed: `ε ≤ 1` follows from `10 * ε ^ ω₀ ≤ r ≤ ρ / 4 < 1` (`eps_le_one_of_ten_rpow`).
* `walkG_pt`: the leaf binder exactly, first conjunct on `ball 0 (ρ - ε ^ K.ω)` taken as the named hypothesis
  `hFirst` (open claim, see the report), second conjunct from `walkG_full_pt`.
* `walkG_pt_sq` (fp-S4S6c-walk-sq): the leaf binder with `hFirst` replaced by the premise `hsq : 4 * ε ^ K.ω ≤ r²`.
  The first conjunct is proved: the walk producer `hWalk_ae_of_walk_loc` at `ω0 := ω₀` (its exponent `ωG` only
  enters the second conjunct, which is not used) gives `vertexPoint ∈ ball 0 (ρ - R/4)` a.s.; `hEl_ae_of_walk_loc`
  gives `r² ≤ d ≤ R` a.s.; so `ε ^ K.ω ≤ R/4` and the ball lies in `ball 0 (ρ - ε ^ K.ω)`.
-/

namespace MatedCRT
namespace Lemma68CGResWalkG

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

/-- **The walk binder with both conjuncts at the Green exponent `ωG` (`walkG_full_pt`).** The walk producer
`hWalk_pw_g_loc` with `K := shellKCG … ωG`. The first conjunct lies on `ball 0 (ρ - ε ^ ωG)`, the second is
`ε ^ ωG ≤ winRf(centre) / 8`, the third is the gap `winRf / 8 ≤ infDist`. -/
theorem walkG_full_pt {γ ω₀ α ζ ρ CG CE C s₀ ε r ωG c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hω0 : 0 < ω₀) (hωG : 2 * ω₀ < ωG) (hε0 : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hrε : 10 * ε ^ ω₀ ≤ r)
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
            ε ^ ωG ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat))
                (sphere 0 ρ) := by
  have hωG0 : 0 < ωG := by linarith
  have hε1 : ε ≤ 1 := Lemma68CGResGreenWalk.eps_le_one_of_ten_rpow hω0 hrε hrρ hρ1
  have hW := Lemma68CGResWalkLoc.hWalk_pw_g_loc (ω₀ := ω₀) (ωm := ω₀) (C := C) (CG := CG) (α := α) (CE := CE)
    (s1 := shellS1CG γ CG) (c0W := c0W) S (shellKCG γ ρ ωG ζ CG hγ0 hγ2 hρ0 hρ1 hωG0 hζ0 hζ1 hCG) ω i
    hρ0 hρ1 hζ0 hζ1 hr0 hrρ hrz hε0 hε1 hs₀ hreg hmesh hgapM hωG hrε
  exact hW

/-- **The split-leaf walk binder `hWalk` (`walkG_pt`).** The leaf's binder with first conjunct on
`ball 0 (ρ - ε ^ K.ω)` and second conjunct `ε ^ ωG ≤ winRf / 8`. The first conjunct is the named hypothesis `hFirst`
(its exact type is the leaf's first conjunct; the missing claim is reported). The second and third conjuncts come
from `walkG_full_pt`. -/
theorem walkG_pt {γ ω₀ α ζ ρ CG CE C s₀ ε r ωG c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (K : Constants68 γ ρ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hω0 : 0 < ω₀) (hωG : 2 * ω₀ < ωG) (hε0 : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    -- named hypothesis: the first conjunct of the leaf's `hWalk` at the shell exponent `K.ω` (open claim)
    (hFirst : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω))) :
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ ωG ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat))
                (sphere 0 ρ) := by
  have hW := walkG_full_pt (ωG := ωG) (C := C) (CG := CG) (α := α) (CE := CE) (c0W := c0W) (s₀ := s₀) S ω i
    hγ0 hγ2 hρ0 hρ1 hζ0 hζ1 hCG hω0 hωG hε0 hs₀ hr0 hrρ hrz hrε hreg hmesh hgapM
  intro hFA k hk
  filter_upwards [hW hFA k hk, hFirst hFA k hk] with x hx hf hP
  obtain ⟨_, h2, h3⟩ := hx hP
  exact ⟨hf hP, h2, h3⟩

/-- **The split-leaf walk binder with the square premise (`walkG_pt_sq`).** As `walkG_pt`, with the named hypothesis
`hFirst` replaced by `hsq : 4 * ε ^ K.ω ≤ r ^ 2`. The first conjunct on `ball 0 (ρ - ε ^ K.ω)` is proved here.
Walk: `hWalk_ae_of_walk_loc` with the Green-side constants `shellKCG … ωG` and `ω0 := ω₀` (this needs only
`2 * ω₀ < ωG`); its first conjunct `vertexPoint ∈ ball 0 (ρ - R / 4)` does not involve the exponent. Radius:
`hEl_ae_of_walk_loc` and `hRf` give `r² ≤ d ≤ R` a.s., so `ε ^ K.ω ≤ R / 4` by `hsq`, and the ball is inside
`ball 0 (ρ - ε ^ K.ω)`. The vertex lies in its own cell (`vertexPoint_mem_cell_direct`), so the index is in
`cellVertices`. The second and third conjuncts are those of `walkG_full_pt`. Terminology: Duplantier-Sheffield
(walk exit of an annulus), Armitage-Gardiner (balls). -/
theorem walkG_pt_sq {γ ω₀ α ζ ρ CG CE C s₀ ε r ωG c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (K : Constants68 γ ρ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hω0 : 0 < ω₀) (hωG : 2 * ω₀ < ωG) (hε0 : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hsq : 4 * ε ^ K.ω ≤ r ^ 2) :
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ ωG ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat))
                (sphere 0 ρ) := by
  have hωG0 : 0 < ωG := by linarith
  have hε1 : ε ≤ 1 := Lemma68CGResGreenWalk.eps_le_one_of_ten_rpow hω0 hrε hrρ hρ1
  intro hFA
  have hcont : Continuous (S.η ω) := hreg.2.2.2.1
  have hr1 : r ≤ 1 := by linarith
  have hdpos : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdpos hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hdpos hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hdpos _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hdpos hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hreg.2.1
  have hlf : IsLocallyFiniteMult (S.mult ε ω) := (hreg.2.2.1 ε hε0).1
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := (hreg.2.2.1 ε hε0).2
  have hedge : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => hreg.2.2.2.2.2.2.2.2 ε hε0 j k h
  have hdeg := hreg.2.2.2.2.2.2.1
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (ball 0 ρ) := hFA.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ ball (0 : ℂ) (ρ / 2) := subset_closure.trans hFA.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hFA.1.2.2 (mem_ball_self hs₀)
  have hst := Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1 S hε0 hs₀ ω hcont r hr0 i hFA
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ∧
        windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hdpos hd1 ha1 ω hz
  have hW := Lemma68CGResWalkLoc.hWalk_ae_of_walk_loc (ε := ε) (η := S.η ω)
    (shellKCG γ ρ ωG ζ CG hγ0 hγ2 hρ0 hρ1 hωG0 hζ0 hζ1 hCG) hcont hε0 hε1 hp hedge hlf hcons i.a
    (Θ := i.Θ) (F0 := i.F0) (ρ := ρ) (r := r) (d := dyadicD r) (a := shortExp ζ)
    (s := dyadicD r ^ shortExp ζ) (ρmom := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (ω0 := ω₀)
    (Rf := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hr0 hrρ hdpos hdr hds hs4 hNs rfl hrε hωG le_rfl hgapM hmesh hF0 h0 hKb hRf hst hdeg
  have hEl := MatedCRT.Lemma68WalkLoc.hEl_ae_of_walk_loc (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) hcont hε0 hr0 hrρ hdpos hds hs4 hNs rfl hgapM hmesh hF0 h0
    hKb hRf (MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae hcont hε0 hp hedge hlf hcons i.a hF0 hst)
  have hW2 := walkG_full_pt (ωG := ωG) (C := C) (CG := CG) (α := α) (CE := CE) (c0W := c0W) (s₀ := s₀) S ω i
    hγ0 hγ2 hρ0 hρ1 hζ0 hζ1 hCG hω0 hωG hε0 hs₀ hr0 hrρ hrz hrε hreg hmesh hgapM hFA
  intro k hk
  filter_upwards [hW k hk, hEl k hk, hW2 k hk] with x hx hel hx2 hpre
  obtain ⟨hv, -⟩ := hx hpre
  obtain ⟨-, h2, h3⟩ := hx2 hpre
  have hRz := hRf _ (hel hpre)
  refine ⟨⟨_, MatedCRT.Lemma68Window.vertexPoint_mem_cell_direct hε0 _, ball_subset_ball ?_ hv⟩, h2, h3⟩
  linarith [hdr.trans hRz.1]

end Lemma68CGResWalkG
end MatedCRT

#print axioms MatedCRT.Lemma68CGResWalkG.walkG_full_pt
#print axioms MatedCRT.Lemma68CGResWalkG.walkG_pt
#print axioms MatedCRT.Lemma68CGResWalkG.walkG_pt_sq
