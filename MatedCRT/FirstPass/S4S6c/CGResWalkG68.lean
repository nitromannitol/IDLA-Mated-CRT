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

end Lemma68CGResWalkG
end MatedCRT

#print axioms MatedCRT.Lemma68CGResWalkG.walkG_full_pt
#print axioms MatedCRT.Lemma68CGResWalkG.walkG_pt
