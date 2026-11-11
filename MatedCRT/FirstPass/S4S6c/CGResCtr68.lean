import MatedCRT.FirstPass.S4S6c.CGRCXG2Core68
import MatedCRT.FirstPass.S4S6c.CGResX1MomS68

/-!
# The exit-vertex centre bound of the CG-R residual

`CGRCXG2Core68.ShellCGResG2Ctr` (residual `74a`, the `hc` binder of `shellOneTest_at_of_goodEnv_loc_g2`) asks that at a
`FullAdmAt` point of `ShellPtPremCG`, the exit vertex of every leaf path lies in
`B(0, 1 - windowRf(centre) / 4)`.

Route (step "shorter discharge"):
the stronger bound `‖vertexPoint b‖ < rhoCell68 ρ - windowRf(centre) / 4` is already proved by
`CGResX1MomS68.resX1_pt` (the residual `hx1`, which contains the exit-cell and annulus computation). Since `ρ < 1`
gives `rhoCell68 ρ < 1` (`Lemma68HoneCellGood.rhoCell68_lt_one`), the bound with `1` in place of `rhoCell68 ρ` follows
by `sub_lt_sub_right`. No mathematical input beyond the clauses of `ShellPtPremCG` used by `resX1_pt`.

* `shellCGResCtr_pt`: the pointwise form with explicit premises (the binders of `resX1_pt`, no `ShellPtPremCG` bundle).
* `shellCGResG2Ctr_holds`: the residual `ShellCGResG2Ctr 𝒮` for every space-filling SLE model `𝒮`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGResCtr

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellCoreCG
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly

/-- **The exit-vertex centre bound at one point (pointwise form of `ShellCGResG2Ctr`).** Same explicit
premises as `CGResX1MomS68.resX1_pt`. The exit vertex of each leaf path satisfies
`‖vertexPoint b‖ < 1 - windowRf(centre) / 4`, from `resX1_pt` and `rhoCell68 ρ < 1`. -/
theorem shellCGResCtr_pt {γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hω₀ : 0 < ω₀) (hω2ζ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0B : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hRρ : R ≤ ρ / 4) (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hrR : r ≤ R)
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) (hr10 : 10 * ε ^ ω₀ ≤ r)
    (hmeshω : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε)
    (hgap : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hcurve : Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hmult : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hcont : Continuous (S.η ω)) (hμN : ∀ v : ℂ, S.μ ω {v} = 0) (hμF : IsFiniteMeasureOnCompacts (S.μ ω))
    (hdeg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (hadj : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hadjAll : ∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
        ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
          (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat)‖
          < 1 - windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 := by
  intro k hk
  filter_upwards [Lemma68CGResX1MomS.resX1_pt S i hγ0 hγ2 hω₀ hω2ζ hζ0 hζ1 hρ0 hρ1 hCG hq0 hq0B hRρ hRA hrR hs₀
    hε hεe hr10 hmeshω hgap hcurve hmult hcont hμN hμF hdeg hadj hadjAll hFA k hk] with x hx hleaf
  exact lt_trans (hx hleaf) (sub_lt_sub_right (Lemma68HoneCellGood.rhoCell68_lt_one hρ1) _)

/-- **The exit-vertex centre bound holds (residual `74a`).** Destructures `ShellPtPremCG`
(ShellCoreCG68.lean:287) as `CGResX1MomS68.shellCGResX1_holds` does, and applies `shellCGResCtr_pt`; the mesh event is
`countingMeshEventR_meshR`. No hypothesis. -/
theorem shellCGResG2Ctr_holds (𝒮 : SpaceFillingSLEModel) : Lemma68CGRCXG2Core.ShellCGResG2Ctr 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨hγ0, hγ2, hω₀, -, -, -, -, hω2ζ, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, -, hq0B, -, hRρ, hRA, -,
    hs₀, -, -, hε, hεe, hr10, hrR, -, hmeshC, hgap, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll, -, -⟩ :=
    hpre
  exact shellCGResCtr_pt S i hγ0 hγ2 hω₀ hω2ζ hζ0 hζ1 hρ0 hρ1 hCG hq0 hq0B hRρ hRA hrR hs₀ hε hεe hr10
    (countingMeshEventR_meshR hmeshC) hgap hcurve hmult hcont hμN hμF hdeg hadj hadjAll hFA

end Lemma68CGResCtr
end MatedCRT

#print axioms MatedCRT.Lemma68CGResCtr.shellCGResCtr_pt
#print axioms MatedCRT.Lemma68CGResCtr.shellCGResG2Ctr_holds
