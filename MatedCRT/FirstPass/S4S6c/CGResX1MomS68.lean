import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.HoneX1Loc68
import MatedCRT.FirstPass.S4S6c.HoneMomSPw68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68

/-!
# The residuals `ShellCGResX1` and `ShellCGResMomS` at one point (fp-S4S6c-cgres-x1-moms, q3)

STEP A of the task: for one environment `ω` and one radius `r`, the residual Props of ShellCoreCG68.lean
(`ShellCGResX1` at l.455, `ShellCGResMomS` at l.469) follow from the individual clauses of `ShellPtPremCG` that they use,
written as binders (exact types copied from ShellCoreCG68.lean:311-335). The mesh event is `meshEventR` (never the
full-support clause `∀ w t, 0 < t → 0 < S.μ ω (ball w t)`). The window constant is `c0W := shellC0 CG` and the sparsity
exponent is `s1 := shellS1CG γ CG`.

* `resX1_pt`: the residual `ShellCGResX1` body. Producer: `HoneX1Loc68.hx1_fixedOmega_loc_s1_g` at `ρmom = ρmesh = rhoCell68 ρ`.
  No extra hypothesis.
* `resMomS_pt`: the residual `ShellCGResMomS` body (test sets `D ⊆ ball 0 (rhoCell68 ρ)`). Producer:
  `HoneMomSPw68.hmomS_pointwise_rhoMom_s1_g` at `ρmom = rhoCell68 ρ`, which needs `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε`.
  This membership is NOT a clause of `ShellPtPremCG`: the exit component of `meshEventR` is at radius `ρ`, and
  `exitTimeEvent68 S α ρ CE ε` quantifies only over `D ⊆ ball 0 ρ` (UniformEvents.lean:48-50). It is therefore kept as the
  named hypothesis `hexitR`.
* `resMomS_ballRho_pt`: the same moments on `D ⊆ ball 0 ρ` (the conclusion of `hmomS_pointwise_s1_g`), from `meshEventR`
  alone. It does NOT match `ShellCGResMomS`; it is recorded for the operator's decision on the radius of the binder.
-/

namespace MatedCRT
namespace Lemma68CGResX1MomS

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellCoreCG
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

/-- **The residual `ShellCGResX1` at one point (q3, STEP A).** Its body, with `c0W := shellC0 CG` and
`s1 := shellS1CG γ CG`, from the clauses of `ShellPtPremCG` used by the producer. The regularity clauses `hcurve`, `hmult`,
`hcont`, `hμN`, `hμF`, `hdeg`, `hadj`, `hadjAll` are those of `RegularEnvAt68` (B1Assembly68.lean:675); `hmeshω` gives the
mesh event through `meshEventR_sub_meshEvent`; the cell-size ball `B(0, rhoCell68 ρ)` comes from
`cellDiamLe_rhoCell_of_meshEventR`. The margin gap `hgapMesh` is the gap clause `hgap` of `ShellPtPremCG`. -/
theorem resX1_pt {γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
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
          < Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 := by
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  have hεcell := shellKCG_eps_cell (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hε hεe hr10
  have hmesh := cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω hε hρ1 hr0 hrρ
    (shellC0_le_one_cg hCG) hεcell
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω :=
    ⟨meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω, hcurve, hmult, hcont, hμN, hμF,
      hdeg, hadj, hadjAll⟩
  have hrle := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0B hζ0 hζ1 hrA
  have hd : 0 ≤ dyadicD r := (dyadicD_pos r).le
  have hdp : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd _
  have hgapMesh : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have h100 : 0 ≤ dyadicD r / 100 := div_nonneg hd (by norm_num)
    linarith
  have hρm : ρ ≤ Lemma68HoneCellGood.rhoCell68 ρ := by
    unfold Lemma68HoneCellGood.rhoCell68; linarith
  exact MatedCRT.HoneX1Loc68.hx1_fixedOmega_loc_s1_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG)
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) S hreg hρ1 hζ0 hζ1
    hε hs₀ hr0 hrρ hrle hρm hgapMesh hmesh i hFA

/-- **The residual `ShellCGResMomS` at one point (q3, STEP A), with the exit-time membership at radius `rhoCell68 ρ` as
a named hypothesis.** Its body is the residual's, test sets `D ⊆ ball 0 (rhoCell68 ρ)`. The producer is
`HoneMomSPw68.hmomS_pointwise_rhoMom_s1_g` at `ρmom = rhoCell68 ρ`, with `hω := hexitR`. The membership `hexitR` is not a
clause of `ShellPtPremCG`, and `meshEventR` only gives `ω ∈ exitTimeEvent68 S α ρ CE ε`. The missing claim is the exit-moment
bound on the test sets `D ⊆ B(0, rhoCell68 ρ) = B(0, (1+ρ)/2)`; see the module docstring. -/
theorem resMomS_pt {γ ρ s₀ α CE ε r CG C ζ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (i : Lemma68Config.Config68)
    (hexitR : ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ) →
        ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
        ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
            ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N :=
  MatedCRT.HoneMomSPw68.hmomS_pointwise_rhoMom_s1_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG)
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) S hexitR i hFA

/-- **The moments of `ShellCGResMomS` with test sets `D ⊆ ball 0 ρ` (q3, STEP A; auxiliary).** From `meshEventR` alone (no
extra hypothesis): `meshEventR_sub_meshEvent` gives `ω ∈ meshEvent`, and `hmomS_pointwise_s1_g` gives the moments on
`D ⊆ ball 0 ρ`. This is NOT the residual `ShellCGResMomS` (its radius is `rhoCell68 ρ`); it is the conclusion that
`meshEventR` supports. -/
theorem resMomS_ballRho_pt {γ ω₀ ρ CG ζ α CE ε s₀ r C : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hρ1 : ρ < 1) (hmeshω : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε)
    (i : Lemma68Config.Config68)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
        ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
            ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N :=
  MatedCRT.HoneMomSPw68.hmomS_pointwise_s1_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG) S
    (meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω) i hFA

/-- **`ShellCGResX1` holds (q3, STEP B).** Destructures `ShellPtPremCG` (ShellCoreCG68.lean:287, with `β` and
`countingMeshEventR`) and applies `resX1_pt`; the mesh event is `countingMeshEventR_meshR`. No hypothesis. -/
theorem shellCGResX1_holds (𝒮 : SpaceFillingSLEModel) : ShellCGResX1 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨hγ0, hγ2, hω₀, -, -, -, -, hω2ζ, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, -, hq0B, -, hRρ, hRA, -,
    hs₀, -, -, hε, hεe, hr10, hrR, -, hmeshC, hgap, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll, -, -⟩ :=
    hpre
  exact resX1_pt S i hγ0 hγ2 hω₀ hω2ζ hζ0 hζ1 hρ0 hρ1 hCG hq0 hq0B hRρ hRA hrR hs₀ hε hεe hr10
    (countingMeshEventR_meshR hmeshC) hgap hcurve hmult hcont hμN hμF hdeg hadj hadjAll hFA

/-- **The exit-time membership at radius `rhoCell68 ρ` (q3, STEP B; NAMED PREMISE, not provable from `ShellPtPremCG`).**
`ShellCGResMomS` needs the exit moments on `D ⊆ B(0, rhoCell68 ρ)`, i.e. `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε`
(`hmomS_pointwise_rhoMom_s1_g`). `ShellPtPremCG` gives only `ω ∈ countingMeshEventR …`, whose exit component is at radius `ρ`
(Guard68S10.lean:53-55), and `exitTimeEvent68 S α ρ CE ε` quantifies over `D ⊆ ball 0 ρ` only (UniformEvents.lean:48-50). -/
def ShellCGExitRhoCell (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε

/-- **`ShellCGResMomS` holds, given the named premise `ShellCGExitRhoCell` (q3, STEP B).** Conditional: the premise is not
derivable from the clauses of `ShellPtPremCG`; the operator decides (see the module docstring). -/
theorem shellCGResMomS_holds_of_exitRhoCell (𝒮 : SpaceFillingSLEModel) (hexit : ShellCGExitRhoCell 𝒮) :
    ShellCGResMomS 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  exact resMomS_pt S i (hexit γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω hpre) hFA

/-- The residual `ShellCGResMomS` with the test sets in `ball 0 ρ` instead of `ball 0 (rhoCell68 ρ)` (q3, STEP B;
auxiliary, NOT the current residual). It holds with no premise beyond `ShellPtPremCG`: the moments on `D ⊆ ball 0 ρ` come from
`meshEventR` (`resMomS_ballRho_pt`). Recorded for the operator's decision on the radius of the residual and of
`shellOneTest_at_of_goodEnv_loc_g`'s `hmomS` binder (B1Assembly68.lean:1296-1310). -/
def ShellCGResMomSBallRho (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N

theorem shellCGResMomSBallRho_holds (𝒮 : SpaceFillingSLEModel) : ShellCGResMomSBallRho 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hρ1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmeshC,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hpre
  exact resMomS_ballRho_pt S hρ1 (countingMeshEventR_meshR hmeshC) i hFA

end Lemma68CGResX1MomS
end MatedCRT

#print axioms MatedCRT.Lemma68CGResX1MomS.resX1_pt
#print axioms MatedCRT.Lemma68CGResX1MomS.resMomS_pt
#print axioms MatedCRT.Lemma68CGResX1MomS.resMomS_ballRho_pt
#print axioms MatedCRT.Lemma68CGResX1MomS.shellCGResX1_holds
#print axioms MatedCRT.Lemma68CGResX1MomS.shellCGResMomS_holds_of_exitRhoCell
#print axioms MatedCRT.Lemma68CGResX1MomS.shellCGResMomSBallRho_holds
