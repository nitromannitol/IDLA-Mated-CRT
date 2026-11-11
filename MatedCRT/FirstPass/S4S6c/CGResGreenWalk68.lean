import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.B1EnvPwG68
import MatedCRT.FirstPass.S4S6c.HoneEnvEvents68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68
import MatedCRT.FirstPass.S4S6c.Guard68S10

/-!
# The CG residuals `ShellCGResGreen` and `ShellCGResWalk`

STEP A. `resGreen_pt` and `resWalk_pt` have as binders only the individual ω-level clauses of `ShellPtPremCG`
that they use, the `FullAdmAt` premise, and the named inputs listed below. Their conclusions are the bodies of
`ShellCGResGreen` (ShellCoreCG68.lean:422) and `ShellCGResWalk` (ShellCoreCG68.lean:486) after the two premises.
The global full-support clause of `ShellPtPremCG` is not used.

Named inputs (not derivable from the clauses and the landed lemmas):
* `hGreenE` (`resGreen_pt`): the Lemma 2.16 good event at the exponent `e = 2/(2+γ)^2 - ζ`, in place of `ω₀`.
  `ShellPtPremCG` supplies only the event at `ω₀` (through `meshEventR`, its `greenLowEvent68` conjunct).
* `ωm`, `hωm`, `hr10m` (`resWalk_pt`, G1): the walk input of `Lemma68B1EnvPwG.hWalk_pw_g` (B1EnvPwG68.lean:120).
* `hmesh` (`resWalk_pt`): the univ mesh `CellDiamLe` of the walk producer (HoneWalkAe68.lean:111).
-/

namespace MatedCRT
namespace Lemma68CGResGreenWalk

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder
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

/-- The cell-size clause at the radius `ρm` gives the cell-size clause at every smaller radius `ρ ≤ ρm`
(`cellSizeEvent68`, S6f/UniformEvents.lean): a cell meeting `ball 0 ρ` meets `ball 0 ρm`. -/
theorem cellSizeEvent68_of_le {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ζ ρ ρm ε : ℝ}
    (hle : ρ ≤ ρm) {ω : Ω} (h : ω ∈ cellSizeEvent68 S γ ζ ρm ε) : ω ∈ cellSizeEvent68 S γ ζ ρ ε := by
  simp only [cellSizeEvent68, Set.mem_ofPred_eq] at h ⊢
  intro k hk
  exact h k (Set.Nonempty.mono (fun x hx => ⟨hx.1, Metric.ball_subset_ball hle hx.2⟩) hk)

/-- The mesh event with the cell-size clause at the mesh radius `(1+ρ)/2` (`meshEventR`) implies the mesh event at
the radius `ρ` (`meshEvent`, Guard68S10.lean:46 and :53). -/
theorem meshEvent_of_meshEventR {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ω₀ ρ CG ζ α CE ε : ℝ} (hρ1 : ρ < 1) {ω : Ω} (h : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε) :
    ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε := by
  unfold meshEvent
  unfold meshEventR at h
  exact ⟨⟨h.1.1, cellSizeEvent68_of_le (by linarith) h.1.2⟩, h.2⟩

/-- `ε ≤ 1` from `10 ε^ω₀ ≤ r ≤ ρ/4 < 1` and `ω₀ > 0`. -/
theorem eps_le_one_of_ten_rpow {ε ω₀ r ρ : ℝ} (hω0 : 0 < ω₀) (hrε : 10 * ε ^ ω₀ ≤ r)
    (hrρ : r ≤ ρ / 4) (hρ1 : ρ < 1) : ε ≤ 1 := by
  by_contra h
  have h' : 1 < ε := not_le.mp h
  have h1 : 1 < ε ^ ω₀ := Real.one_lt_rpow h' hω0
  linarith

/-- `ε^e ≤ ε^ω₀` for `ω₀ ≤ e` and `0 < ε ≤ 1`. -/
theorem rpow_e_le_rpow_w0 {ε ω₀ e : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hωe : ω₀ < e) :
    ε ^ e ≤ ε ^ ω₀ :=
  Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hωe.le

/-- **`ShellCGResGreen` at one ω (`resGreen_pt`).** Body of `ShellCGResGreen` (ShellCoreCG68.lean:422) after its two
premises. The Green lower bound is the Lemma 2.16 good event at the exponent `e = 2/(2+γ)^2 - ζ` (named input
`hGreenE`); its cell ball `ball 0 (ρ - ε^e)` contains `ball 0 (ρ - ε^ω₀)` because `ε^e ≤ ε^ω₀`. -/
theorem resGreen_pt {γ ω₀ ζ ρ CG s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hω0 : 0 < ω₀) (hωe : ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hε0 : 0 < ε)
    (hrε : 10 * ε ^ ω₀ ≤ r) (hrρ : r ≤ ρ / 4) (hρ1 : ρ < 1)
    (hGreenE : ω ∈ HoneModelInputs68.greenLowerGoodEvent (2 / (2 + γ) ^ 2 - ζ) CG ρ S ε)
    (_hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b := by
  have hε1 : ε ≤ 1 := eps_le_one_of_ten_rpow hω0 hrε hrρ hρ1
  have hεe : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ ε ^ ω₀ := rpow_e_le_rpow_w0 hε0 hε1 hωe
  intro a ha r' hr' hrinf b hb
  have ha' : a ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (ρ - ε ^ (2 / (2 + γ) ^ 2 - ζ))) := by
    have hsub : ball (0 : ℂ) (ρ - ε ^ ω₀) ⊆ ball (0 : ℂ) (ρ - ε ^ (2 / (2 + γ) ^ 2 - ζ)) :=
      Metric.ball_subset_ball (by linarith)
    have hne : (cell ε (S.η ω) a ∩ ball (0 : ℂ) (ρ - ε ^ ω₀)).Nonempty := ha
    show (cell ε (S.η ω) a ∩ ball (0 : ℂ) (ρ - ε ^ (2 / (2 + γ) ^ 2 - ζ))).Nonempty
    exact Set.Nonempty.mono (fun x hx => ⟨hx.1, hsub hx.2⟩) hne
  exact HoneEnvEvents68.hGreen_of_mem hGreenE a ha' r' hr' hrinf b hb

/-- **`ShellCGResWalk` at one ω (`resWalk_pt`).** Body of `ShellCGResWalk` (ShellCoreCG68.lean:486) after its two
premises. The second conjunct is the split exponent `ε^e` with `e = 2/(2+γ)^2 - ζ`; it follows from the `ω₀`-form
of `hWalk_pw_g` because `ε^e ≤ ε^ω₀` (`ω₀ < e`, `0 < ε ≤ 1`). The window is `windowRfT … (shellC0 CG) C`. -/
theorem resWalk_pt {γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hω0 : 0 < ω₀) (hωe : ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hs₀ : 0 < s₀) (hε0 : 0 < ε)
    (hrε : 10 * ε ^ ω₀ ≤ r) (hrR : r ≤ R) (hRρ : R ≤ ρ / 4)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hmeshR : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε)
    (hcurve : Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hmult : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hcont : Continuous (S.η ω)) (hμN : ∀ v : ℂ, S.μ ω {v} = 0) (hμF : IsFiniteMeasureOnCompacts (S.μ ω))
    (hdeg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (hadj : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hadjAll : ∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty)
    -- named input G1: the walk exponent of `hWalk_pw_g` (B1EnvPwG68.lean:120)
    (ωm : ℝ) (hωm : 2 * ωm < ω₀) (hr10m : 10 * ε ^ ωm ≤ r)
    -- named input: the univ mesh of the walk producer (HoneWalkAe68.lean:111)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat))
                (sphere 0 ρ) := by
  have hr0 : 0 < r := by
    have := Real.rpow_pos_of_pos hε0 ω₀
    linarith
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  have hε1 : ε ≤ 1 := eps_le_one_of_ten_rpow hω0 hrε hrρ hρ1
  have hrz := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0c hζ0 hζ1 (le_trans hrR hRA)
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω := by
    unfold RegularEnvAt68
    exact ⟨meshEvent_of_meshEventR S hρ1 hmeshR, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll⟩
  have hW := Lemma68B1EnvPwG.hWalk_pw_g (C := C) (CG := CG) (α := α) (CE := CE)
    (s1 := shellS1CG γ CG) (c0W := shellC0 CG) S
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG) ω i
    hρ0 hρ1 hζ0 hζ1 hr0 hrρ hrz hε0 hε1 hs₀ hreg hmesh hωm hr10m hFA
  intro k hk
  filter_upwards [hW k hk] with x hx hP
  obtain ⟨h1, h2, h3⟩ := hx hP
  exact ⟨h1, le_trans (rpow_e_le_rpow_w0 hε0 hε1 hωe) h2, h3⟩

/-! ### STEP B: the two `_holds` (ShellCoreCG68.lean:397 and :461)

The premise `ShellPtPremCG` (post-b51e0dc: `β`, `countingMeshEventR`, no full-support clause) is destructured into the
clauses of `resGreen_pt` / `resWalk_pt`. The inputs that the premise does not carry are named hypotheses with their
exact types (BLOCKED). -/

/-- **`ShellCGResGreen` (`shellCGResGreen_holds`), conditional on the named Green input `hGreenE`.** The Lemma 2.16
good event at the exponent `e = 2/(2+γ)^2 - ζ` is not a clause of `ShellPtPremCG`: `countingMeshEventR` carries only
`greenLowEvent68` at `ω₀`. -/
theorem shellCGResGreen_holds {𝒮 : SpaceFillingSLEModel}
    (hGreenE : ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
      (Ew : ℝ → Set Ω) (ω : Ω) (_i : Lemma68Config.Config68),
      ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
        ω ∈ HoneModelInputs68.greenLowerGoodEvent (2 / (2 + γ) ^ 2 - ζ) CG ρ S ε) :
    ShellCGResGreen 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  have hGE := hGreenE γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre
  obtain ⟨hγ0, hγ2, hω0, -, -, hωe, -, -, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, -, hq0c, -, hRρ, hRA,
    -, hs0, -, -, hε0, -, hrε, hrR, -, hmeshR, -, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll, -, -⟩ := hpre
  exact resGreen_pt S ω i hω0 hωe hε0 hrε (le_trans hrR hRρ) hρ1 hGE hFA

/-- **`ShellCGResWalk` (`shellCGResWalk_holds`), conditional on the named inputs G1 and `hMesh`.**
G1 (`hG1`): the walk exponent `ωm` with `2ωm < ω₀` and `10 ε^ωm ≤ r` (unanswered).
**REFUTED as stated, do not instantiate:** for `0 < ε < 1` and `r = 10 ε^ω₀` (allowed by the premise, whose only lower
bound on `r` is `10 ε^ω₀ ≤ r`), `10 ε^ωm ≤ r` gives `ωm ≥ ω₀`, contradicting `2ωm < ω₀`. The split route
(`ε^e ≤ ε^(2ω₀) ≤ (r/10)^2` from the premise clause `2ω₀ < e`) needs a lower bound `r^2/100 ≤ winRf/8` instead.
`hMesh`: the univ mesh `CellDiamLe` of the walk producer (HoneWalkAe68.lean:111); the premise gives it only on the
cells meeting `ball 0 ρmesh` (`cellDiamLe` of `meshEventR`). -/
theorem shellCGResWalk_holds {𝒮 : SpaceFillingSLEModel}
    (hG1 : ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
      (Ew : ℝ → Set Ω) (ω : Ω) (_i : Lemma68Config.Config68),
      ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
        ∃ ωm : ℝ, 2 * ωm < ω₀ ∧ 10 * ε ^ ωm ≤ r)
    (hMesh : ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
      (Ew : ℝ → Set Ω) (ω : Ω) (_i : Lemma68Config.Config68),
      ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
        CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ) :
    ShellCGResWalk 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨ωm, hωm, hr10m⟩ := hG1 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre
  have hMe := hMesh γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre
  obtain ⟨hγ0, hγ2, hω0, -, -, hωe, -, -, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, -, hq0c, -, hRρ, hRA,
    -, hs0, -, -, hε0, -, hrε, hrR, -, hmeshR, -, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll, -, -⟩ := hpre
  exact resWalk_pt S ω i hγ0 hγ2 hρ0 hρ1 hζ0 hζ1 hCG hω0 hωe hs0 hε0 hrε hrR hRρ hq0 hq0c hRA (countingMeshEventR_meshR hmeshR) hcurve hmult
    hcont hμN hμF hdeg hadj hadjAll ωm hωm hr10m hMe hFA

end Lemma68CGResGreenWalk
end MatedCRT

#print axioms MatedCRT.Lemma68CGResGreenWalk.resGreen_pt
#print axioms MatedCRT.Lemma68CGResGreenWalk.resWalk_pt
#print axioms MatedCRT.Lemma68CGResGreenWalk.shellCGResGreen_holds
#print axioms MatedCRT.Lemma68CGResGreenWalk.shellCGResWalk_holds
