import MatedCRT.FirstPass.LICGRCX68
import MatedCRT.FirstPass.S4S6c.ShellTop68
import MatedCRT.FirstPass.S4S6c.ExitRhoCell68

/-!
# The counting CG chain with the exit clause at the cell radius (fp-S4S6c-cgrcx-closures, lead li request 77b)

X copies of the counting CG chain, each step carrying the exit clause at the cell radius `rhoCell68 ρ`:

* `ShellChainCoreCGRCXStmt` (copy of `ShellChainCoreCGRCStmt`, ShellChainCore68.lean:302): the extra `PolyHighProb` of
  `exitTimeEvent68 S α (rhoCell68 ρ) CE` and the extra almost sure premise `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε`.
* `ShellChainCGRCXStmt` (copy of `ShellChainCGRCStmt`, Guard68S10.lean:946): the same two extra premises.
* `guardProbStmtCGRCX_of_chainCGRCX` (copy of `guardProbStmtCGRC_of_chainCGRC`, Guard68S10.lean:1030): one constant `CE`
  for the radii `ρ` and `rhoCell68 ρ` (`polyHighProb_exitTimeEvent68_common_CE`, ExitRhoCell68.lean:82), whose exit
  projection `hα` is read off `CountingMeshEventsEpsStmt` at each radius (one `α` for all radii). The almost sure event is
  `countingMeshEventR ∩ exitTimeEvent68 S α (rhoCell68 ρ) CE`, with `ProbTendsToOne` by `.inter`.
* `hU_top_cgRCX`: `UniformConstantOrderLowerBoundStmt` from `LICGRCX68.ShellOneTestOrderAeCGRCXStmt`.

Nothing else changes. Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGRCX

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ConstOrder DyadicCutoff68 Lemma68Window
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **`ShellChainCoreCGRCStmt` with the exit clause at the cell radius (fp-S4S6c-cgrcx-closures).** Copy of
`ShellChainCoreCGRCStmt` (ShellChainCore68.lean:302) with `PolyHighProb S.P (exitTimeEvent68 S α (rhoCell68 ρ) CE)` after
the exit hypothesis at radius `ρ`, and the almost sure premise `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε` after the
membership in `countingMeshEventR`. The conclusion is that of `ShellChainCoreCGRCStmt`. -/
def ShellChainCoreCGRCXStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCoreCGRCXStmt` from the X one-test order input (fp-S4S6c-cgrcx-closures).** Copy of
`shellChainCoreCGRCStmt_of_oneTestOrderCGRC` (ShellHoneInst68.lean:448) with the extra exit clause passed through. -/
theorem shellChainCoreCGRCX_of_oneTestOrderCGRCX {𝒮 : SpaceFillingSLEModel}
    (h : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) : ShellChainCoreCGRCXStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hexit hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hexit hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **`ShellChainCGRCStmt` with the exit clause at the cell radius (fp-S4S6c-cgrcx-closures).** Copy of
`ShellChainCGRCStmt` (Guard68S10.lean:946) with the extra `PolyHighProb` at `rhoCell68 ρ` (after the one at `ρ`) and the
extra almost sure premise `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε`. -/
def ShellChainCGRCXStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
          ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
          ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGRCXStmt` from the X counting core (fp-S4S6c-cgrcx-closures).** Copy of `shellChainCGRCStmt_of_core`
(ShellChainCore68.lean:361) with the exit clause at `rhoCell68 ρ` passed through. -/
theorem shellChainCGRCX_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRCXStmt 𝒮) : ShellChainCGRCXStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨hc0, hc1⟩ := shellC0_bounds CG hCG
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 (shellC0 CG) hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hEr hKp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav⟩

/-- **`GuardProbStmt` from the X counting CG chain (fp-S4S6c-cgrcx-closures).** Copy of `guardProbStmtCGRC_of_chainCGRC`
(Guard68S10.lean:1030). The exponent `α` is the one of `CountingMeshEventsEpsStmt` (the same at every radius); at the
radius `ρ` one constant `CE` serves both `ρ` and `rhoCell68 ρ` (`polyHighProb_exitTimeEvent68_common_CE`); the almost sure
event is `countingMeshEventR ∩ exitTimeEvent68 S α (rhoCell68 ρ) CE`. -/
theorem guardProbStmtCGRCX_of_chainCGRCX (𝒮 : SpaceFillingSLEModel)
    (hMesh : Lemma68Guard10.CountingMeshEventsEpsStmt 𝒮) (hChain : ShellChainCGRCXStmt 𝒮) :
    Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, β, hω₀, hωα, hα0, hβ0, hωζ, hexp1, hexp2, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, _, _, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨_, _, _, _, hPHm⟩ := hmesh ((1 + ρ) / 2) (by linarith) (by linarith)
  have hαρ : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ' C) := by
    intro ρ' h0 h1
    obtain ⟨_, _, CE', hCE', hPH'⟩ := hmesh ρ' h0 h1
    exact ⟨CE', hCE', fun Ω _ S hS => (hPH' Ω S hS).2.2.1⟩
  obtain ⟨CE, hCE, hPHc⟩ := Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_common_CE 𝒮 hαρ ρ hρ0 hρ1
  obtain ⟨q0, hq0, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ0 hζ0 hζ1 hρ0 hρ1
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  obtain ⟨Rc, hRc0, hRc⟩ := exists_radius_cutoff_gap hρ0 hρ1 hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) :=
    lt_min (by linarith) (lt_min hrA (lt_min hra0 hRc0))
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    shellS1CG γ CG, shellS1CG_pos γ CG, shellS1CG_lt_one γ CG hCG, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRc : R ≤ Rc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, _, _, hKp⟩ := hPH Ω S hS
  obtain ⟨hEp, hEr⟩ := hPHc Ω S hS
  have hCpm : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) :=
    (hPHm Ω S hS).2.1
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hCpm hEp hEr hKp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hEX : ProbTendsToOne S.P
      (fun ε => countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
        exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε) :=
    (probTendsToOne_countingMeshEventR hGp hCpm hEp hKp).inter (probTendsToOne_of_polyHighProb hEr)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : S.P (goodField S Ew dd0)ᶜ = 0 := ae_iff.1 hGae
  have he0 : 0 < shellEps0ZCG γ α ω₀ ζ CG := shellEps0ZCG_pos γ α ω₀ ζ CG
  set e0 : ℝ := shellEps0ZCG γ α ω₀ ζ CG with he0def
  set E : ℝ → Set Ω := fun ε => if ε ≤ e0 then
    countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
      exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε else ∅ with hEdef
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small he0 hEX (fun ε _ hle => by simp [hEdef, hle])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ goodField S Ew dd0 →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min R (dd0 ω) → ∀ i : Lemma68Config.Config68,
        Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ e0
    · filter_upwards [hpt ε hε hle] with ω hω
      rintro ⟨hωm, h1, h2, h3⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      have hωm' : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∧
          ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε := by
        simpa [hEdef, hle] using hωm
      exact hω hωm'.1 hωm'.2 h1 h2 r hr (hrd.trans (min_le_left _ _))
        (h3 r hr0 (hrd.trans (min_le_right _ _))) i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp [hEdef, hle])
  refine ⟨fun ω => min R (dd0 ω), measurable_const.min hdd0m, fun ω => lt_min hR0 (hdd0pos ω),
    fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (dd0 ω)) (E := E)
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **`UniformConstantOrderLowerBoundStmt` from the X counting CG chain (fp-S4S6c-cgrcx-closures).** Copy of
`uniformConstantOrderLowerBoundCGRC_of_chain` (Guard68S10.lean:1143). -/
theorem uniformConstantOrderLowerBoundCGRCX_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hChain : ShellChainCGRCXStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (guardProbStmtCGRCX_of_chainCGRCX 𝒮
      (Lemma68Guard10.countingMeshEventsEpsStmt_of_draft 𝒮 hG hC hK) hChain)

/-- **hU from the X counting CG shell-chain core (fp-S4S6c-cgrcx-closures).** Copy of `hU_of_core_cgRC`
(ShellChainCore68.lean:387). -/
theorem hU_of_core_cgRCX {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRCXStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBoundCGRCX_of_chain 𝒮 hG hC hK (shellChainCGRCX_of_core hprev hcore)

end Lemma68CGRCX

namespace Lemma68ShellTopCGRCX

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the X counting CG one-test order input (fp-S4S6c-cgrcx-closures).**
Copy of `Lemma68ShellTop.hU_top_cgRC` (ShellTop68.lean:92) with `hOne` the X form `LICGRCX68.ShellOneTestOrderAeCGRCXStmt`. -/
theorem hU_top_cgRCX {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : MatedCRT.LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68CGRCX.hU_of_core_cgRCX hG hC hK
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68CGRCX.shellChainCoreCGRCX_of_oneTestOrderCGRCX hOne)

end Lemma68ShellTopCGRCX
end MatedCRT
