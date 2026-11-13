import MatedCRT.FirstPass.S4S6c.ShellChainCGRCX68
import MatedCRT.FirstPass.LICGRCY68

/-!
# The Y counting CG chain: split Green exponent and volume-guarded radius

Copy of the X chain of `ShellChainCGRCX68.lean` consuming the one-test input
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt`. Three changes with respect to the X chain:

* The radius clause carries the volume guard `LICGRCY68.VolReady68 S γ ζ r ω` after `ω ∈ Ew (dyadicD r)`. At the guard
  assembly the radius bound is `dd ω = min R (min (dd₀ ω) ((tVol ω / (8 · 2^a))^(1/(1+ζ))))`, with `tVol` the
  field-measurable volume cutoff `FieldVolCutoffStmt` (`VolCutoffField68.lean:171`, derived from `VolumeGrowthStmt` in `Closed6x68Y.lean`).
* A second Green exponent `ωG` with `2 * ω₀ < ωG` (`LICGRCY68` (75a)). The mesh exponent `ω₀` of
  `CountingMeshEventsHiStmt` is chosen with `4 * ω₀ ≤ ωG`, so that `greenLowEvent68_polyHighProb` (UniformEvents.lean:74)
  gives `PolyHighProb (greenLowEvent68 S ωG ρ CG)` with the same `CG` as at `ω₀`.
* The good-annulus constant `C` is free: no comparison with `CG`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set HarmonicBalls Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGRCY

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ConstOrder DyadicCutoff68 Lemma68Window
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **Field-measurable volume cutoff (named input).** For `γ ∈ (0,2)`, every valid model and every
`ω` off a null set, there is a field-measurable radius `tVol ω > 0` below which every ball `B(z, δ)`, `z ∈ B(0, 1-δ)`,
has mass at least `δ^b` with `b = (2+γ)²/2 + 1`. Discharged from `VolumeGrowthStmt` by `VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr` (`Closed6x68Y.lean`). -/
def FieldVolCutoffStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ tVol : Ω → ℝ, Measurable[S.fieldSigma] tVol ∧ (∀ ω, 0 < tVol ω) ∧
      ∀ᵐ ω ∂S.P, ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)

/-- **Counting mesh events with a split Green exponent.** `CountingMeshEventsEpsStmt` (Guard68S10.lean:974) with the
mesh exponent `ω₀` and an extra exponent `ωG` with `2 * ω₀ < ωG`, `PolyHighProb (greenLowEvent68 S ωG ρ CG)` at the same
`CG`. -/
def CountingMeshEventsHiStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 / 2 ∧ ∃ ω₀ α β : ℝ, 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧ 0 < β ∧
    ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧ 2 * ω₀ * chosenBetaMinus γ < α ∧ 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    ∃ ωG : ℝ, 2 * ω₀ < ωG ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CG : ℝ, 0 < CG ∧ ∃ CE : ℝ, 0 < CE ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) ∧
        HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ωG ρ CG) ∧
        HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) ∧
        HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) ∧
        HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ)

/-- **`CountingMeshEventsHiStmt` from the Draft inputs.** Copy of `countingMeshEventsEpsStmt_of_draft`
(Guard68S10.lean:987) with the mesh exponent `ω₀ = min (ωG/4) (min (α/(4β⁻)) (q/4))`, where `ωG` is the Draft Green
exponent of `greenLowEvent68_polyHighProb`. The old choice `ω₀ = min ωG (…)` gives no room for `2 * ω₀ < ωG`. -/
theorem countingMeshEventsHi_of_draft (𝒮 : SpaceFillingSLEModel) (hG : GreenKernelLowerBoundStmt 𝒮)
    (hC : CellSizeEstimateStmt 𝒮) (hK : CountingAtExitAlphaStmt 𝒮) : CountingMeshEventsHiStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨ωG, hωG, hGr⟩ := greenLowEvent68_polyHighProb hG hγ hγ2
  obtain ⟨α, β, hα, hβK, hKr⟩ := hK γ hγ hγ2
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hq0 : 0 < q := by rw [hq_def]; positivity
  have hq1 : q < 1 / 2 := by
    rw [hq_def, div_lt_iff₀ h2γ]
    nlinarith
  have hqq : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  have hβ : 0 < chosenBetaMinus γ := by unfold chosenBetaMinus; positivity
  have hβ1 : 1 ≤ chosenBetaMinus γ := by
    unfold chosenBetaMinus; have := sq_nonneg (2 + γ); linarith
  obtain ⟨ω₀, hω₀def⟩ : ∃ ω₀ : ℝ, ω₀ = min (ωG / 4) (min (α / (4 * chosenBetaMinus γ)) (q / 4)) :=
    ⟨_, rfl⟩
  have hω₀1 : ω₀ ≤ ωG / 4 := by rw [hω₀def]; exact min_le_left _ _
  have hω₀2 : ω₀ ≤ α / (4 * chosenBetaMinus γ) := by
    rw [hω₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hω₀3 : ω₀ ≤ q / 4 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hω₀pos : 0 < ω₀ := by
    rw [hω₀def]; exact lt_min (by linarith) (lt_min (div_pos hα (by linarith)) (by linarith))
  have hHi : 2 * ω₀ < ωG := by linarith
  have hω₀G : ω₀ ≤ ωG := by linarith
  have hexp1 : 2 * ω₀ * chosenBetaMinus γ < α := by
    have h4 : ω₀ * (4 * chosenBetaMinus γ) ≤ α := by
      rwa [le_div_iff₀ (by linarith)] at hω₀2
    nlinarith
  have hωα : ω₀ < α := by nlinarith [mul_le_mul_of_nonneg_left hβ1 hω₀pos.le]
  have hωq : ω₀ < 2 / (2 + γ) ^ 2 - q := by rw [hqq]; linarith
  have hexp2 : 2 * ω₀ < 2 / (2 + γ) ^ 2 - q := by rw [hqq]; linarith
  refine ⟨q, hq0, hq1, ω₀, α, β, hω₀pos, hωα, hα, hβK, hωq, hexp1, hexp2, ωG, hHi, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  obtain ⟨CE, hCE, hKS⟩ := hKr ρ hρ0 hρ1
  refine ⟨CG, hCG, CE, hCE, fun Ω _ S hS => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hGS ω₀ hω₀pos hω₀G Ω S hS
  · exact hGS ωG (by linarith) le_rfl Ω S hS
  · exact hC γ hγ hγ2 q ρ hq0 (by linarith) hρ0 hρ1 Ω S hS
  · exact (hKS Ω S hS).1
  · exact (hKS Ω S hS).2

/-- **`ShellChainCGRCXStmt` with the Y one-test input.** The X chain statement with: the Green exponent
`ωG` (`2 * ω₀ < ωG`, universal, its `PolyHighProb` at `ρ`, `CG` as at `ω₀`), the constant `εG` (from the one-test input,
after `q0`), `ε ≤ εG` and the almost sure membership `ω ∈ greenLowEvent68 S ωG ρ CG ε`, and the volume guard
`VolReady68 S γ ζ r ω` in the radius clause. -/
def ShellChainCGRCYStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → ∀ ωG : ℝ, 2 * ω₀ < ωG →
    ∃ q0 εG : ℝ, 0 < q0 ∧ 0 < εG ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ωG ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ε ≤ εG → ∀ᵐ ω ∂S.P,
          ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
          ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
          ω ∈ greenLowEvent68 S ωG ρ CG ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) → LICGRCY68.VolReady68 S γ ζ r ω →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGRCYStmt` from the Y one-test order input.** Copy of `shellChainCGRCX_of_core`
(ShellChainCGRCX68.lean:122) and `shellChainCoreCGRCX_of_oneTestOrderCGRCX` (:70): the window constants `C, C'` come from
`hprev` (free, no `C ≤ CG`), the one-test input supplies `q0, εG` and the shell order, the exit step is
`Lemma68ChainGlue.exitQ_core_step` as in the X chain. -/
theorem shellChainCGRCY_of_oneTestOrderCGRCY {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (h : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) : ShellChainCGRCYStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hHi
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨hc0, hc1⟩ := shellC0_bounds CG hCG
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 (shellC0 CG) hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' := hP
  obtain ⟨q0, εG, hq0, hεG, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hHi C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, εG, hq0, hεG, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hGH hCp hEp hEr hKp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  refine ⟨Ew, hEwm, hEwp, fun ε hε hle hleG => ?_⟩
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hGH hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle hleG).mono ?_
  intro ω hω hmesh hexit hgreen hcurve hmult r hr1 hr2 hωE hvol i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hexit hgreen hcurve hmult r hr1 hr2 hωE hvol i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **`GuardProbStmt` from the Y counting CG chain.** Copy of `guardProbStmtCGRCX_of_chainCGRCX`
(ShellChainCGRCX68.lean:147) with `CountingMeshEventsHiStmt`, the Green event at `ωG` (almost sure, `ε ≤ εG`) and the
radius `dd ω = min R (min (dd₀ ω) ((tVol ω / (8·2^a))^(1/(1+ζ))))`. The almost sure event is `goodField ∩ {volume cutoff at
tVol ω}`; `r ≤ dd ω` gives `VolReady68 S γ ζ r ω` with `t = tVol ω`. -/
theorem guardProbStmtCGRCY_of_chainCGRCY (𝒮 : SpaceFillingSLEModel)
    (hMesh : CountingMeshEventsHiStmt 𝒮) (hVol : FieldVolCutoffStmt 𝒮) (hChain : ShellChainCGRCYStmt 𝒮) :
    Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, β, hω₀, hωα, hα0, hβ0, hωζ, hexp1, hexp2, ωG, hHi, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, _, _, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨_, _, _, _, hPHm⟩ := hmesh ((1 + ρ) / 2) (by linarith) (by linarith)
  have hαρ : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ' C) := by
    intro ρ' h0 h1
    obtain ⟨_, _, CE', hCE', hPH'⟩ := hmesh ρ' h0 h1
    exact ⟨CE', hCE', fun Ω _ S hS => (hPH' Ω S hS).2.2.2.1⟩
  obtain ⟨CE, hCE, hPHc⟩ := Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_common_CE 𝒮 hαρ ρ hρ0 hρ1
  obtain ⟨q0, εG, hq0, hεG, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ0 hζ0 hζ1 hρ0 hρ1 ωG hHi
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
  obtain ⟨hGp, hGH, _, _, hKp⟩ := hPH Ω S hS
  obtain ⟨hEp, hEr⟩ := hPHc Ω S hS
  have hCpm : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) :=
    (hPHm Ω S hS).2.2.1
  obtain ⟨tVol, htVm, htVpos, htVae⟩ := hVol γ hγ0 hγ2 Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hGH hCpm hEp hEr hKp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hcapm : Measurable[S.fieldSigma] (fun ω => (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ))) :=
    (htVm.div_const _).pow_const _
  have hcappos : ∀ ω, 0 < (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) := fun ω =>
    Real.rpow_pos_of_pos (div_pos (htVpos ω) (by positivity)) _
  have hEX : ProbTendsToOne S.P (fun ε => countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
      exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε ∩ greenLowEvent68 S ωG ρ CG ε) :=
    ((probTendsToOne_countingMeshEventR hGp hCpm hEp hKp).inter (probTendsToOne_of_polyHighProb hEr)).inter
      (probTendsToOne_of_polyHighProb hGH)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ) := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0, htVae] with ω h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω →
      ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)} := ⟨_, rfl⟩
  have hG : S.P Gᶜ = 0 := by rw [hGdef]; exact ae_iff.1 hGae
  have hGmem : ∀ ω, ω ∈ G ↔ (ω ∈ goodField S Ew dd0 ∧ ∀ δ : ℝ, 0 < δ → δ < tVol ω →
      ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) := by
    intro ω; subst hGdef; exact Iff.rfl
  have he0 : 0 < shellEps0ZCG γ α ω₀ ζ CG := shellEps0ZCG_pos γ α ω₀ ζ CG
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ → Set Ω, E = fun ε => if ε ≤ min (shellEps0ZCG γ α ω₀ ζ CG) εG then
      (countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∩
        exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε) ∩ greenLowEvent68 S ωG ρ CG ε
      else ∅ := ⟨_, rfl⟩
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small (lt_min he0 hεG) hEX (fun ε _ hle => by simp only [hEdef, hle, ↓reduceIte])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ G →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r →
        r ≤ min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))) →
        ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ min (shellEps0ZCG γ α ω₀ ζ CG) εG
    · have hle1 : ε ≤ shellEps0ZCG γ α ω₀ ζ CG := hle.trans (min_le_left _ _)
      have hle2 : ε ≤ εG := hle.trans (min_le_right _ _)
      filter_upwards [hpt ε hε hle1 hle2] with ω hω
      rintro ⟨hωE, hωG'⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      have hωm' : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε ∧
          ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε ∧
          ω ∈ greenLowEvent68 S ωG ρ CG ε := by
        simp only [hEdef, hle, ↓reduceIte] at hωE
        exact ⟨hωE.1.1, hωE.1.2, hωE.2⟩
      obtain ⟨hGfs, hGvol⟩ := (hGmem ω).1 hωG'
      have hrR : r ≤ R := hrd.trans (min_le_left _ _)
      have hrd0 : r ≤ dd0 ω := hrd.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hrc : r ≤ (tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) :=
        hrd.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hvol : LICGRCY68.VolReady68 S γ ζ r ω := ⟨tVol ω, htVpos ω, hGvol, hrc⟩
      exact hω hωm'.1 hωm'.2.1 hωm'.2.2 hGfs.1 hGfs.2.1 r hr hrR (hGfs.2.2 r hr0 hrd0) hvol i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp only [hEdef, hle, ↓reduceIte, Set.mem_empty_iff_false, not_false_eq_true])
  refine ⟨fun ω => min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))),
    measurable_const.min (hdd0m.min hcapm),
    fun ω => lt_min hR0 (lt_min (hdd0pos ω) (hcappos ω)), fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (min (dd0 ω) ((tVol ω / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))))
    (E := E) (G := G) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **`UniformConstantOrderLowerBoundStmt` from the Y counting CG chain.** -/
theorem uniformConstantOrderLowerBoundCGRCY_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮) (hVol : FieldVolCutoffStmt 𝒮)
    (hChain : ShellChainCGRCYStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (guardProbStmtCGRCY_of_chainCGRCY 𝒮 (countingMeshEventsHi_of_draft 𝒮 hG hC hK) hVol hChain)

end Lemma68CGRCY

namespace Lemma68ShellTopCGRCY

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Y counting CG one-test order input.**
Copy of `Lemma68ShellTopCGRCX.hU_top_cgRCX` (ShellChainCGRCX68.lean:256) with `hOne` the Y form
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` and the volume cutoff `hVol : FieldVolCutoffStmt 𝒮` as an extra input. -/
theorem hU_top_cgRCY {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hOne : MatedCRT.LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68CGRCY.uniformConstantOrderLowerBoundCGRCY_of_chain 𝒮 hG hC hK hVol
    (Lemma68CGRCY.shellChainCGRCY_of_oneTestOrderCGRCY
      (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ) hOne)

end Lemma68ShellTopCGRCY
end MatedCRT
