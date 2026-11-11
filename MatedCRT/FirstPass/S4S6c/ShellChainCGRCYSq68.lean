import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68
import MatedCRT.FirstPass.LICGRCY68

/-!
# The square-premise variant of the Y counting CG chain

The split-leaf walk `walkG_pt_sq` (CGResWalkG68.lean:117) needs the square premise `4 * ε ^ ω₀ ≤ r ^ 2` in addition to
the radius premise `10 * ε ^ ω₀ ≤ r` of the one-test. This file carries that premise through the Y chain:

* `ShellOneTestOrderAeCGRCYSqStmt`: `LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (LICGRCY68.lean:45) with the square premise
  added to the radius clause. `shellOneTestOrderAeCGRCYSq_of_Y`: the Y form implies it (the Sq form is weaker).
* `ShellChainCGRCYSqStmt`: `ShellChainCGRCYStmt` (ShellChainCGRCY68.lean:108) with the square premise in the radius clause,
  and its proof `shellChainCGRCYSq_of_oneTestOrderCGRCYSq` (copy of `shellChainCGRCY_of_oneTestOrderCGRCY`,
  ShellChainCGRCY68.lean:140, using the square premise at each radius).

Obstruction (the consumers are not closed here). Every consumer fixes the radius clause at `10 * ε ^ ω₀ ≤ r`:
`guardProbStmtCGRCY_of_chainCGRCY` (ShellChainCGRCY68.lean:172, binder `hChain`), `GuardProbStmt`
(S6e/Uniform.lean:140), `FaithfulConstantOrderLowerBoundStmt` and the other faithful headers (S6d.lean:41-100). At the
least such radius `r = 10 * ε ^ ω₀` the square premise fails for all small `ε` (`sqPremise_fails_at_min_radius`), and no
radius reindexing removes that: the square chain gives the shell conclusion only for `r ≥ max (10 * ε ^ ω₀) (2 * ε ^ (ω₀/2))`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set HarmonicBalls Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGRCYSq

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ConstOrder DyadicCutoff68 Lemma68Window
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The one-test order input with the square premise.** Copy of
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (LICGRCY68.lean:45) except the radius premise: the shell one-test is asserted
only for radii with `10 * ε ^ ω₀ ≤ r` and the square premise `4 * ε ^ ω₀ ≤ r ^ 2` of the leaf walk `walkG_pt_sq`
(CGResWalkG68.lean:117). -/
def ShellOneTestOrderAeCGRCYSqStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → ∀ ωG : ℝ, 2 * ω₀ < ωG →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 εG : ℝ, 0 < q0 ∧ 0 < εG ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ωG ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ε ≤ εG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        ω ∈ greenLowEvent68 S ωG ρ CG ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → 4 * ε ^ ω₀ ≤ r ^ 2 → r ≤ R → ω ∈ Ew (dyadicD r) →
          LICGRCY68.VolReady68 S γ ζ r ω →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- The square premise makes the one-test weaker: the Y form (LICGRCY68.lean:45) implies the Sq form by dropping the
square premise. -/
theorem shellOneTestOrderAeCGRCYSq_of_Y {𝒮 : SpaceFillingSLEModel}
    (h : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) : ShellOneTestOrderAeCGRCYSqStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hHi C C' hC0 hC'0 hP
  obtain ⟨q0, εG, hq0, hεG, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hHi C C' hC0 hC'0 hP
  refine ⟨q0, εG, hq0, hεG, hq0c, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hGH hCp hEp hEr hKp Ew hEwm hEwp hav
    ε hε hle hleG => ?_⟩
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hGH hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle hleG).mono ?_
  intro ω hω hmesh hexit hgreen hcurve hmult r hr1 _ hr3 hωE hvol i hi
  exact hω hmesh hexit hgreen hcurve hmult r hr1 hr3 hωE hvol i hi

/-- **`ShellChainCGRCYStmt` with the square premise.** Copy of `ShellChainCGRCYStmt`
(ShellChainCGRCY68.lean:108) whose radius clause carries the square premise `4 * ε ^ ω₀ ≤ r ^ 2` after `10 * ε ^ ω₀ ≤ r`. -/
def ShellChainCGRCYSqStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → 4 * ε ^ ω₀ ≤ r ^ 2 → r ≤ R → ω ∈ Ew (dyadicD r) →
            LICGRCY68.VolReady68 S γ ζ r ω →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGRCYSqStmt` from the square one-test order input.** Copy of
`shellChainCGRCY_of_oneTestOrderCGRCY` (ShellChainCGRCY68.lean:140). The window constants `C, C'` come from `hprev`,
the one-test supplies `q0, εG` and the shell order at radii satisfying both premises, and the exit step is
`Lemma68ChainGlue.exitQ_core_step` as before. -/
theorem shellChainCGRCYSq_of_oneTestOrderCGRCYSq {𝒮 : SpaceFillingSLEModel}
    (hprev : ShortWindowGoodRadiusPrevalenceStmt) (h : ShellOneTestOrderAeCGRCYSqStmt 𝒮) :
    ShellChainCGRCYSqStmt 𝒮 := by
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
  intro ω hω hmesh hexit hgreen hcurve hmult r hr1 hr2 hr3 hωE hvol i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hexit hgreen hcurve hmult r hr1 hr2 hr3 hωE hvol i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr3.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **The square premise fails at the least consumer radius (the obstruction).** For `ω₀ > 0` there
is `ε₀ > 0` such that for `0 < ε < ε₀` the radius `r = 10 * ε ^ ω₀` (the least radius of the consumers' clause
`10 * ε ^ ω₀ ≤ r`, ShellChainCGRCY68.lean:172 and S6e/Uniform.lean:140) violates `4 * ε ^ ω₀ ≤ r ^ 2`. With
`x = ε ^ ω₀ < 1/25` one has `4 x ≤ 100 x ^ 2` false. -/
theorem sqPremise_fails_at_min_radius {ω₀ : ℝ} (hω₀ : 0 < ω₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ¬ (4 * ε ^ ω₀ ≤ (10 * ε ^ ω₀) ^ 2) := by
  refine ⟨(1 / 25 : ℝ) ^ (1 / ω₀), Real.rpow_pos_of_pos (by norm_num) _, fun ε hε0 hεε₀ hle => ?_⟩
  have hx0 : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε0 ω₀
  have hpow : ((1 / 25 : ℝ) ^ (1 / ω₀)) ^ ω₀ = 1 / 25 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 25), one_div_mul_cancel hω₀.ne', Real.rpow_one]
  have hx1 : ε ^ ω₀ < 1 / 25 :=
    calc ε ^ ω₀ < ((1 / 25 : ℝ) ^ (1 / ω₀)) ^ ω₀ := Real.rpow_lt_rpow hε0.le hεε₀ hω₀
      _ = 1 / 25 := hpow
  nlinarith [mul_pos hx0 hx0]

#print axioms MatedCRT.Lemma68CGRCYSq.shellOneTestOrderAeCGRCYSq_of_Y
#print axioms MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq
#print axioms MatedCRT.Lemma68CGRCYSq.sqPremise_fails_at_min_radius

end Lemma68CGRCYSq
end MatedCRT
