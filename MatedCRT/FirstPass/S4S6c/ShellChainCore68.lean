import MatedCRT.FirstPass.S4S6c.ShellChain68
import MatedCRT.FirstPass.S4S6c.Guard68S10

/-!
# The shell-chain core, the reduction of `ShellChainStmt` to it, and the reduction of `hU` (q2, fp-S4S6c-hU-chain)

* `WindowPrevAt γ a c₀ C C'`: the prevalence bound of `ShortWindowGoodRadiusPrevalenceStmt` (S6r/ShortWindow.lean:61)
  at fixed window constants `(a, c₀, C, C')`, with the bad window `badWindowOf` (ShellChain68.lean:33).
* `shortWindow_fieldFamily_at`: the field-measurable window family of `shortWindow_fieldFamily_ae`
  (ShellChain68.lean:45) with the constants `C, C'` given as arguments. Two uses of one existential proof give
  unrelated constants, so the constants must be passed, not re-chosen from `hprev`.
* `ShellChainCoreStmt 𝒮`: NAMED INPUT. The chain bound on good windows. For the parameters of `ShellChainStmt` there
  is a ball-ratio constant `c₀ ∈ (0, 1/5)` such that, for every `C, C'` with the prevalence bound at
  `(γ, a = shortExp ζ, c₀, C, C')`, every polynomially-high window family avoiding the bad window almost surely
  satisfies the window clause of `ShellChainStmt`.
* `shellChainStmt_of_core`: `ShellChainStmt 𝒮` from `hprev` and `ShellChainCoreStmt 𝒮`.
* `hU_of_core`: `UniformConstantOrderLowerBoundStmt 𝒮` from the Draft inputs `hG, hC, hE`, `hprev` and `hcore`.

Relations not stated in the sources and therefore NOT assumed: `c₀` is existential (not `K.c0` of a
`Constants68 γ ρ`), and `C` is quantified only over prevalence-admissible constants. Terminology: Armstrong-Kuusi-
Mourrat (good annuli, prevalence of good radii), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68ChainCore

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open DyadicCutoff68 Lemma68Window

/-- The prevalence bound of `ShortWindowGoodRadiusPrevalenceStmt` at fixed window constants `(a, c₀, C, C')`:
for every admissible cone field and every scale `d ∈ (0,1)`, the bad window has probability at most `C' d⁶`. -/
def WindowPrevAt (γ a c₀ C C' : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ d : ℝ, 0 < d → d < 1 → P (badWindowOf μ ρ a c₀ C d) ≤ ENNReal.ofReal (C' * d ^ 6)

/-- **The field-measurable short-window family at given constants.** This is `shortWindow_fieldFamily_ae`
(ShellChain68.lean:45) with the prevalence constants `C, C'` passed in as `hP : WindowPrevAt γ a c₀ C C'`. -/
theorem shortWindow_fieldFamily_at {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (a c₀ C C' ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hP : WindowPrevAt γ a c₀ C C') :
    ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
      HarmonicBalls.PolyHighProb S.P Ew ∧
      ∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ a c₀ C δ := by
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  obtain ⟨μ', hμ'm, hμ'ae⟩ := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮 γ hγ hγ2 Ω S hS
  have hN : S.P {ω | ¬ (μ' ω = S.μ ω)} = 0 := ae_iff.1 hμ'ae
  have hbad_le : ∀ δ : ℝ, S.P (badWindowOf μ' ρ a c₀ C δ) ≤ S.P (badWindowOf S.μ ρ a c₀ C δ) := by
    intro δ
    calc S.P (badWindowOf μ' ρ a c₀ C δ)
        ≤ S.P (badWindowOf S.μ ρ a c₀ C δ ∪ {ω | ¬ (μ' ω = S.μ ω)}) := by
          refine measure_mono (fun ω hω => ?_)
          by_cases h : μ' ω = S.μ ω
          · exact Or.inl ((badWindowOf_iff_of_eq S.μ μ' ρ a c₀ C δ ω h).1 hω)
          · exact Or.inr h
      _ ≤ S.P (badWindowOf S.μ ρ a c₀ C δ) + S.P {ω | ¬ (μ' ω = S.μ ω)} := measure_union_le _ _
      _ = S.P (badWindowOf S.μ ρ a c₀ C δ) := by rw [hN, add_zero]
  refine ⟨fun δ => (badWindowOf μ' ρ a c₀ C δ)ᶜ, ?_, ?_, ?_⟩
  · intro δ
    exact (WindowEventMeasurable.measurableSet_shortWindowEvent_of_measurable μ' hμ'm ρ δ a c₀ C).compl
  · refine ⟨6, by norm_num, C', 1, one_pos, fun r hr hr1 => ?_⟩
    rw [compl_compl, show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    exact (hbad_le r).trans (hP ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hcone r hr hr1)
  · intro δ
    filter_upwards [hμ'ae] with ω hω hin hbad
    exact hin ((badWindowOf_iff_of_eq S.μ μ' ρ a c₀ C δ ω hω).2 hbad)

/-- **NAMED INPUT: the shell chain on good windows (window clause of `ShellChainStmt`, Ew given).**
For the parameters of `ShellChainStmt` there is `c₀ ∈ (0, 1/5)` such that for every `C, C'` with the prevalence bound
`WindowPrevAt γ (shortExp ζ) c₀ C C'`, every polynomially-high window family `Ew` (measurable for the field
σ-algebra) whose members almost surely avoid the bad window `badWindowOf S.μ ρ (shortExp ζ) c₀ C`, satisfies, for each
`ε > 0` and almost every `ω` of the mesh event, the window clause of `ShellChainStmt`
(Lemma 6.8 shell chain: one-test bound `hone`, shell order `ShellOrderAe`, count `count_hypothesis`).
The relations of `c₀, C` with `Constants68 γ ρ` are not stated in the sources and are not assumed. -/
def ShellChainCoreStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE R q0 s₀ : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → 0 < q0 → q0 ≤ 1 → 0 < R → R ≤ ρ / 4 →
    R ≤ Lemma68Cutoff.rAmp q0 ζ → 0 < s₀ → s₀ < 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ < 1 / 5 ∧
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) c₀ C C' →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) c₀ C δ) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainStmt` from the shell-chain core.** The window family is supplied by `shortWindow_fieldFamily_at`
with the prevalence constants `C, C'` of `hprev` at `(a = shortExp ζ, c₀)`, and the window clause by `hcore`. -/
theorem shellChainStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreStmt 𝒮) : ShellChainStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE R q0 s₀ hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 hq0 hq1 hR0 hRρ hRA hs₀ hs₁
    Ω _ S hS hGp hCp hEp
  obtain ⟨c₀, hc0, hc1, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE R q0 s₀ hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 hq0 hq1 hR0 hRρ hRA hs₀ hs₁
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 c₀ hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) c₀ C C' := hP
  obtain ⟨Ew, hEwm, hEwp, hav⟩ := shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) c₀ C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl C C' hC0 hC'0 hP' Ω S hS hGp hCp hEp Ew hEwm hEwp hav⟩

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Draft inputs and the shell-chain core.** Same conclusion as
`uniformConstantOrderLowerBound_of_chain` (Guard68S10), with the chain supplied by `shellChainStmt_of_core`. -/
theorem hU_of_core {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBound_of_chain 𝒮 hG hC hE (shellChainStmt_of_core hprev hcore)

end Lemma68ChainCore
end MatedCRT
