import MatedCRT.FirstPass.S4S6c.ShellChain68
import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.ShellConstOrder68

/-!
# The shell-chain core, the reduction of `ShellChainStmt` to it, and the reduction of `hU`

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
open MatedCRT.Lemma68ConstOrder
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
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C δ) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCoreStmt` with the Eps antecedents.** The body of `ShellChainCoreStmt`, plus
`2 ω₀ β⁻ < α` and `2 ω₀ < 2/(2+γ)² - ζ` next to the `ω₀` hypotheses; `ε ≤ shellEps0 γ α ω₀` in the ε-clause; and the radius
cutoff `∀ r, 0 < r → r ≤ R → (dyadicD r)^{shortExp ζ} < rhoCell68 ρ - ρ` next to `R ≤ rAmp q0 ζ`. -/
def ShellChainCoreEpsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0Z γ α ω₀ ζ → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **Old implies Eps.** `ShellChainCoreStmt` specialises to `ShellChainCoreEpsStmt`: the Eps
antecedents are ignored, the ε-clause is used for `ε ≤ shellEps0`, and the radius cutoff is ignored. -/
theorem shellChainCoreEpsStmt_of_shellChainCoreStmt {𝒮 : SpaceFillingSLEModel} (h : ShellChainCoreStmt 𝒮) :
    ShellChainCoreEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ _ _ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA _ s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε _
  exact hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε

/-- **`ShellChainEpsStmt` from the Eps shell-chain core.** As `shellChainStmt_of_core`, with the
radius cutoff passed through. -/
theorem shellChainEpsStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreEpsStmt 𝒮) : ShellChainEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  have hc0 : 0 < shellC068 := by unfold shellC068; positivity
  have hc1 : shellC068 < 1 / 5 := by
    unfold shellC068
    have h := Real.exp_le_one_iff.2 (show (-2 : ℝ) ≤ 0 by norm_num)
    linarith
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 shellC068 hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) shellC068 C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) shellC068 C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav⟩

/-- **`ShellChainCoreEpsStmt` at the Green constant `CG`.** The body of `ShellChainCoreEpsStmt` with the
window constant `c₀(CG) = shellC0 CG` in `WindowPrevAt` and `badWindowOf`, the threshold `shellEps0ZCG γ α ω₀ ζ CG` and the
sparsity `shellS1CG γ CG`. -/
def ShellChainCoreCGStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGStmt` from the CG shell-chain core.** The window family is supplied by
`shortWindow_fieldFamily_at` with the prevalence constants `C, C'` of `hprev` at `(a = shortExp ζ, c₀ = c₀(CG))`; `hprev` holds
for every `c₀ ∈ (0, 1/5)` (`ShortWindowGoodRadiusPrevalenceStmt`, S6r/ShortWindow.lean:61), and `c₀(CG) ∈ (0,1/5)` for `CG > 0`
(`shellC0_bounds`). -/
theorem shellChainCGStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGStmt 𝒮) : ShellChainCGStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨hc0, hc1⟩ := shellC0_bounds CG hCG
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 (shellC0 CG) hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav⟩

/-- **`ShellChainStmt` from the shell-chain core.** The window family is supplied by `shortWindow_fieldFamily_at`
with the prevalence constants `C, C'` of `hprev` at `(a = shortExp ζ, c₀)`, and the window clause by `hcore`. -/
theorem shellChainStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreStmt 𝒮) : ShellChainStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  have hc0 : 0 < shellC068 := by unfold shellC068; positivity
  have hc1 : shellC068 < 1 / 5 := by
    unfold shellC068
    have h := Real.exp_le_one_iff.2 (show (-2 : ℝ) ≤ 0 by norm_num)
    linarith
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 shellC068 hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) shellC068 C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) shellC068 C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav⟩

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Draft inputs and the shell-chain core.** Same conclusion as
`uniformConstantOrderLowerBound_of_chain` (Guard68S10), with the chain supplied by `shellChainStmt_of_core`. -/
theorem hU_of_core {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBound_of_chain 𝒮 hG hC hE (shellChainStmt_of_core hprev hcore)

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Draft inputs and the Eps shell-chain core.**
Same conclusion as `hU_of_core`, through `uniformConstantOrderLowerBoundEps_of_chain` (Guard68S10.lean). -/
theorem hU_of_core_eps {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreEpsStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBoundEps_of_chain 𝒮 hG hC hE (shellChainEpsStmt_of_core hprev hcore)

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Draft inputs and the CG shell-chain core.**
Same conclusion as `hU_of_core_eps`, through `uniformConstantOrderLowerBoundCG_of_chain` (Guard68S10.lean). -/
theorem hU_of_core_cg {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBoundCG_of_chain 𝒮 hG hC hE (shellChainCGStmt_of_core hprev hcore)

/-- **`ShellChainCoreCGStmt` with the mesh-radius cell event.** The body of
`ShellChainCoreCGStmt`, with the cell-size hypothesis at the mesh radius `(1 + ρ)/2` (`rhoCell68 ρ`) and the almost sure
mesh clause on `meshEventR` (cell component at `(1 + ρ)/2`; Green and exit components at `ρ`). -/
def ShellChainCoreCGRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
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
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCoreCGRStmt` with the counting component.** The body of
`ShellChainCoreCGRStmt`, with the counting exponent `β > 0`, the counting hypothesis `PolyHighProb (countingGoodEvent S α β ρ)`
at the chain exponent `α`, and the almost sure clause on `countingMeshEventR` (Guard68S10). -/
def ShellChainCoreCGRCStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGRStmt` from the CG mesh-radius shell-chain core.** As
`shellChainCGStmt_of_core`, with `ShellChainCoreCGRStmt` and `meshEventR`. -/
theorem shellChainCGRStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRStmt 𝒮) : ShellChainCGRStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨hc0, hc1⟩ := shellC0_bounds CG hCG
  obtain ⟨C, C', hC0, hC'0, hP⟩ := hprev (shortExp ζ) ha0 ha1 γ hγ0 hγ2 (shellC0 CG) hc0 hc1
  have hP' : WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP'
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav⟩

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the Draft inputs and the CG mesh-radius shell-chain core.**
Same conclusion as `hU_of_core_cg`, through `uniformConstantOrderLowerBoundCGR_of_chain`
(Guard68S10.lean). -/
theorem hU_of_core_cgR {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBoundCGR_of_chain 𝒮 hG hC hE (shellChainCGRStmt_of_core hprev hcore)

/-- **`ShellChainCGRCStmt` from the counting CG shell-chain core.** As
`shellChainCGRStmt_of_core`, with `ShellChainCoreCGRCStmt` (counting exponent `β`, counting hypothesis at the chain exponent
`α`, almost sure clause on `countingMeshEventR`). -/
theorem shellChainCGRCStmt_of_core {𝒮 : SpaceFillingSLEModel} (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRCStmt 𝒮) : ShellChainCGRCStmt 𝒮 := by
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
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hKp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hKp Ew hEwm hEwp hav⟩

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the counting CG shell-chain core.** Same
conclusion as `hU_of_core_cgR`, through `uniformConstantOrderLowerBoundCGRC_of_chain` (Guard68S10.lean), with the
counting input `hK : CountingAtExitAlphaStmt 𝒮` in place of the exit-time input. -/
theorem hU_of_core_cgRC {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮) (hprev : ShortWindowGoodRadiusPrevalenceStmt)
    (hcore : ShellChainCoreCGRCStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  MatedCRT.uniformConstantOrderLowerBoundCGRC_of_chain 𝒮 hG hC hK (shellChainCGRCStmt_of_core hprev hcore)

end Lemma68ChainCore
end MatedCRT

#print axioms MatedCRT.Lemma68ChainCore.shellChainCGRStmt_of_core
#print axioms MatedCRT.Lemma68ChainCore.hU_of_core_cgR
#print axioms MatedCRT.Lemma68ChainCore.shellChainCGRCStmt_of_core
#print axioms MatedCRT.Lemma68ChainCore.hU_of_core_cgRC
#print axioms MatedCRT.Lemma68ChainCore.shellChainStmt_of_core
#print axioms MatedCRT.Lemma68ChainCore.hU_of_core
#print axioms MatedCRT.Lemma68ChainCore.shellChainCoreEpsStmt_of_shellChainCoreStmt
#print axioms MatedCRT.Lemma68ChainCore.shellChainEpsStmt_of_core
#print axioms MatedCRT.Lemma68ChainCore.hU_of_core_eps
