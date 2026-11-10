import MatedCRT.FirstPass.S4S6c.ShellHoneInst68

/-!
# The radius-outside one-test order input `ShellOneTestOrderAeRStmt` (q2 G1, fp-S4S6c-G1-order)

* `ShellOneTestOrderAeRStmt 𝒮`: `ShellOneTestOrderAeStmt 𝒮` (ShellHoneInst68.lean:158) with the quantifier `∀ r`
  moved outside `∀ᵐ ω ∂S.P`. Nothing else changes. The radius bounds `10 * ε ^ ω₀ ≤ r ≤ R` do not involve `ω`, so they
  move out with `∀ r`; the event `ω ∈ Ew (dyadicD r)`, the premise `FullAdm` and the conclusion `∃ Rf, ...` stay inside
  `∀ᵐ ω`.
* `shellOneTestOrderAeRStmt_of_ae`: `ShellOneTestOrderAeStmt 𝒮 → ShellOneTestOrderAeRStmt 𝒮`. The radius-outside form is
  the weaker input: a radius-by-radius almost-sure statement, which is the form the window route (B1Assembly68.lean,
  `shellOneTest_ae_fixedR`) delivers for a fixed radius.

NOT PROVED here: `ShellOneTestOrderAeRStmt 𝒮 → ShellChainCoreStmt 𝒮`. The consumers use the radius inside the almost-sure
quantifier, over an interval of reals and not over a countable family:
* ShellHoneInst68.lean:202-203 (`shellChainCoreStmt_of_oneTestOrder`): the hypothesis is applied, for a fixed `ω`, to an
  arbitrary real `r` with `10 * ε ^ ω₀ ≤ r ≤ R`;
* ShellChainCore68.lean:99 (`ShellChainCoreStmt`): `∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) → ...` lies
  inside `∀ᵐ ω ∂S.P`;
* S6d.lean:102 (`UniformConstantOrderLowerBoundStmt`, the consumer hU): `{ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ...}`
  is the event of `ProbTendsToOne` at each `ε`;
* paper, corrected draft l.2788-2790 (lemma:constant-order-lower-bound-div): "with probability approaching one as ε goes
  to zero, ... for all r ∈ [10 ε^ω, δ]".
From `∀ r, ∀ᵐ ω, P r ω` one gets no `∀ᵐ ω, ∀ r, P r ω` in general: on `[0,1]` with Lebesgue measure and `A r = {ω ≠ r}`,
each `A r` has full measure and `⋂ r, A r = ∅`. `ae_all_iff` needs a countable index, and the consumers do not give one.

Terminology: Armstrong-Kuusi-Mourrat (shells, one-test bound), Duplantier-Sheffield (LQG measure), Armitage-Gardiner (balls).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68ShellHoneInst

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The radius-outside one-test order input** (q2 G1): `ShellOneTestOrderAeStmt` with `∀ r` moved outside `∀ᵐ ω ∂S.P`;
nothing else changed. The admissibility premise is `FullAdmAt (sparsityS1 γ)`, as in the working-tree
`ShellOneTestOrderAeStmt` (ShellHoneInst68.lean:177); the committed HEAD version still has `FullAdm` (legacy 1/4 guard),
so this file imports the working-tree state. Not a frozen statement; the uniform-in-r form is the one the consumers use. -/
def ShellOneTestOrderAeRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      ∀ ε : ℝ, 0 < ε → ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R →
      ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellOneTestOrderAeStmt` implies its radius-outside form.** For a fixed radius, the almost-sure statement of
`ShellOneTestOrderAeStmt` (which holds for all radii inside `∀ᵐ ω`) gives the almost-sure statement at that radius. -/
theorem shellOneTestOrderAeRStmt_of_ae {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeStmt 𝒮) :
    ShellOneTestOrderAeRStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε r hr1 hr2
  refine (hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε).mono ?_
  intro ω hω hmesh hcurve hmult hωE i hi
  exact hω hmesh hcurve hmult r hr1 hr2 hωE i hi

/-- **The pointwise one-test input on the window-good event** (fp-S4S6c-uniform-r-source). The written argument of the
corrected draft gives the one-test order on ONE event per `ε`, for all radii at once: the dyadic Borel-Cantelli
construction of the short-window good radii (corrected draft l.2866-2945, one null set for every dyadic scale), the
intersection of the `ε`-events with `r² ≤ d < 2r²` for dyadic `d`, uniform over `r` (l.2995-3016), and the one-test
estimate on a good annulus, which is pointwise (l.3033-3036). Window avoidance is put at each dyadic scale `(1/2)^k`
(countably many), so the almost-sure part is a countable intersection (`shellOneTestOrderAeStmt_of_pointwise`).
Named input, not frozen. -/
def ShellOneTestPointwiseStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      ∀ ε : ℝ, 0 < ε → ∀ ω : Ω, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The countable swap** (fp-S4S6c-uniform-r-source): the pointwise input, with the window avoidance almost surely at
the countably many dyadic scales `(1/2)^k` (`ae_all_iff` over `ℕ`, from the almost-sure `hav` of
`ShellOneTestOrderAeStmt`), gives the almost-sure order statement `ShellOneTestOrderAeStmt` with all radii inside `∀ᵐ ω`. -/
theorem shellOneTestOrderAeStmt_of_pointwise {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestPointwiseStmt 𝒮) :
    ShellOneTestOrderAeStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy] with ω hω hmesh hcurve hmult
  exact hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp ε hε ω hmesh hcurve hmult hω

/-- **`ShellChainCoreStmt` from the pointwise one-test input** (the variant of `shellChainCoreStmt_of_oneTestOrderR` that
the written argument supports): through `shellOneTestOrderAeStmt_of_pointwise` and `shellChainCoreStmt_of_oneTestOrder`. -/
theorem shellChainCoreStmt_of_oneTestPointwise {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestPointwiseStmt 𝒮) :
    ShellChainCoreStmt 𝒮 :=
  shellChainCoreStmt_of_oneTestOrder (shellOneTestOrderAeStmt_of_pointwise h)

end Lemma68ShellHoneInst
end MatedCRT

#print axioms MatedCRT.Lemma68ShellHoneInst.shellOneTestOrderAeRStmt_of_ae
#print axioms MatedCRT.Lemma68ShellHoneInst.shellOneTestOrderAeStmt_of_pointwise
#print axioms MatedCRT.Lemma68ShellHoneInst.shellChainCoreStmt_of_oneTestPointwise
