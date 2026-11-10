import MatedCRT.FirstPass.S4S6c.HoneSetup68
import MatedCRT.FirstPass.S4S6c.HoneCellGood68
import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.Proofs.Sec6.AnnulusHit.EventInvariance

/-!
# Pointwise producers of the binders `hCellGood` and `hsel` of `shellOneTest_at_of_goodEnv'` (fp-S4S6c-cellgood-sel-pw, z10)

`shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803) takes two binders that concern one environment `ω` only, under the
guard `FullAdmAt`:

* `hCellGood` (B1Assembly68.lean:885): every cell of mesh `ε` meeting the ball `B(0, ρ_cell)`, `ρ_cell = rhoCell68 ρ`,
  has diameter at most `ε^κ`, `κ = 2/(2+γ)² - ζ` (Armstrong-Kuusi-Mourrat cells `H^ε_a`).
* `hsel` (B1Assembly68.lean:920): every short-eligible centre `z` has a good annulus event (Armstrong-Kuusi-Mourrat good
  annuli) at the window radius `winRf S ρ ζ C r ω z`, with the constants `K.c0` and `CG`.

This file gives both conclusions at ONE environment `ω`, with no almost-sure quantifier in `ω`. The conclusions are the
binder types, so the consumer may pass the results to the binders directly.

Named inputs (exact types in the statements; each one is the missing ingredient reported in the task report):
* `hCellGood_fixedOmega`: `hmesh : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε` (q2, Guard68S10.lean:52). Its cell-size component is
  at the mesh radius `(1 + ρ)/2 = rhoCell68 ρ` (`Lemma68Guard10.meshEventR_cell`, Guard68S10.lean:58), so the cell clause is
  projected, with no new premise. The earlier bare binder `hcell` (fp-S4S6c-cellgood-sel-pw) is retired.
* `hsel_fixedOmega`: `hwin : ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C (dyadicD r)`, the complement of the window
  event at the scale `dyadicD r` (ShellChain68.lean:33). It is the pointwise form of the a.s. premise
  `∀ δ, ∀ᵐ ω, ω ∈ Ew δ → ω ∉ badWindowOf …` of `ShellOneTestOrderAeEpsStmt` (ShellHoneInst68.lean, the Eps statement).
  Without it the window radius is `dyadicD r` on bad `ω` and `hsel` is not implied.
* `hsel_fixedOmega`: `hCCG : C ≤ CG`. The window radius `winRf S ρ ζ C r ω` is chosen as a good annulus radius at the
  WINDOW constant `C` (ShellWindowRf68 `windowRf_spec`), while `hsel` asserts goodness at the constant `CG` of the
  good-annulus binder. B1Assembly68.lean:803 takes `C` and `CG` as unrelated variables, so nothing gives `C ≤ CG`.
  The consumer must choose `C ≤ CG` (e.g. `C := CG`); `IsGoodAnnulusEvent.mono_const` (larger constant, weaker event)
  then gives `hsel`. Reported as an interface mismatch.

`hsel_fixedOmega` does not use `ω ∈ meshEvent`; `hCellGood_fixedOmega` does not use `FullAdmAt` (it is kept as the
premise of the binder, so that the conclusions match the binder types exactly).

Terminology: Armstrong-Kuusi-Mourrat (cells, good annuli, good radii), Armitage-Gardiner (balls), Duplantier-Sheffield
(the mated-CRT boundary-length parametrisation `η`).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneCellGoodSelPw

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68WindowRf
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68ShellHoneInst

/-- **`hCellGood` at one environment (fp-S4S6c-cellgood-sel-pw).** The cell-size event at the separate cell-control
radius `ρ_cell = rhoCell68 ρ = (1 + ρ)/2` (chat 237 §3, chat 239 l.478-501) gives the upper cell-diameter bound on
every cell meeting `B(0, ρ_cell)`: the upper half of `cellSizeEvent68` is literally the binder. -/
theorem hCellGood_fixedOmega {γ ζ ρ ε s₀ r ω₀ CG α CE : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hmesh : ω ∈ Lemma68Guard10.meshEventR S γ ω₀ ρ CG ζ α CE ε) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
  fun _ k' hk => (Lemma68Guard10.meshEventR_cell hmesh k' hk).2

/-- **`hsel` at one environment (fp-S4S6c-cellgood-sel-pw).** Off the window event at the scale `dyadicD r`, every
short-eligible centre `z` has the window radius `winRf S ρ ζ C r ω z = windowRf … z`, which is a good annulus radius for
`μ ω` (`windowRf_spec`, ShellWindowRf68.lean). The constant `K.c0` is `shellC068` (`shellK68_params`). -/
theorem hsel_fixedOmega {γ ω₀ ρ ζ C r CG s₀ ε : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (S : MatedCRTEnv Ω) (K : Constants68 γ ρ)
    (hK : K = Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hwin : ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C (dyadicD r)) (hCCG : C ≤ CG) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (Lemma68HoneSetup.winRf S ρ ζ C r ω z) z := by
  intro _ z hz
  have hc0 : K.c0 = shellC068 := by
    rw [hK]; exact (shellK68_params γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).2.2.1
  rw [hc0]
  have hw := windowRf_spec S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω hwin hz
  have hT : Lemma68HoneSetup.winRf S ρ ζ C r ω z = windowRf S.μ shellC068 C (shortExp ζ) (dyadicD r) ω z := by
    unfold Lemma68HoneSetup.winRf windowRfT
    simp only [hwin, ↓reduceIte]
  rw [hT]
  exact IsGoodAnnulusEvent.mono_const hCCG hw.2

/-- **`hCellGood` at one environment, generic sparsity exponent (fp-S4S6c-s1-generic, z10).** Same statement as
`hCellGood_fixedOmega` with `Lemma68Config.sparsityS1 γ` replaced by a free `s1 : ℝ`. The proof does not use the guard
`FullAdmAt`, so no hypothesis on `s1` is needed. -/
theorem hCellGood_fixedOmega_s1 {γ ζ ρ ε s₀ r ω₀ CG α CE s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hmesh : ω ∈ Lemma68Guard10.meshEventR S γ ω₀ ρ CG ζ α CE ε) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
  fun _ k' hk => (Lemma68Guard10.meshEventR_cell hmesh k' hk).2

/-- **`hsel` at one environment, generic sparsity exponent (fp-S4S6c-s1-generic, z10).** Same statement as
`hsel_fixedOmega` with `Lemma68Config.sparsityS1 γ` replaced by a free `s1 : ℝ`; `hCCG : C ≤ CG` stays a named premise
(operator request 73a). The proof does not use the guard `FullAdmAt`, so no hypothesis on `s1` is needed. -/
theorem hsel_fixedOmega_s1 {γ ω₀ ρ ζ C r CG s₀ ε s1 : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (S : MatedCRTEnv Ω) (K : Constants68 γ ρ)
    (hK : K = Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hwin : ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C (dyadicD r)) (hCCG : C ≤ CG) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (Lemma68HoneSetup.winRf S ρ ζ C r ω z) z := by
  intro _ z hz
  have hc0 : K.c0 = shellC068 := by
    rw [hK]; exact (shellK68_params γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).2.2.1
  rw [hc0]
  have hw := windowRf_spec S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω hwin hz
  have hT : Lemma68HoneSetup.winRf S ρ ζ C r ω z = windowRf S.μ shellC068 C (shortExp ζ) (dyadicD r) ω z := by
    unfold Lemma68HoneSetup.winRf windowRfT
    simp only [hwin, ↓reduceIte]
  rw [hT]
  exact IsGoodAnnulusEvent.mono_const hCCG hw.2

end Lemma68HoneCellGoodSelPw
end MatedCRT

#print axioms MatedCRT.Lemma68HoneCellGoodSelPw.hCellGood_fixedOmega
#print axioms MatedCRT.Lemma68HoneCellGoodSelPw.hsel_fixedOmega

#print axioms MatedCRT.Lemma68HoneCellGoodSelPw.hCellGood_fixedOmega_s1
#print axioms MatedCRT.Lemma68HoneCellGoodSelPw.hsel_fixedOmega_s1
