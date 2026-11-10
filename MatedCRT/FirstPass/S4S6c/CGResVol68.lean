import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.HVolFullPw68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S4S6c.ShellConstOrder68
import MatedCRT.FirstPass.S4S6c.HoneCellGood68

/-!
# FIRST PASS S4S6c, CGResVol68: the volume residuals of the CG pointwise route
(task fp-S4S6c-cgres-vol, worker z9; residuals `ShellCGResVolC`, `ShellCGResVolY` of ShellCoreCG68.lean)

STEP A (this file): `resVolC_pt` and `resVolY_pt`, the pointwise volume bounds at ONE environment `ω`, with the
constants `K := shellKCG …` (so `K.c0 = shellC0 CG` and `K.βm = (2+γ)²/2+1` by unfolding). The producers are
`hVolC_pw_g` and `hVolY_pw_g` (HVolFullPw68.lean). The conclusions are the bodies of `ShellCGResVolC` and
`ShellCGResVolY` after their two premises `ShellPtPremCG` and `FullAdmAt`.

Clauses of `ShellPtPremCG` used: `0 < γ`, `γ < 2`, `0 < ω₀`, `0 < CG`, `0 < ζ`, `ζ < 1/2`, `0 < ρ`, `ρ < 1`,
`0 < ε`, `10 ε^ω₀ ≤ r`, `r ≤ R`, `R ≤ ρ/4`. The global full-support clause and the mesh clause are not used.

Named premises, NOT derivable from the clauses of `ShellPtPremCG` (reported in reports/z9.md):
* `hcapω`: an `∃ t` giving the volume cutoff at `ω` (the `∃ t` clause of `ShellPtPremCG`) TOGETHER WITH the radius cap
  `r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ))`. The cap is missing from `ShellPtPremCG`: `t` is only given by an
  existential, while `R` is quantified before `ω`, so no choice of `t` is controlled by the clauses.
* `hEl`: the leaf centres are eligible (the body of `ShellCGResEl`, ShellCoreCG68.lean:349).
* `hc` (C-residual only): the exit-vertex centre bound (the `hc` binder of `hVolC_pw_g`).

`hRr` (the window lies in `[r², 1]` on the leaf) is NOT a named premise: it is derived from `hEl` by
`windowRfT_bounds` and `dyadicD_mem`.
-/

namespace MatedCRT
namespace Lemma68CGResVol

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open MatedCRT.Lemma68B1Assembly
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **Volume residual `hVolC` of the CG route, pointwise at one `ω` (`ShellCGResVolC`, ShellCoreCG68.lean:388).**
The `t`-cutoff `hcapω` (cut part: the `∃ t` clause of `ShellPtPremCG`; cap part: NOT in `ShellPtPremCG`, see the
module docstring), the eligibility `hEl`, and the exit-vertex centre bound `hc` feed `hVolC_pw_g`. -/
theorem resVolC_pt {γ ω₀ ζ ρ CG C R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hω₀ : 0 < ω₀) (hCG : 0 < CG) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε) (hr10 : 10 * ε ^ ω₀ ≤ r) (hrR : r ≤ R) (hRρ : R ≤ ρ / 4)
    (hcapω : ∃ t : ℝ, 0 < t ∧ r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) ∧
      ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ))
    (hEl : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hc : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x).toNat)‖ <
            1 - windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) :
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ENNReal.ofReal ((shellC0 CG * (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^
                ((2 + γ) ^ 2 / 2 + 1))
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat))
              (shellC0 CG * (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
  intro hadm
  obtain ⟨t, ht, hrt, hcut⟩ := hcapω
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr10
  have hr1 : r ≤ 1 := le_trans hrR (le_trans hRρ (by linarith))
  have hc0 : 0 < (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG).c0 := (shellC0_bounds CG hCG).1
  have hc0' : (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG).c0 ≤ 1 / 4 :=
    le_trans (shellC0_bounds CG hCG).2.le (by norm_num)
  have ha : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have ha0 : 0 ≤ shortExp ζ := by unfold shortExp; linarith
  have hda : dyadicD r ^ shortExp ζ ≤ 1 := Real.rpow_le_one (dyadicD_pos r).le (dyadicD_le_one r) ha0
  -- the window bounds `r² ≤ W ≤ 1` on the leaf, from the eligibility `hEl` (`windowRfT_bounds`, `dyadicD_mem`)
  exact MatedCRT.Lemma68HVolFullPw.hVolC_pw_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG) (t := t) (ζ := ζ)
    (γ := γ) (ρ := ρ) (C := C) (s₀ := s₀) (ε := ε) (r := r) S (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG)
    ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut
    (fun hA k hk => (hEl hA k hk).mono fun x hx hpre =>
      ⟨le_trans (MatedCRT.Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
          (windowRfT_bounds S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
            (hx hpre)).1,
        le_trans (windowRfT_bounds S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
            (hx hpre)).2 hda⟩)
    hEl hc hadm

/-- **Volume residual `hVolY` of the CG route, pointwise at one `ω` (`ShellCGResVolY`, ShellCoreCG68.lean:405).**
The annulus volume bound on `ball 0 (rhoCell68 ρ - W/4)`, from `hVolY_pw_g` on the larger ball `ball 0 (1 - W/4)`
(`rhoCell68 ρ ≤ 1`, so the residual ball is contained in the producer's). Premises as in `resVolC_pt`
(no `hc`). -/
theorem resVolY_pt {γ ω₀ ζ ρ CG C R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hω₀ : 0 < ω₀) (hCG : 0 < CG) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε) (hr10 : 10 * ε ^ ω₀ ≤ r) (hrR : r ≤ R) (hRρ : R ≤ ρ / 4)
    (hcapω : ∃ t : ℝ, 0 < t ∧ r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)) ∧
      ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ))
    (hEl : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ)) :
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ∀ y ∈ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal (((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^
                ((2 + γ) ^ 2 / 2 + 1))
              ≤ S.μ ω (ball y ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
                (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)) := by
  intro hadm
  obtain ⟨t, ht, hrt, hcut⟩ := hcapω
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr10
  have hr1 : r ≤ 1 := le_trans hrR (le_trans hRρ (by linarith))
  have hc0 : 0 < (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG).c0 := (shellC0_bounds CG hCG).1
  have hc0' : (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG).c0 ≤ 1 / 4 :=
    le_trans (shellC0_bounds CG hCG).2.le (by norm_num)
  have ha : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have ha0 : 0 ≤ shortExp ζ := by unfold shortExp; linarith
  have hda : dyadicD r ^ shortExp ζ ≤ 1 := Real.rpow_le_one (dyadicD_pos r).le (dyadicD_le_one r) ha0
  have hρc : Lemma68HoneCellGood.rhoCell68 ρ ≤ 1 := (Lemma68HoneCellGood.rhoCell68_lt_one hρ1).le
  have hVY := MatedCRT.Lemma68HVolFullPw.hVolY_pw_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG) (t := t) (ζ := ζ)
    (γ := γ) (ρ := ρ) (C := C) (s₀ := s₀) (ε := ε) (r := r) S (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG)
    ω i hζ0 hζ1 hr0 hr1 ht hc0 hc0' hrt hcut hEl
    (fun hA k hk => (hEl hA k hk).mono fun x hx hpre =>
      ⟨le_trans (MatedCRT.Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
          (windowRfT_bounds S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
            (hx hpre)).1,
        le_trans (windowRfT_bounds S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
            (hx hpre)).2 hda⟩)
  intro k hk
  exact (hVY hadm k hk).mono fun x hx hpre y hy => hx hpre y (Metric.ball_subset_ball (by linarith [hρc]) hy)

end Lemma68CGResVol
end MatedCRT

#print axioms MatedCRT.Lemma68CGResVol.resVolC_pt
#print axioms MatedCRT.Lemma68CGResVol.resVolY_pt
