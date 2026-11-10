import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HVolCutoff239_68

/-!
# FIRST PASS S4S6c, HVolFullPw68: pointwise volume and full-support inputs of `shellOneTest_at_of_goodEnv'`
(task fp-S4S6c-volfull-pw-docs, worker z9; residuals `ShellResVolC`, `ShellResVolY`, `ShellResFull` of
ShellCorePw68.lean, reports/z5.md l.17-19)

* `hVolC_pw`, `hVolY_pw`: the binders `hVolC`, `hVolY` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803) at ONE
  environment `ω`. The environment fact is the value at `ω` of the measurable cutoff of `volume_bounds_measurable_ae`
  (HVolCutoff239_68.lean:206), given as the explicit pointwise hypothesis `hcut` with the cutoff `t`. The walk facts are the
  binders `hRr`, `hEl` of the same theorem and the exit-vertex centre bound `hc` (no written argument yet: see the report).
* `hVolY_ae_pw`: the a.s. form of the second volume input, from `volume_bounds_of_cutoff` with the centre `0`.
* `fullSupport_ae`: the full support of `S.μ ω` almost surely (`MatedCRT.Field.wholePlane_lqg_full_support_ae`).
* `hfull_pw`: the binder `hfull` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:923) at one `ω`, from the pointwise
  full-support hypothesis `hFS`.
-/

namespace MatedCRT
namespace Lemma68HVolFullPw

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open MatedCRT.Lemma68B1Assembly
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **Second volume input, almost surely on the prefix (centre `0`).** Given the cutoff bound at scale `R/4` and the
radius bounds `0 < R`, `4R < t`, `R < 4`, the lower bound `ofReal((R/4)^β) ≤ μ (B_{R/4}(y))` holds for every `y` in
`B_{1-R/4}(0)`, almost surely on `pre`; this is the second conjunct of `Lemma68Cutoff.volume_bounds_of_cutoff`, applied
with the centre `0` so that no centre bound is needed. -/
theorem hVolY_ae_pw {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'} {μ : Measure ℂ} {β c0 t : ℝ}
    (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ μ (ball z δ))
    {pre : Ω' → Prop} {R : Ω' → ℝ}
    (hR0 : ∀ᵐ x ∂ν, pre x → 0 < R x) (hRt : ∀ᵐ x ∂ν, pre x → 4 * R x < t)
    (hR1 : ∀ᵐ x ∂ν, pre x → R x < 4) :
    ∀ᵐ x ∂ν, pre x → ∀ y ∈ ball (0 : ℂ) (1 - R x / 4),
      ENNReal.ofReal ((R x / 4) ^ β) ≤ μ (ball y (R x / 4)) := by
  filter_upwards [hR0, hRt, hR1] with x h0 h1 h2 hpre
  exact (Lemma68Cutoff.volume_bounds_of_cutoff hc0 hc0' (h0 hpre) hcut (by linarith [h0 hpre, h1 hpre])
    (show ‖(0 : ℂ)‖ < 1 - R x / 4 by rw [norm_zero]; linarith [h2 hpre])).2

/-- **Full support almost surely (the a.s. form of `hfull`).** For a valid environment with `γ ∈ (0,2)`, the LQG
measure of the whole-plane field charges every ball of positive radius, almost surely. Wraps the proved
`MatedCRT.Field.wholePlane_lqg_full_support_ae`; the whole-plane GFF `hW` is an explicit input. -/
theorem fullSupport_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hV : S.IsValid 𝒮 γ)
    (hW : HarmonicBalls.IsWholePlaneGFF S.P S.hC S.hcirc) :
    ∀ᵐ ω ∂S.P, ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t) :=
  MatedCRT.Field.wholePlane_lqg_full_support_ae hγ0 hγ2 hW hV.isLQGMeasure

/-- **Pointwise `hfull` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:923) at one environment `ω`.** The full
support of `S.μ ω` is the explicit pointwise hypothesis `hFS` (the value at `ω` of `fullSupport_ae`); the binder
`hfull` is its constant in the walk-admissibility premise. -/
theorem hfull_pw {γ ρ s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (i : Lemma68Config.Config68)
    (hFS : ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t) :=
  fun _ => hFS


/-- **Pointwise `hVolC` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:856) at one environment `ω`.**
Environment: the cutoff `t > 0` and the volume bound `hcut` at scales below `t` (the value at `ω` of
`volume_bounds_measurable_ae`). Walk (almost surely on the leaf prefix, as in the binders of that theorem):
`hRr` (`r² ≤ R ≤ 1`), `hEl` (shell-centre eligibility), and the exit-vertex centre bound `hc`. The radius cap
`4R < t` follows from `hEl` through `windowRfT_bounds` (`R ≤ d^a`) and `four_mul_lt_of_radius_cap` (`hrt`). -/
theorem hVolC_pw {γ ρ ζ C s₀ ε r t : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t)
    (hc0 : 0 < K.c0) (hc0' : K.c0 ≤ 1 / 4)
    (hrt : r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ K.βm) ≤ S.μ ω (ball z δ))
    (hRr : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hEl : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hc : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖ <
            1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
  intro hadm k hk
  have ha : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hR0 := (hRr hadm k hk).mono fun x hx hpre => lt_of_lt_of_le (pow_pos hr0 2) (hx hpre).1
  have hRs := (hEl hadm k hk).mono fun x hx hpre =>
    (windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
      (hx hpre)).2
  have hRt := hRs.mono fun x hx hpre =>
    Lemma68Cutoff239.four_mul_lt_of_radius_cap rfl hζ0 ht hr0 (dyadicD_pos r)
      (dyadicD_lt_two_mul_sq hr0 hr1) (hx hpre) hrt
  exact (Lemma68Cutoff239.hVolC_hVolY_ae_of_cutoff hc0 hc0' ht hcut hR0 hRt (hc hadm k hk)).1

/-- **Pointwise `hVolY` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:865) at one environment `ω`.**
Same environment and walk inputs as `hVolC_pw`, except the exit-vertex centre bound `hc`, which the second volume input
does not need (the centre is `0`, `hVolY_ae_pw`). The bound `R ≤ d^a ≤ 1` gives `R < 4`. -/
theorem hVolY_pw {γ ρ ζ C s₀ ε r t : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t)
    (hc0 : 0 < K.c0) (hc0' : K.c0 ≤ 1 / 4)
    (hrt : r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ)))
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ K.βm) ≤ S.μ ω (ball z δ))
    (hEl : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hRr : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)) := by
  intro hadm k hk
  have ha : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hRs := (hEl hadm k hk).mono fun x hx hpre =>
    (windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) ha ω
      (hx hpre)).2
  have hR0 := (hRr hadm k hk).mono fun x hx hpre => lt_of_lt_of_le (pow_pos hr0 2) (hx hpre).1
  have hRt := hRs.mono fun x hx hpre =>
    Lemma68Cutoff239.four_mul_lt_of_radius_cap rfl hζ0 ht hr0 (dyadicD_pos r)
      (dyadicD_lt_two_mul_sq hr0 hr1) (hx hpre) hrt
  have hda : dyadicD r ^ shortExp ζ ≤ 1 :=
    Real.rpow_le_one (dyadicD_pos r).le (dyadicD_le_one r) (by unfold shortExp; linarith)
  have hR1 := hRs.mono fun x hx hpre => lt_of_le_of_lt (hx hpre) (lt_of_le_of_lt hda (show (1 : ℝ) < 4 by norm_num))
  exact hVolY_ae_pw hc0 hc0' hcut hR0 hRt hR1

end Lemma68HVolFullPw
end MatedCRT

#print axioms MatedCRT.Lemma68HVolFullPw.hVolY_ae_pw
#print axioms MatedCRT.Lemma68HVolFullPw.fullSupport_ae
#print axioms MatedCRT.Lemma68HVolFullPw.hfull_pw
#print axioms MatedCRT.Lemma68HVolFullPw.hVolC_pw
#print axioms MatedCRT.Lemma68HVolFullPw.hVolY_pw
