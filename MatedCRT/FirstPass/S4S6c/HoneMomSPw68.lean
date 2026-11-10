import MatedCRT.FirstPass.S4S6c.HoneMomS239_68
import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped
import MatedCRT.FirstPass.S6r.ShellOmegaStop

/-!
# The shell radius for the stopped coordinates, and `hmomS` at one point of the mesh event
(fp-S4S6c-momS-pw, chat 239 section 4)

* `measurable_shellCentre_radius_stop` (hR of `HoneMomS239_68.Shell.shell_hmom_pair`): the radius
  `Rf (shellCentre k)` is measurable for the σ-algebra of the stopped coordinates at the shell exit `shellExit k`.
  The centre is read at the shell hit `shellHit k ≤ shellExit k`, so `measurable_coord_toNat_stop`
  (ChoiceStopped.lean:82) applies with the arbitrary index map `j ↦ Rf (gridRound (d/100) (vertexPoint ε η j))`:
  no measurability of `Rf` is needed.
* `hmomS_pointwise`: the binder `hmomS` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803), at one `ω`,
  from `ω ∈ meshEvent` (its exit-time component is the exit-moment clause at the radius `ρ` with constant `CE`,
  `exitTimeEvent68`, UniformEvents.lean:48) through `HoneMomS239.Shell.hmomS_rhoMom`.
  The radius of the test sets is `ρ` (the `ρmom` of q1's binder form), not `1`.
-/

namespace MatedCRT
namespace HoneMomSPw68

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68Window Lemma68Omega Lemma68OmegaStop Lemma68ShellParam Lemma68B1Assembly
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68ShellIdent MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible MatedCRT.Lemma68ConstOrder

/-- **hR: the shell radius is measurable for the stopped coordinates at the shell exit.** For `k : ℕ`, the map
`w ↦ Rf (shellCentre k w)` is `𝓕_{shellExit k}`-measurable (Mathlib `IsStoppingTime.measurableSpace`), for every
`Rf : ℂ → ℝ`. The shell hit `shellHit k` is a stopping time with `shellHit k ≤ shellExit k`, so its σ-algebra is
contained in that of `shellExit k`; and `shellCentre k w` is the grid point of `vertexPoint (w (shellHit k w))`. -/
theorem measurable_shellCentre_radius_stop (ε : ℝ) (η : ℝ → ℂ) (Kset : Set ℂ) (r s d : ℝ) (Rf : ℂ → ℝ)
    (k : ℕ) :
    Measurable[(isStoppingTime_shellExit ε η Kset r s d Rf k).measurableSpace]
      (fun w : ℕ → ℤ => Rf (shellCentre ε η Kset r s d k w)) := by
  have h1 : Measurable[(isStoppingTime_shellHit ε η Kset r s k).measurableSpace]
      (fun w : ℕ → ℤ => Rf (shellCentre ε η Kset r s d k w)) :=
    measurable_coord_toNat_stop (isStoppingTime_shellHit ε η Kset r s k)
      (fun j : ℤ => Rf (gridRound (d / 100) (vertexPoint ε η j)))
  have hle : (isStoppingTime_shellHit ε η Kset r s k).measurableSpace ≤
      (isStoppingTime_shellExit ε η Kset r s d Rf k).measurableSpace :=
    (isStoppingTime_shellHit ε η Kset r s k).measurableSpace_mono
      (isStoppingTime_shellExit ε η Kset r s d Rf k)
      (fun w => shellHit_le_shellExit ε η Kset r s d Rf k w)
  exact h1.mono hle le_rfl

/-- **The binder `hmomS` of `shellOneTest_at_of_goodEnv'` at one point `ω` of the mesh event.** Under
`ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε`, the exit-time component `exitTimeEvent68 S α ρ CE ε` is the exit-moment clause
`ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α CE ρ`. Then `HoneMomS239.Shell.hmomS_rhoMom` gives the binder for
every index `k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1`, `P`-almost every walk in `leafPre`, and the test sets
`D ⊆ ball 0 ρ`. The conclusion is the binder with `ball 0 ρ` in place of `ball 0 1` (B1Assembly68.lean:905): the
binder of `shellOneTest_at_of_goodEnv'` is not changed here. The margin binder `hx1` is not an input of this
conclusion. -/
theorem hmomS_pointwise {γ ω₀ ρ CG ζ α CE ε C s₀ r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hω : ω ∈ Lemma68Guard10.meshEvent S γ ω₀ ρ CG ζ α CE ε)
    (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
            ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
              exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
                ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                  (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                    ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N := by
  intro _
  have hexit : ω ∈ exitTimeEvent68 S α ρ CE ε := hω.2
  have hcl : S3cBridge.ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α CE ρ := hexit.1
  intro k hk
  exact HoneMomS239.Shell.hmomS_rhoMom hcl (i.A : Set ℤ) (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (fillCells ε (S.η ω) (i.Θ : Set ℤ)) (winRf S ρ ζ C r ω) r (dyadicD r ^ shortExp ζ) (dyadicD r) i.a k hk

/-- **The leaf moments `hmom1`, `hmom2` with hR discharged.** `HoneMomS239.Shell.shell_hmom_pair` with its binder
`hR` supplied by `measurable_shellCentre_radius_stop`; the named inputs left are `hTdom` and `hRbd` (q1 / operator). -/
theorem shell_hmom_pair_hR {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (a : ℤ) {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ}
    (hTdom : ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
      shellExit ε η Kset r s d Rf k w < ⊤ → shellExit ε η Kset r s d Rf k w ≤ vExitTime D w)
    (hRbd : ∀ k : ℕ, ∃ t : ℝ, ∀ w : ℕ → ℤ,
      shellExit ε η Kset r s d Rf k w < ⊤ → Rf (shellCentre ε η Kset r s d k w) ≤ t)
    (k : ℕ) :
    Integrable ({w : ℕ → ℤ | shellExit ε η Kset r s d Rf k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (shellWalkParam ε η Kset r s d Rf k w)
          (postTimePath (fun n w => w n) (shellExit ε η Kset r s d Rf k) w) : ℕ) : ℝ))) (srwLaw m a) ∧
    Integrable ({w : ℕ → ℤ | shellExit ε η Kset r s d Rf k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (shellWalkParam ε η Kset r s d Rf k w)
          (postTimePath (fun n w => w n) (shellExit ε η Kset r s d Rf k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a) :=
  HoneMomS239.Shell.shell_hmom_pair hlf hcons hη hp hε a
    (fun k => measurable_shellCentre_radius_stop ε η Kset r s d Rf k) hTdom hRbd k

end HoneMomSPw68
end MatedCRT
