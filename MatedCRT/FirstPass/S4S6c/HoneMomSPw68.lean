import MatedCRT.FirstPass.S4S6c.HoneMomS239_68
import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.Guard68S10
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped
import MatedCRT.FirstPass.S6r.ShellOmegaStop
import MatedCRT.FirstPass.S4S6c.HoneWalkAe68
import MatedCRT.FirstPass.S4S6c.ShellCorePw68
import MatedCRT.FirstPass.S4S6c.HoneSetup68
import MatedCRT.FirstPass.S4S6c.HoneRadii68

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

/-- **The binder `hmomS` of `shellOneTest_of_direct_ae_rcell_rho` (HoneLeafAe68.lean:696) at one point `ω`, at the
radius `ρmom`.** Under `ω ∈ exitTimeEvent68 S α ρmom CE ε` (the exit-moment clause at the deterministic radius `ρmom`,
UniformEvents.lean:48), `HoneMomS239.Shell.hmomS_rhoMom` gives the leaf binder for every `k ≤ n` and `P`-almost every
walk in `leafPre`, with test sets `D ⊆ ball 0 ρmom` (the form of `hmomS_pointwise` with `ρ` replaced by `ρmom`). The
margin binder `hx1` is not an input of this conclusion. -/
theorem hmomS_pointwise_rhoMom {γ ρ s₀ α CE ε ρmom C ζ r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hω : ω ∈ exitTimeEvent68 S α ρmom CE ε) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
            ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
              exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
                ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                  (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                    ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N := by
  intro _ k hk
  have hcl : S3cBridge.ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α CE ρmom := hω.1
  exact HoneMomS239.Shell.hmomS_rhoMom hcl (i.A : Set ℤ) (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (fillCells ε (S.η ω) (i.Θ : Set ℤ)) (winRf S ρ ζ C r ω) r (dyadicD r ^ shortExp ζ) (dyadicD r) i.a k hk

/-- **The binder `hx1` of `shellOneTest_of_direct_ae_rcell_rho` at one point `ω` (the `ρmom` margin; the residual
`ShellResX1` of z5).** Under `RegularEnvAt68` at `ω` and `FullAdmAt`, for every `k ≤ n` and `P`-almost every walk in
`leafPre` the exit vertex satisfies `‖vertexPoint (x T)‖ < ρmom - R / 4`, with `T = shellExit`, `R = winRf (shellCentre)`.
This is the first conjunct of `HoneWalkAe68.hWalk_ae_of_walk` (chat 239 l.787-793), re-proved from its components
(`walk_inputs_ae`, `hEl_ae_of_walk`, `hb_ae_of_walk`, `exitVertex_mem_ball_of_sphere`): `hWalk_ae_of_walk` also needs
`10 ε^{ω₀} ≤ r` with `2 ω₀ < K.ω`, which the `hx1` consumer does not have.

Environment facts at `ω`, all explicit:
* `hreg` (`RegularEnvAt68`): continuity of `η ω`, curve escape (cocompact limit), local finiteness and adjacency of
  `S.mult ε ω`, and the edge masses `edgeMeasure ≠ 0, ≠ ⊤`;
* `hadm` (`FullAdmAt`): `ConfigOK` (the vertex set `F0`, the fill closure in `ball 0 (ρ/2)`, `ball 0 s₀ ⊆ fill`) and,
  through `hstart_of_fullAdmAt`, the start cell meets the frontier of the thickened fill;
* `hmω : CellDiamLe ε (η ω) (dyadicD r / 100) univ` (the global mesh, the same form as `hRr_fixedOmega`);
* `hgap : ρ ≤ ρmom`, `hrρ : r ≤ ρ / 4`, `hrle : r ≤ countThreshold ζ`.
The window radius `winRf` is in `[dyadicD r, dyadicD r ^ shortExp ζ]` on every eligible centre for every `ω`
(`windowRfT_rangeShortEligible`: `windowRfT` equals `dyadicD r` on the bad window event), so no window binder is needed. -/
theorem hx1_fixedOmega {γ ω₀ ρ CG ζ α CE C ε s₀ r ρmom : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r)
    (hrρ : r ≤ ρ / 4) (hrle : r ≤ countThreshold ζ) (hgap : ρ ≤ ρmom)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < ρmom - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4 := by
  intro hadm
  obtain ⟨-, hcurve, hmult, hη, -, -, hdeg, hadjC, hadjε⟩ := hreg
  obtain ⟨hlf, hcons⟩ := hmult ε hε
  have hedge := hadjε ε hε
  have hp := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (Metric.ball (0 : ℂ) ρ) := hadm.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) :=
    subset_closure.trans hadm.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hadm.1.2.2 (Metric.mem_ball_self hs₀)
  have hst := Lemma68ShellCorePw.hstart_of_fullAdmAt S ω i hη hε hr0 hs₀ hadm
  have hr1 : r ≤ 1 := by linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (Lemma68ChainGlue.dyadicD_mem hr0 hr1).2
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  have hcb := Lemma68ChainGlue.countBound_zeta hζ0 hr0 hrle hd hdr hd2
  have hζr : r ^ ζ ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000 := by
    have h := Real.rpow_le_rpow hr0.le hrle hζ0.le
    unfold countThreshold at h
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hζ0.ne', Real.rpow_one] at h
  have hrpos : 0 < r ^ ζ := Real.rpow_pos_of_pos hr0 ζ
  have hkey : 1 ≤ countConst ζ * r ^ (-ζ) := by
    unfold countConst
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, one_le_div hrpos]
    have hX : (0 : ℝ) < (2 : ℝ) ^ (-shortExp ζ) := by positivity
    linarith
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h := hkey.trans hcb
    exact_mod_cast h
  have hn : shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 = shellCount r (dyadicD r ^ shortExp ζ) :=
    Nat.sub_add_cancel hN1
  have hNs : 20 * (((shellCount r (dyadicD r ^ shortExp ζ) - 1) + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [hn]
    have h1 : ((shellCount r (dyadicD r ^ shortExp ζ) : ℕ) : ℝ) ≤ r / (400 * dyadicD r ^ shortExp ζ) := by
      unfold shellCount
      exact Nat.floor_le (by positivity)
    have hpos : 0 < 400 * dyadicD r ^ shortExp ζ := by positivity
    have h2 := (le_div_iff₀ hpos).mp h1
    nlinarith [h2]
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ winRf S ρ ζ C r ω z ∧ winRf S ρ ζ C r ω z ≤ dyadicD r ^ shortExp ζ :=
    Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω
  have hPath := Lemma68HoneGoodEventAe.walk_inputs_ae hη hε hp hedge hlf hcons i.a hF0 hst
  have hEl := Lemma68HoneGoodEventAe.hEl_ae_of_walk (A := (↑i.A : Set ℤ))
    (τU := vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) (Rf := winRf S ρ ζ C r ω)
    (m := S.mult ε ω) (s0 := i.a) hη hε hr0 hrρ hd hds hs4 hNs rfl hmω hF0 h0 hKb hRf hPath
  have hhit : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
        (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
      ∀ t : ℕ, shellHit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε (S.η ω) (ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) (4 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
            (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 3)) :=
    fun k hk => (hEl k hk).mono fun x hx hxm t ht =>
      Lemma68HoneExitGeom.shellHit_interior_of_mesh hε (fillCells ε (S.η ω) ↑i.Θ) hd hmω k x
        (hRf _ (hx hxm)).1 t ht
  have hb := Lemma68HoneExitGeom.hb_ae_of_walk hη (fillCells ε (S.η ω) ↑i.Θ)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1) hdeg hadjC (fun _ _ => rfl) hhit
  intro k hk
  filter_upwards [hb k hk, hEl k hk] with x hbx helx hpre
  have hbx' := hbx hpre
  have hz := helx hpre
  have hRz := hRf _ hz
  have hmeshLoc : ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε (S.η ω) k', ∀ q ∈ cell ε (S.η ω) k', dist p q ≤ dyadicD r / 100 :=
    fun k' hk' => hmω k' (Set.Nonempty.mono (Set.inter_subset_inter_right _ (Set.subset_univ _)) hk')
  have hv := Lemma68HoneWalkAe.exitVertex_mem_ball_of_sphere hε
    (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
      (winRf S ρ ζ C r ω) k x).toNat)
    hd hds hRz.2 hgap hz hmeshLoc hbx'
  exact mem_ball_zero_iff.mp hv

/-- **`hmomS_pointwise` with a general sparsity coefficient `s1` (variant, fp-S4S6c-s1-generic, q3).** The guard
`FullAdmAt s1` replaces `FullAdmAt (sparsityS1 γ)`. The proof discards the guard (`intro _`), so no property of `s1`
is used: no hypothesis `0 < s1` or `s1 < 1` is needed. The original `hmomS_pointwise` is unchanged. -/
theorem hmomS_pointwise_s1 {γ ω₀ ρ CG ζ α CE ε C s₀ r : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hω : ω ∈ Lemma68Guard10.meshEvent S γ ω₀ ρ CG ζ α CE ε)
    (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
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

/-- **`hmomS_pointwise_rhoMom` with a general sparsity coefficient `s1` (variant, fp-S4S6c-s1-generic, q3).** The guard
`FullAdmAt s1` replaces `FullAdmAt (sparsityS1 γ)`. The proof discards the guard (`intro _`), so no property of `s1`
is used: no hypothesis `0 < s1` or `s1 < 1` is needed. The original `hmomS_pointwise_rhoMom` is unchanged. -/
theorem hmomS_pointwise_rhoMom_s1 {γ ρ s₀ α CE ε ρmom C ζ r : ℝ} (s1 : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ω : Ω} (hω : ω ∈ exitTimeEvent68 S α ρmom CE ε) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
            ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
              exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
                ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                  (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                    ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N := by
  intro _ k hk
  have hcl : S3cBridge.ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α CE ρmom := hω.1
  exact HoneMomS239.Shell.hmomS_rhoMom hcl (i.A : Set ℤ) (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (fillCells ε (S.η ω) (i.Θ : Set ℤ)) (winRf S ρ ζ C r ω) r (dyadicD r ^ shortExp ζ) (dyadicD r) i.a k hk

end HoneMomSPw68
end MatedCRT
