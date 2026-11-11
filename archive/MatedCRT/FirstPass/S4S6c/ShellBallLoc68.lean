import MatedCRT.FirstPass.S4S6c.HoneRrLocal68

/-!
# The shell-centre ball bound with the ball mesh

`hShellBall_loc` is the binder `hShellBall` of `shellOrder_fullAdm_ae_omega_loc` (ShellOrderLoc68.lean): on the
shell-centre balls `B(zc k, 2 R(zc k))`, with `zc k = gridRound (dyadicD r / 100) (vertexPoint (x (hitTime k)))`, the
cell-diameter bound `dyadicD r / 100` holds.

Route. (i) `hitTime_eq_toNat_shellHit`: the ℕ-valued hitting time of `ShellWiring.lean` is the `toNat` of the ℕ∞-valued
`shellHit` of `ShellOmega.lean`, so the centre is `shellCentre`. Both are the junk value `0` when the hit set is empty.
(ii) `ball_two_mul_R_subset_of_shortEligible`: for a centre `c ∈ shortEligible ρ d a` (`|c| < ρ - 3 d^a`) and radius
`R ≤ d^a`, the ball `B(c, 2R)` lies in `B(0, ρ)`, since `ρ - 3 d^a + 2 d^a ≤ ρ`. No gap beyond `ρ ≤ ρmesh` is needed.
(iii) the ball mesh `CellDiamLe (dyadicD r / 100) (B(0, ρmesh))` restricts to `B(c, 2R) ⊆ B(0, ρmesh)`
(`cellDiamLe_mono_set`).

The centre eligibility `c ∈ shortEligible` is the input `hEl`: it is the `Elig`-conjunct of `hde`
(ShellOrderLoc68.lean) with `Elig := shortEligible ρ d a`, and it is discharged by `hEl_ae_of_walk_loc` (WalkLoc68.lean)
on the walk inputs.

Terminology: Armitage-Gardiner (balls and their closure), Armstrong-Kuusi-Mourrat (cells `H^ε_a`, mesh),
Duplantier-Sheffield (boundary-length parametrisation).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68ShellBallLoc

open Lemma68Window Lemma68Omega

/-- **The hitting time is the `toNat` of the shell hit.** `hitTime` (ShellWiring.lean:31) is `firstShellHit` (`sInf` of
the hit set in ℕ, Crossing.lean:112), and `shellHit` (ShellOmega.lean:99) is `firstTime` (ℕ∞-valued, `Nat.find`).
Both are `0` when the hit set is empty (`⊤.toNat = 0`). -/
theorem hitTime_eq_toNat_shellHit {ε : ℝ} {η : ℝ → ℂ} (K : Set ℂ) (r s : ℝ) (x : ℕ → ℤ) (k : ℕ) :
    hitTime ε η K r s x k = (shellHit ε η K r s k x).toNat := by
  unfold hitTime firstShellHit shellHit firstTime
  split_ifs with h
  · rw [ENat.toNat_natCast]
    exact Nat.sInf_def (s := {n : ℕ | (cell ε η (x n) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty}) h
  · rw [ENat.toNat_top]
    have hempty : {n : ℕ | (cell ε η (x n) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty} = ∅ := by
      ext n
      exact ⟨fun hn => absurd ⟨n, hn⟩ h, fun hn => hn.elim⟩
    rw [hempty, Nat.sInf_empty]

/-- **The shortly eligible centre ball.** For `c ∈ shortEligible ρ d a` and `0 ≤ d^a`, `R ≤ d^a`, the ball
`B(c, 2R)` lies in `B(0, ρ)` (the shortEligible definition, ShortWindow.lean:54: `|c| < ρ - 3 d^a`). -/
theorem ball_two_mul_R_subset_of_shortEligible {ρ d a R : ℝ} {c : ℂ} (hc : c ∈ shortEligible ρ d a)
    (hRa : R ≤ d ^ a) (hd0 : 0 ≤ d ^ a) :
    Metric.ball c (2 * R) ⊆ Metric.ball (0 : ℂ) ρ := by
  intro z hz
  obtain ⟨⟨hball, -⟩, -⟩ := hc
  have h1 : dist c 0 < ρ - 3 * d ^ a := Metric.mem_ball.1 hball
  have h2 : dist z c < 2 * R := Metric.mem_ball.1 hz
  rw [Metric.mem_ball]
  have htri := dist_triangle z c 0
  linarith


/-- **`hShellBall` with the ball mesh (ShellOrderLoc68.lean).** On the shell-centre balls
`B(zc k, 2 R(zc k))`, with `zc k = gridRound (dyadicD r / 100) (vertexPoint (x (hitTime k)))`, the cell-diameter bound
`dyadicD r / 100` holds, almost surely. Inputs: `hR` (the `Rf` bound on `shortEligible ρ d a`, `d = dyadicD r`,
`a = shortExp ζ`, i.e. `hR` with `Elig := shortEligible`), `hmesh` (the ball mesh on `B(0, ρmesh)`), `hρ : ρ ≤ ρmesh`,
and `hEl`. No gap beyond
`ρ ≤ ρmesh` is needed (`ball_two_mul_R_subset_of_shortEligible`). -/
theorem hShellBall_loc {γ ζ ρ s₀ ε r ρmesh : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (i : Lemma68Config.Config68) {Rf : Ω → ℂ → ℝ}
    (hρ : ρ ≤ ρmesh)
    (hR : ∀ᵐ ω ∂S.P, ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hEl : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
          ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k))))
            (2 * Rf ω (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k)))))) := by
  filter_upwards [hmesh, hR, hEl] with ω hm hRω hElω
  intro hFA
  filter_upwards [hElω hFA] with x hx
  intro k hk
  have hkey : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
        (2 * Rf ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
    have hc := hx k hk
    have hRc := hRω _ hc
    have hd0 : 0 < dyadicD r := by unfold dyadicD; positivity
    have hd0a : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd0.le _
    have hsub := ball_two_mul_R_subset_of_shortEligible hc hRc.2 hd0a
    exact Lemma68HoneRrLocal.cellDiamLe_mono_set (hsub.trans (Metric.ball_subset_ball hρ)) hm
  rw [hitTime_eq_toNat_shellHit]
  exact hkey


/-- **`hShellBall` at a free sparsity exponent `s1`.** The conclusion is
exactly the `hShellBall` binder of `shellOrder_fullAdm_ae_omega_loc_s1` (ShellOrderLoc68.lean): the gap antecedent
`2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ ρmesh - ρ` and the guard `FullAdmAt s1`. The proof is that of
`hShellBall_loc` (l.68) with `sparsityS1 γ` replaced by `s1`; the gap antecedent is not used (only `ρ ≤ ρmesh`).
No hypothesis on `s1` is used. -/
theorem hShellBall_loc_s1 {γ ζ ρ s₀ ε r ρmesh s1 : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (i : Lemma68Config.Config68) {Rf : Ω → ℂ → ℝ}
    (hρ : ρ ≤ ρmesh)
    (hR : ∀ᵐ ω ∂S.P, ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf ω w ∧ Rf ω w ≤ dyadicD r ^ shortExp ζ)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hEl : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x
          ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) :
    2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ ρmesh - ρ →
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        CellDiamLe ε (S.η ω) (dyadicD r / 100)
          (Metric.ball (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k))))
            (2 * Rf ω (gridRound (dyadicD r / 100)
              (vertexPoint ε (S.η ω) (x (hitTime ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) x k)))))) := by
  intro _
  filter_upwards [hmesh, hR, hEl] with ω hm hRω hElω
  intro hFA
  filter_upwards [hElω hFA] with x hx
  intro k hk
  have hkey : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
        (2 * Rf ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x))) := by
    have hc := hx k hk
    have hRc := hRω _ hc
    have hd0 : 0 < dyadicD r := by unfold dyadicD; positivity
    have hd0a : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd0.le _
    have hsub := ball_two_mul_R_subset_of_shortEligible hc hRc.2 hd0a
    exact Lemma68HoneRrLocal.cellDiamLe_mono_set (hsub.trans (Metric.ball_subset_ball hρ)) hm
  rw [hitTime_eq_toNat_shellHit]
  exact hkey

end Lemma68ShellBallLoc
end MatedCRT

#print axioms MatedCRT.Lemma68ShellBallLoc.hitTime_eq_toNat_shellHit
#print axioms MatedCRT.Lemma68ShellBallLoc.ball_two_mul_R_subset_of_shortEligible
#print axioms MatedCRT.Lemma68ShellBallLoc.hShellBall_loc

#print axioms MatedCRT.Lemma68ShellBallLoc.hShellBall_loc_s1
