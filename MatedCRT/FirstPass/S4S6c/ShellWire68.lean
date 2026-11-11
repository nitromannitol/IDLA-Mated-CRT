import MatedCRT.FirstPass.S6r.ShellExitFinal
import MatedCRT.FirstPass.S6r.ShellPathAe
import MatedCRT.FirstPass.S4S6c.ShellIdent68
import MatedCRT.FirstPass.S4S6c.HoneWalk

/-!
# Wiring of the Lemma 6.8 shell exit bound

* `exitQ_le_pow_shell_walk`: `exitQ_le_pow_shell` (S6r/ShellExitFinal) with its one-test hypothesis `hone` written in the
  walk-centred form `testEndExit (shellWalkParam k) (shellExit k)`, which is the conclusion of `hone_exitQ_walk`
  (S4S6c/HoneWalk) at `R k := R ∘ shellCentre k`, `T k := shellExit k`. The translation is the identification
  `testEnd_fun_eq_testEndExit_shell` (S4S6c/ShellIdent68).
* `shellOrderAe_of_path`: the almost-sure shell-order provider `ShellOrderAe` (S6r/ShellOrder), from the named almost-sure
  path facts, by `Lemma68ShellPathAe.shell_ineqs_ae` (S6r/ShellPathAe). Its hypotheses are exactly those of
  `shell_ineqs_ae`; nothing is added.
-/

namespace MatedCRT
namespace Lemma68ShellWire

open MeasureTheory
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **Lemma 6.8, shell form with the walk-centred one-test bound.** `exitQ ≤ (1 - q)^(n + 1)` from the one-test bound
`hone` in the walk-centred form (the conclusion of `hone_exitQ_walk`), the shell-order inequalities `hShell`, and the
environment finiteness `hlf`, `hcons`. -/
theorem exitQ_le_pow_shell_walk {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r s d : ℝ)
    (R : ℂ → ℝ) (i : Lemma68Config.Config68) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (Lemma68Window.testEndExit ε (S.η ω)
            (shellWalkParam ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k))).indicator (fun _ => (1 : ℝ)) |
          (isStoppingTime_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k).measurableSpace] x
          ≤ 1 - q)
    (hShell : Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r s d R n (S.mult ε ω) i.a)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ (n + 1) := by
  refine Lemma68ShellExitFinal.exitQ_le_pow_shell S ε ω r s d R i hq1 n (fun k hk => ?_) hShell hlf hcons
  rw [testEnd_fun_eq_testEndExit_shell]
  exact hone k hk

/-- **The shell-order provider.** `ShellOrderAe` from the almost-sure path facts `hae` and the environment hypotheses, by
`shell_ineqs_ae` (S6r/ShellPathAe), with the same hypotheses and no others. -/
theorem shellOrderAe_of_path {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop}
    {n : ℕ} {mm : ℤ → ℤ → ℕ} {a : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hmesh : CellDiamLe ε η h Set.univ) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hstart : (cell ε η a ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hmap : ∀ j k : ℤ, mm j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hae : ∀ᵐ x ∂(srwLaw mm a),
      vExitTime (killed ε η Θ F0 r) x ≠ ⊤ ∧
      (∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤ ∧
        testEnd ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤) ∧
      (∀ k ≤ n, Elig (shellCentre ε η (fillCells ε η ↑Θ) r s d k x))) :
    Lemma68ShellOrder.ShellOrderAe ε η Θ F0 r s d R n mm a :=
  Lemma68ShellPathAe.shell_ineqs_ae hη hε hr hs hs4 hd hh hds hΘne hR hF0 hmesh hNs hstart hmap hae

end Lemma68ShellWire
end MatedCRT
