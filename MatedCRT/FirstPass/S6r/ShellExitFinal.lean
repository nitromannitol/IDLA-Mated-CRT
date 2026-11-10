import MatedCRT.FirstPass.S6r.ExitQAe
import MatedCRT.FirstPass.S6r.ShellOmegaStop

/-!
# Lemma 6.8 shell exit bound, final assembly (`ShellExitFinal`)

`Lemma68ExitAe.exitQ_le_pow_ae` (ExitQAe) with the shell times `T k = shellExit k`, `L k = testEnd k`
(ShellOmega) and their stopping-time property (`Lemma68OmegaStop`, ShellOmegaStop).

The four shell-order inequalities are the named almost-sure hypotheses `hTT`, `hLT`, `hCross`, `hEnd`, in exactly the
form of the conclusion of `Lemma68ShellPathAe.shell_ineqs_ae` (ShellPathAe, commit 20bea44). That lemma is not
imported here, because its import closure (GoodScale: `MatedCRT.measurable_logKernel`) clashes with the one of
WalkBridge68 (GoodAnnulusHF68). Once the clash is resolved, `hTT`, `hLT`, `hCross`, `hEnd` are discharged by
`shell_ineqs_ae` (with `hmap`, `hlf`, `hcons`, its hae (d), (e)) and `exitQ_le_pow_shell` becomes unconditional
except for the one-test bound `hone` (z8, S6r/OneTest) and the environment `hlf`, `hcons`.
-/

namespace MatedCRT
namespace Lemma68ShellExitFinal

open MeasureTheory
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe

/-- **Lemma 6.8, shell form.** For the shell times `T k = shellExit k`, `L k = testEnd k` of `ShellOmega`,
`exitQ ≤ (1 - q) ^ (n + 1)`, given the one-test bound `hone` (z8), the four almost-sure shell-order inequalities
(named inputs, discharged by `shell_ineqs_ae` after the import clash), and the environment finiteness hypotheses
`hlf`, `hcons` of the multigraph `S.mult ε ω`. -/
theorem exitQ_le_pow_shell {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r s d : ℝ)
    (R : ℂ → ℝ) (i : Lemma68Config.Config68) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)).indicator (fun _ => (1 : ℝ)) |
          (isStoppingTime_shellExit (ε := ε) (η := S.η ω) (K := fillCells ε (S.η ω) ↑i.Θ) (r := r) (s := s)
            (d := d) (R := R) k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R (j + 1) x <
          vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x →
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R j x ≤
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R (j + 1) x)
    (hLT : ∀ j < n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R (j + 1) x <
          vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x →
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R j x ≤
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R (j + 1) x)
    (hCross : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R n x <
        vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x)
    (hEnd : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R n x ≤
        vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ (n + 1) := by
  have hcross : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R n x <
            vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x :=
    hCross.mono fun _ hx _ _ => hx
  have hend : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R n x ≤
            vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x :=
    hEnd.mono fun _ hx _ _ => hx
  exact exitQ_le_pow_ae S ε ω r i
    (T := fun k => shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
    (L := fun k => testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
    (fun k => isStoppingTime_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
    (fun k => isStoppingTime_testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
    hq1 n hone hTT hLT hcross hend hlf hcons

end Lemma68ShellExitFinal
end MatedCRT
