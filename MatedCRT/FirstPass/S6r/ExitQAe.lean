import Mathlib
import MatedCRT.FirstPass.S4S6c.WalkBridge68
import MatedCRT.FirstPass.S6r.ShellChainAe

/-!
# Quenched exit bound with almost-sure shell-order hypotheses (`ExitQAe`)

`exitQ_le_pow` (S4S6c/WalkBridge68) takes the shell-order hypotheses `hTT`, `hLT`, `hcross`, `hend`
for every path. The walk-level and quenched forms below take them `srwLaw`-almost surely, with the
same conclusion `(1 - q)^(n+1)` (notes (8.5)-(8.9) of the 6.8 argument, Duplantier-Sheffield style
quenched exit probability `exitQ`).
-/

open MeasureTheory
open MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68Window MatedCRT.Lemma68ChainAe

namespace MatedCRT
namespace Lemma68ExitAe

/-- `srw_exit_le_pow` with `hTT`, `hLT`, `hcross`, `hend` holding `srwLaw`-almost surely. -/
theorem srw_exit_le_pow_ae {m : ℤ → ℤ → ℕ} {a : ℤ} {U A : Set ℤ}
    {T L : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    (hL : ∀ k, IsStoppingTime coordFiltration (L k)) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw m a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) A (T k) (vExitTime U) →
        (srwLaw m a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) A (T k) (L k)).indicator
          (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ᵐ x ∂(srwLaw m a), T (j + 1) x < vExitTime U x → T j x ≤ T (j + 1) x)
    (hLT : ∀ j < n, ∀ᵐ x ∂(srwLaw m a), T (j + 1) x < vExitTime U x → L j x ≤ T (j + 1) x)
    (hcross : ∀ᵐ x ∂(srwLaw m a), x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U) →
      vExitTime U x ≠ ⊤ → T n x < vExitTime U x)
    (hend : ∀ᵐ x ∂(srwLaw m a), x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U) →
      vExitTime U x ≠ ⊤ → L n x ≤ vExitTime U x)
    (hnull : srwLaw m a {x | vExitTime U x = ⊤} = 0) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) ≤ (1 - q) ^ (n + 1) := by
  rw [srw_exit_eq_noEscape]
  exact prefix_bad_bound_ae coordFiltration coord_measurable MeasurableSet.of_discrete hT hL
    (isStoppingTime_vExitTime U) hq1 n hone hTT hLT hcross hend hnull

/-- `exitQ_le_pow` with the four shell-order hypotheses holding `srwLaw`-almost surely (the quenched
exit probability of a Lemma 6.8 configuration, same conclusion `(1 - q)^(n+1)`). -/
theorem exitQ_le_pow_ae {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r : ℝ)
    (i : Lemma68Config.Config68) {T L : ℕ → (ℕ → ℤ) → ℕ∞}
    (hT : ∀ k, IsStoppingTime coordFiltration (T k)) (hL : ∀ k, IsStoppingTime coordFiltration (L k))
    {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k)
          (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k)
          (L k)).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      T (j + 1) x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x → T j x ≤ T (j + 1) x)
    (hLT : ∀ j < n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      T (j + 1) x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x → L j x ≤ T (j + 1) x)
    (hcross : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
        T n x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x)
    (hend : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
        L n x ≤ vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ (n + 1) := by
  unfold Lemma68Config.exitQ
  exact srw_exit_le_pow_ae hT hL hq1 n hone hTT hLT hcross hend
    (srw_killed_top_null hlf hcons i.a ε (S.η ω) i.Θ i.F0 r)

end Lemma68ExitAe
end MatedCRT
