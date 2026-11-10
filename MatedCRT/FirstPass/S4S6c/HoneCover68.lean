import MatedCRT.FirstPass.S4S6c.ShellConstOrder68
import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6r.Amplification

/-!
# The deterministic annulus cover behind the hypothesis `hN` of `shellOneTest_of_direct` (fp-S4S6c-hone-cover, z1)

The binder `hN` of `shellOneTest_of_direct` (`S4S6c/ShellHoneInst68.lean`) asks that, for every shell `k` and every
environment `ω` in the prefix set, every open annulus `𝔸_{R',2R'}(z')` is covered by at most `N_cov` balls of radius
`R'` centred in the annulus. Nothing about `k`, `ω`, the configuration `A`, the stopping time `τU` or the radius
function `Rf` enters this covering property: it is the Euclidean statement `AnnulusCover68 N_cov`
(`S4S6c/ShellConstOrder68.lean`, the covering by compactness of the closed unit annulus and scaling; annulus notation
of Armitage-Gardiner, `HarmonicBalls.annulus`).

Route. `hN_of_annulusCover68` is the binder `hN` with `N_cov` a free count carrying `AnnulusCover68 N_cov`; the
discharge is the projection of that cover at the radius `R'` and centre `z'`, the shell index and the environment
being ignored. `hN_shellNcov68` is the same statement at the universal count `shellNcov68` of ShellConstOrder68,
which is the count used by the outer statement through `hCw`.

Terminology: Armstrong-Kuusi-Mourrat (annular covering behind the one-test bound), Armitage-Gardiner (Euclidean
annuli). No hypothesis is added.
-/

open Set Metric
open MatedCRT.Lemma68Window
open scoped Classical

namespace MatedCRT
namespace Lemma68HoneCover

/-- **`hN` discharged by the annulus cover (fp-S4S6c-hone-cover).** For any count `N_cov` with `AnnulusCover68 N_cov`,
the binder `hN` of `shellOneTest_of_direct` holds for the walk-centred shells: every annulus `𝔸_{R',2R'}(z')` with
`R' > 0` is covered by a finite set `t` of at most `N_cov` centres lying in the annulus, with the balls of radius `R'`. -/
theorem hN_of_annulusCover68 (ε : ℝ) (η : ℝ → ℂ) (Kset : Set ℂ) (r s d : ℝ) (Rf : ℂ → ℝ) (A : Set ℤ)
    (τU : (ℕ → ℤ) → ℕ∞) {N_cov : ℕ} (hcov : Lemma68ConstOrder.AnnulusCover68 N_cov) :
    ∀ k : ℕ, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
        (Lemma68Omega.shellExit ε η Kset r s d Rf k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ HarmonicBalls.annulus z' R' (2 * R')) ∧
        HarmonicBalls.annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R' :=
  fun _ _ _ R' z' hR => hcov R' z' hR

/-- **`hN` at the universal count (fp-S4S6c-hone-cover).** The binder `hN` of `shellOneTest_of_direct` at the count
`N_cov := shellNcov68` (ShellConstOrder68), which is the count fixed in the constants of the one-test bound. -/
theorem hN_shellNcov68 (ε : ℝ) (η : ℝ → ℂ) (Kset : Set ℂ) (r s d : ℝ) (Rf : ℂ → ℝ) (A : Set ℤ)
    (τU : (ℕ → ℤ) → ℕ∞) :
    ∀ k : ℕ, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
        (Lemma68Omega.shellExit ε η Kset r s d Rf k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ Lemma68ConstOrder.shellNcov68 ∧
        (∀ v ∈ t, v ∈ HarmonicBalls.annulus z' R' (2 * R')) ∧
        HarmonicBalls.annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R' :=
  hN_of_annulusCover68 ε η Kset r s d Rf A τU Lemma68ConstOrder.shellNcov68_spec

end Lemma68HoneCover
end MatedCRT

#print axioms MatedCRT.Lemma68HoneCover.hN_of_annulusCover68
#print axioms MatedCRT.Lemma68HoneCover.hN_shellNcov68
