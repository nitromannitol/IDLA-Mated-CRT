import MatedCRT.FirstPass.S4S6c.HoneCellR68

/-!
# Discharge of the prefix binder `hRcell`

The cell-control binder `hRcell` of `hone_exitQ_walk_of_env_direct_ae` (HoneLeafAe68.lean) asks that the shell radius
satisfies `R_k / 4 < rhoCell - rho_c` on the prefix set, almost surely for `k ≤ n`. The argument
 (l.335-348) gives it from two facts:

* the selected test radius satisfies `R_k ≤ d ^ a` (`d = dyadicD r`, `a = shortExp ζ`), because the centre is
  eligible (`shortEligible`) and the radius selector obeys `Rf z ≤ d ^ a` there (`windowRfT_rangeShortEligible`
  in the B1 instance); the centre eligibility is almost sure on the prefix (`HoneGoodEventAe68.hEl_ae_of_walk`);
* the deterministic cutoff `d ^ a < rhoCell - rho_c` (a hypothesis here).

Nothing else is used: `R_k / 4 ≤ R_k^+ / 4 ≤ d ^ a < rhoCell - rho_c` with `0 ≤ d ^ a`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
namespace Lemma68RcellDischarge

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- A radius with `0 ≤ s`, `R ≤ s` and `s < g` satisfies `R / 4 < g`. -/
theorem div4_lt_of_le_cutoff {R s g : ℝ} (hs0 : 0 ≤ s) (hRs : R ≤ s) (hsg : s < g) : R / 4 < g := by
  linarith

/-- The a.s. radius bound on the prefix: the radius selector's bound `Rf z ≤ d ^ aW` on the eligible centres
(`hRf`) and the a.s. centre eligibility on the prefix (`hEl`, e.g. `HoneGoodEventAe68.hEl_ae_of_walk`). -/
theorem radius_le_of_eligible_ae {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {Rf : ℂ → ℝ} {A : Set ℤ}
    {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ} {m : ℤ → ℤ → ℕ} {a0 : ℤ} {r sc d ρ aW : ℝ}
    (hRf : ∀ z ∈ shortEligible ρ d aW, Rf z ≤ d ^ aW)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r sc d Rf k) τU →
        shellCentre ε η Kset r sc d k x ∈ shortEligible ρ d aW) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r sc d Rf k) τU →
        Rf (shellCentre ε η Kset r sc d k x) ≤ d ^ aW :=
  fun k hk => (hEl k hk).mono fun _ hx hP => hRf _ (hx hP)

/-- **Binder `hRcell` of `hone_exitQ_walk_of_env_direct_ae`, discharged.** From the radius bound
(`radius_le_of_eligible_ae`), `0 ≤ d ^ aW` (`0 < d`, `0 ≤ aW`) and the cutoff `d ^ aW < g` with
`g = rhoCell - rho_c` (the hypothesis `hcut`). -/
theorem hRcell_of_eligible {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {Rf : ℂ → ℝ} {A : Set ℤ}
    {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ} {m : ℤ → ℤ → ℕ} {a0 : ℤ} {r sc d ρ aW g : ℝ}
    (hd : 0 < d)
    (hRf : ∀ z ∈ shortEligible ρ d aW, Rf z ≤ d ^ aW)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r sc d Rf k) τU →
        shellCentre ε η Kset r sc d k x ∈ shortEligible ρ d aW)
    (hcut : d ^ aW < g) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r sc d Rf k) τU →
        Rf (shellCentre ε η Kset r sc d k x) / 4 < g :=
  fun k hk => (radius_le_of_eligible_ae hRf hEl k hk).mono fun _ hx hP =>
    div4_lt_of_le_cutoff (Real.rpow_nonneg hd.le aW) (hx hP) hcut

end Lemma68RcellDischarge
end MatedCRT

#print axioms MatedCRT.Lemma68RcellDischarge.radius_le_of_eligible_ae
#print axioms MatedCRT.Lemma68RcellDischarge.hRcell_of_eligible
