import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68

/-!
# Dischargers of the leaf binders of `shellOneTest_of_direct` (z12, fp-S4S6c-hone-radii)

Leaf: `shellOneTest_of_direct` (S4S6c/ShellHoneInst68.lean:53). Each lemma below concludes the binder type of that
theorem, with the substitution stated in its docstring. Hypotheses that are not in the leaf are listed explicitly.

* `windowRfT_rangeShortEligible`: range of the window radius `windowRfT` on `shortEligible ρ d a` (every environment).
* `hRr_of_centre`, `hRr_of_centre_dyadic`: binder `hRr` from the range of `Rf` on `shortEligible` and the walk-centre check.
* `hRmin_of_hRr`: binder `hRmin` at `rmin := K.c0 * r ^ 2`.
* `hεcell_of_scale`: binder `hεcell` at `rmin := K.c0 * r ^ 2`, from the scale range `10 ε^ω ≤ r` and an ε-smallness.

Terminology: Armstrong-Kuusi-Mourrat (scale range, good annuli), Armitage-Gardiner (exit radius of a ball).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneRadii

open MatedCRT.Lemma68Window MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent MatedCRT.Lemma68Omega

/-- Range of the total window radius on the eligible set, for every environment and every `ω`:
`windowRfT_bounds` (ShellWindowRf68.lean:65) restated as the range hypothesis `hRf` of `hRr_of_centre`. -/
theorem windowRfT_rangeShortEligible {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (ha : a ≤ 1) (ω : Ω) :
    ∀ z ∈ shortEligible ρ d a, d ≤ windowRfT μ ρ a c₀ C d ω z ∧ windowRfT μ ρ a c₀ C d ω z ≤ d ^ a :=
  fun _ hz => windowRfT_bounds μ ρ a c₀ C d hd0 hd1 ha ω hz

/-- **Binder `hRr` of `shellOneTest_of_direct` (ShellHoneInst68.lean:70), reduced to the walk-centre check.**
The conclusion is `hRr` verbatim. The inputs are: the range `hRf` of the radius function on the eligible set (for
`Rf = windowRfT μ ρ a c₀ C d ω₀` this is `windowRfT_rangeShortEligible`), the lower bound `r ^ 2 ≤ d` (`dyadicD_mem`),
`d ≤ 1`, `0 ≤ a`, and the walk-centre check `hcentre` (the shell centres of walks in the prefix set lie in
`shortEligible ρ d a`; the candidate source is `shell_fin_of_path`, S4S6c/ShellHde68.lean:209, which also needs the
mesh hypothesis `CellDiamLe` (binder `hmesh`, routed 55b) and the walk hypotheses `hadj`, `hst`, `hτ`). -/
theorem hRr_of_centre {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} (Kset : Set ℂ) (Rf : ℂ → ℝ)
    {r s d ρ a : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (ha0 : 0 ≤ a) (hdr : r ^ 2 ≤ d)
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    (hcentre : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      shellCentre ε η Kset r s d k ω ∈ shortEligible ρ d a) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1 := by
  intro k ω hω
  obtain ⟨h1, h2⟩ := hRf _ (hcentre k ω hω)
  exact ⟨hdr.trans h1, h2.trans (Real.rpow_le_one hd0.le hd1 ha0)⟩

/-- `hRr_of_centre` at the dyadic scale `d = dyadicD r` (the shell chain's choice): `r ^ 2 ≤ dyadicD r` and
`dyadicD r ≤ 1` come from `dyadicD_mem` and `dyadicD_le_one`. -/
theorem hRr_of_centre_dyadic {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} (Kset : Set ℂ) (Rf : ℂ → ℝ)
    {r s ρ a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ha0 : 0 ≤ a)
    (hRf : ∀ z ∈ shortEligible ρ (dyadicD r) a, dyadicD r ≤ Rf z ∧ Rf z ≤ (dyadicD r) ^ a)
    (hcentre : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
        (shellExit ε η Kset r s (dyadicD r) Rf k) τU,
      shellCentre ε η Kset r s (dyadicD r) k ω ∈ shortEligible ρ (dyadicD r) a) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
        (shellExit ε η Kset r s (dyadicD r) Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s (dyadicD r) k ω) ∧
        Rf (shellCentre ε η Kset r s (dyadicD r) k ω) ≤ 1 :=
  hRr_of_centre Kset Rf (dyadicD_pos r) (dyadicD_le_one r) ha0 (dyadicD_mem hr hr1).1 hRf hcentre

/-- **Binder `hRmin` of `shellOneTest_of_direct` (ShellHoneInst68.lean:77) at `rmin := K.c0 * r ^ 2`.** From the
lower bound `r ^ 2 ≤ Rf` of `hRr` and `0 ≤ K.c0`. -/
theorem hRmin_of_hRr {γ ρc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) {r s d : ℝ}
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      K.c0 * r ^ 2 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := by
  intro k ω hω
  exact mul_le_mul_of_nonneg_left (hRr k ω hω).1 K.hc0.le

/-- **Binder `hεcell` of `shellOneTest_of_direct` (ShellHoneInst68.lean:109) at `rmin := K.c0 * r ^ 2`, conditional.**
The leaf binder is `ε ^ (2/(2+γ)^2 - ζc) ≤ rmin / 100`. The leaf hypotheses do not imply it (they give only `ε ≤ 16 c0`):
it needs `ε ^ (2/(2+γ)^2 - ζc) ≤ c0 r ^ 2 / 100`, i.e. `ε` small relative to the scale `r`. It holds once the scale range `10 ε^ω ≤ r` of Lemma 6.8 (corrected paper, lemma:constant-order-lower-bound-div,
corrected draft l.2788-2790, `r ∈ [10 ε^ω, δ]`) is assumed and `ε` is small enough that `ε ^ (2/(2+γ)^2 - ζc - 2ω) ≤ c0`
(hεsm). The last needs `2 ω < 2/(2+γ)^2 - ζc` (NOT in the sources: the relation between the Lemma 6.8 exponent `ω` and
the cell exponent of `hCellGood`). -/
theorem hεcell_of_scale {γ ρc : ℝ} (K : Constants68 γ ρc) {ε r ζc : ℝ} (hε : 0 < ε)
    (hrε : 10 * ε ^ K.ω ≤ r)
    (hεsm : ε ^ (2 / (2 + γ) ^ 2 - ζc - 2 * K.ω) ≤ K.c0) :
    ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ K.c0 * r ^ 2 / 100 := by
  have hc0 : 0 < K.c0 := K.hc0
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  have hsq : ε ^ (2 * K.ω) = (ε ^ K.ω) ^ 2 := by
    rw [show 2 * K.ω = K.ω * 2 by ring, Real.rpow_mul hε.le, Real.rpow_two]
  have hsqr : (10 * ε ^ K.ω) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hrε 2
  have hr2 : ε ^ (2 * K.ω) ≤ r ^ 2 / 100 := by
    rw [hsq]; nlinarith [hsqr]
  have hpos : 0 ≤ ε ^ (2 * K.ω) := Real.rpow_nonneg hε.le _
  have hsplit : ε ^ (2 / (2 + γ) ^ 2 - ζc)
      = ε ^ (2 * K.ω) * ε ^ (2 / (2 + γ) ^ 2 - ζc - 2 * K.ω) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  calc ε ^ (2 / (2 + γ) ^ 2 - ζc)
      = ε ^ (2 * K.ω) * ε ^ (2 / (2 + γ) ^ 2 - ζc - 2 * K.ω) := hsplit
    _ ≤ ε ^ (2 * K.ω) * K.c0 := mul_le_mul_of_nonneg_left hεsm hpos
    _ ≤ (r ^ 2 / 100) * K.c0 := mul_le_mul_of_nonneg_right hr2 hc0.le
    _ = K.c0 * r ^ 2 / 100 := by ring

end Lemma68HoneRadii
end MatedCRT

#print axioms MatedCRT.Lemma68HoneRadii.windowRfT_rangeShortEligible
#print axioms MatedCRT.Lemma68HoneRadii.hRr_of_centre
#print axioms MatedCRT.Lemma68HoneRadii.hRr_of_centre_dyadic
#print axioms MatedCRT.Lemma68HoneRadii.hRmin_of_hRr
#print axioms MatedCRT.Lemma68HoneRadii.hεcell_of_scale
