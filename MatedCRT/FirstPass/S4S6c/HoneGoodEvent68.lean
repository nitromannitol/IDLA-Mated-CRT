import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S4S6c.HoneInputsDirect

/-!
# Discharges of the good-event and scale binders of `shellOneTest_of_direct` (fp-S4S6c-hone-good-event, z10)

The binders `hεα`, `hεmass`, `hsc`, `hgood`, `hpos` of `shellOneTest_of_direct` (ShellHoneInst68.lean) are the
good-event and scale inputs at the walk radii `R = Rf (shellCentre k ω)` on the prefix set. Each discharge below has
conclusion EXACTLY the binder type; the extra hypotheses are the explicit inputs of the paper's Lemma 6.8 (corrected
proof [C26], the mesh preparation `eq:c26-mesh-preparation`, the choice `eq:c26-choice-omega`, the short-window good
radius `eq:c26-short-window-radius`), which the outer statement does not carry:

* `hrε : 10 * ε ^ ω ≤ r` (the range `r ∈ [10 ε^ω, δ]` of Lemma 6.8, `ShellOneTestOrderAeStmt`);
* `hα : 2 * ω ≤ α`, resp. `2 * ω * βm ≤ α` (the exponent relation `2ω < α_e/β` of `eq:c26-choice-omega`);
* `hεc : 4 * ε ^ α ≤ (c₀ r²)^βm` (the deterministic smallness "ε small" of `eq:c26-mesh-preparation`);
* `hfull` (full support of the LQG measure, every ball has positive mass);
* `hEl` (the shell centre is an eligible centre of the short window: `shell_fin_of_path`, ShellHde68.lean:215) and
  `hZ` (the annulus centre `Z` is the shell centre), and the selector property of the window radius on eligible
  centres (`windowRf_spec`, ShellWindowRf68.lean:37, on the complement of `badWindowOf`).

Terminology: good annuli and good radii (Armstrong-Kuusi-Mourrat), LQG measure of full support (Duplantier-Sheffield),
Armitage-Gardiner (balls and annuli).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal
open HarmonicBalls (annulus)

namespace MatedCRT
namespace Lemma68HoneGoodEvent

open Lemma68Window Lemma68Omega Lemma68ShellChain Lemma68WindowRf

variable {γ ρc : ℝ}

/-- **`ε^{2ω} ≤ r²/100`** from the range `10 ε^ω ≤ r` of Lemma 6.8. -/
theorem eps_pow_two_le_sq {ε r ω0 : ℝ} (hε : 0 < ε) (hrε : 10 * ε ^ ω0 ≤ r) :
    ε ^ (2 * ω0) ≤ r ^ 2 / 100 := by
  have h0 : 0 ≤ ε ^ ω0 := (Real.rpow_pos_of_pos hε ω0).le
  have h1 : ε ^ (2 * ω0) = (ε ^ ω0) ^ 2 := by
    rw [show (2 : ℝ) * ω0 = ω0 * 2 by ring, Real.rpow_mul hε.le, Real.rpow_two]
  have h2 : ε ^ ω0 ≤ r / 10 := by linarith
  calc ε ^ (2 * ω0) = (ε ^ ω0) ^ 2 := h1
    _ ≤ (r / 10) ^ 2 := pow_le_pow_left₀ h0 h2 2
    _ = r ^ 2 / 100 := by ring

/-- **The mesh-scale discharge `hεα`.** On the prefix set, `ε^α ≤ R/100` for the walk radius `R = Rf (shellCentre)`,
from `R ≥ r²` (`hRr`, the outer binder) and `ε^α ≤ ε^{2ω} ≤ r²/100` (`eq:c26-mesh-preparation`, `d ≥ r² ≥ 100 ε^{2ω}`). -/
theorem hεα_of_radius (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 2 * K.ω ≤ α) (hrε : 10 * ε ^ K.ω ≤ r)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ε ^ α ≤ Rf (shellCentre ε η Kset r s d k ω) / 100 := by
  intro k ω hω
  have hR := (hRr k ω hω).1
  have hα' : ε ^ α ≤ ε ^ (2 * K.ω) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hα
  have hsq := eps_pow_two_le_sq hε hrε
  linarith

/-- **The mass-scale discharge `hεmass`.** On the prefix set, `ε^α ≤ (R/4)^βm` for `R = Rf (shellCentre)`, from
`R ≥ r² ≥ 100 ε^{2ω}` and `α ≥ 2ω βm` (the exponent relation of `eq:c26-choice-omega`). -/
theorem hεmass_of_radius (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 2 * K.ω * K.βm ≤ α) (hrε : 10 * ε ^ K.ω ≤ r)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k ω) / 4) ^ K.βm := by
  intro k ω hω
  have hR := (hRr k ω hω).1
  have hβ0 : 0 ≤ K.βm := by
    have h1 := K.hβ
    have h2 : 0 ≤ (2 + γ) ^ 2 / 2 := by positivity
    linarith
  have hsq := eps_pow_two_le_sq hε hrε
  have hpow0 : 0 ≤ ε ^ (2 * K.ω) := (Real.rpow_pos_of_pos hε _).le
  have hα' : ε ^ α ≤ ε ^ (2 * K.ω * K.βm) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hα
  have hmul : ε ^ (2 * K.ω * K.βm) = (ε ^ (2 * K.ω)) ^ K.βm := Real.rpow_mul hε.le _ _
  have hb1 : (ε ^ (2 * K.ω)) ^ K.βm ≤ (r ^ 2 / 100) ^ K.βm :=
    Real.rpow_le_rpow hpow0 hsq hβ0
  have hb2 : (r ^ 2 / 100) ^ K.βm ≤ (Rf (shellCentre ε η Kset r s d k ω) / 4) ^ K.βm :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg r]) hβ0
  linarith

/-- **The good-event discharge `hsc` (lower volume bound at the exit ball).** On the prefix set,
`4 ε^α ≤ μ(B_{c₀R}(exit vertex)).toReal`, from the lower volume bound `hVolC` of the outer statement (at radius
`c₀ R`) and the deterministic smallness `hεc : 4 ε^α ≤ (c₀ r²)^βm` (`eq:c26-mesh-preparation`, third line). -/
theorem hsc_of_volC (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hεc : 4 * ε ^ α ≤ (K.c0 * r ^ 2) ^ K.βm)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ^ K.βm)
        ≤ μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  intro k ω hω
  have hR := (hRr k ω hω).1
  have hβ0 : 0 ≤ K.βm := by
    have h1 := K.hβ
    have h2 : 0 ≤ (2 + γ) ^ 2 / 2 := by positivity
    linarith
  have hpow : (K.c0 * r ^ 2) ^ K.βm ≤ (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ^ K.βm :=
    Real.rpow_le_rpow (mul_nonneg K.hc0.le (sq_nonneg r))
      (mul_le_mul_of_nonneg_left hR K.hc0.le) hβ0
  have hV := hVolC k ω hω
  have hle := (ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top.ne)).1 hV
  linarith

/-- **Positivity of the annulus infimum (full support).** If every ball of positive radius has positive `μ`-mass,
then `inf_{w ∈ A_{R,2R}(z)} μ(B_{c₀R}(w)) > 0`: a finite cover of `closedBall z (2R)` by balls of radius `c₀R/2`
gives, for each `w` in the annulus, a cover ball `B_x(c₀R/2) ⊆ B_w(c₀R)`; the minimum over the finite set is positive. -/
theorem pos_iInf_annulus_ball {μ : Measure ℂ} (hfull : ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < μ (ball w t))
    {z : ℂ} {R c0 : ℝ} (hR : 0 < R) (hc0 : 0 < c0) :
    0 < ⨅ w ∈ annulus z R (2 * R), μ (ball w (c0 * R)) := by
  have hh : 0 < c0 * R / 2 := by positivity
  obtain ⟨T, hTs, hTfin, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall z (2 * R)) hh
  have : Finite T := hTfin.to_subtype
  obtain ⟨x0, hx0T, -⟩ := Set.mem_iUnion₂.1 (hcov (mem_closedBall_self (by linarith : (0 : ℝ) ≤ 2 * R)))
  have : Nonempty T := ⟨⟨x0, hx0T⟩⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min (fun x : T => μ (ball (x : ℂ) (c0 * R / 2)))
  have hcpos : 0 < μ (ball (x₀ : ℂ) (c0 * R / 2)) := hfull _ _ hh
  have key : ∀ w ∈ annulus z R (2 * R), μ (ball (x₀ : ℂ) (c0 * R / 2)) ≤ μ (ball w (c0 * R)) := by
    intro w hw
    have hwb : w ∈ closedBall z (2 * R) := ball_subset_closedBall hw.1
    obtain ⟨x, hxT, hwx⟩ := Set.mem_iUnion₂.1 (hcov hwb)
    have hsub : ball (x : ℂ) (c0 * R / 2) ⊆ ball w (c0 * R) := by
      intro y hy
      rw [mem_ball] at hy hwx ⊢
      linarith [dist_triangle y (x : ℂ) w, dist_comm (x : ℂ) w]
    exact (hx₀ ⟨x, hxT⟩).trans (measure_mono hsub)
  exact lt_of_lt_of_le hcpos (le_iInf₂ fun w hw => key w hw)

/-- **The positivity discharge `hpos`.** Under full support of `μ`, the annulus infimum at the walk radius is positive. -/
theorem hpos_of_fullSupport (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hfull : ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < μ (ball w t))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1) (hr : 0 < r) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
        (2 * Rf (shellCentre ε η Kset r s d k ω)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) := by
  intro k ω hω
  have hR : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (by positivity) (hRr k ω hω).1
  exact pos_iInf_annulus_ball hfull hR K.hc0

/-- **The selector property of the window radius.** Off the window event, the window radius of every eligible
centre is a good annulus radius (`windowRf_spec`, ShellWindowRf68.lean:37). -/
theorem selector_of_not_bad {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (hω : ω ∉ badWindowOf μ ρ a c₀ C d) :
    ∀ z ∈ shortEligible ρ d a, IsGoodAnnulusEvent (μ ω) c₀ C (windowRf μ c₀ C a d ω z) z :=
  fun _ hz => (windowRf_spec μ ρ a c₀ C d ω hω hz).2

/-- **The good-event discharge `hgood`.** On the prefix set the annulus centre is the shell centre `Z k ω =
shellCentre k ω` (`hZ`), the shell centre is an eligible centre of the short window (`hEl`, from the path lemma
`shell_fin_of_path`, ShellHde68.lean:215), and the walk radius is a good radius at every eligible centre (`hsel`, the
selector property of `selector_of_not_bad`). -/
theorem hgood_of_selector (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d a ρ C_good : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hsel : ∀ z ∈ shortEligible ρ d a, IsGoodAnnulusEvent μ K.c0 C_good (Rf z) z)
    (hEl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      shellCentre ε η Kset r s d k ω ∈ shortEligible ρ d a)
    (hZ : ∀ k ω, Z k ω = shellCentre ε η Kset r s d k ω) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω) := by
  intro k ω hω
  rw [hZ k ω]
  exact hsel _ (hEl k ω hω)

end Lemma68HoneGoodEvent
end MatedCRT

#print axioms MatedCRT.Lemma68HoneGoodEvent.hεα_of_radius
#print axioms MatedCRT.Lemma68HoneGoodEvent.hεmass_of_radius
#print axioms MatedCRT.Lemma68HoneGoodEvent.hsc_of_volC
#print axioms MatedCRT.Lemma68HoneGoodEvent.hpos_of_fullSupport
#print axioms MatedCRT.Lemma68HoneGoodEvent.hgood_of_selector
#print axioms MatedCRT.Lemma68HoneGoodEvent.selector_of_not_bad
