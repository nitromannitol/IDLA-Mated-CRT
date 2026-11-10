import MatedCRT.FirstPass.S4S6c.HoneGoodEvent68
import MatedCRT.FirstPass.S4S6c.ExitAe68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S3t.WalkAdjacency
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Almost-sure forms of the good-event dischargers (fp-S4S6c-good-event-ae, z10)

`HoneGoodEvent68.lean` discharges the binders `hεα`, `hεmass`, `hsc`, `hgood`, `hpos` of `shellOneTest_of_direct`
pointwise: the per-path inputs `hPath` (consecutive cells meet, the start cell meets the frontier, the killed exit is
finite) are assumed for every path of the prefix set. Under the walk law `srwLaw m s0` these inputs hold only almost
surely. This file gives the almost sure forms, in the shape of `shellOneTest_of_direct_ae` (HoneLeafAe68.lean:374):
`∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0, x ∈ prefixSet … → P k x`, with `k ≤ n` throughout.

* `walk_inputs_ae`: the three per-path inputs hold almost surely under `srwLaw m s0`. Adjacency:
  `MatedCRT.TruncatedLaws.srwLaw_cells_meet_ae` (WalkAdjacency.lean:41, from the edge condition `hedge`). Start:
  `MatedCRT.srwLaw_ae_start` (RandomWalk.lean:16), so the start cell is `cell ε η s0`; its frontier condition is the named
  input `hst`. Killed exit: `ExitAe68.ae_exit_ne_top_of_bounded` with `GreenTest68.vExitTime_le_of_subset`, as in
  HoneSetup68.lean:126-133.
* `hεα_ae`, `hεmass_ae`, `hsc_ae_of_volC`, `hsc_ae_threshold`, `hpos_ae`, `hgood_ae`: the pointwise dischargers of
  HoneGoodEvent68 applied at almost every path. `hEl_ae_of_walk` gives the eligibility of the shell centres `hEl` from
  `walk_inputs_ae` through `shellCentre_eligible_of_walk` (ShellHde68.lean:215).

Named inputs (not in the corrected paper's statements; see the report): `hst`, `hedge`, `hlf`, `hcons`, `hp`, `hF0`
(the environment and start of the walk, as in HoneSetup68.lean:112-133), `hεs` (the explicit ε-threshold of
`hsc_ae_threshold`), `hfull` (full support of the measure), `hsel`, `hZ`, `hVolC`, `hRr`.

Terminology: good annuli and good radii (Armstrong-Kuusi-Mourrat), Armitage-Gardiner (balls and annuli).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
namespace Lemma68HoneGoodEventAe

open Lemma68Window Lemma68Omega Lemma68ShellChain Lemma68WindowRf
open MatedCRT.Lemma68HoneGoodEvent

variable {γ ρc : ℝ}

/-- **The almost sure walk inputs of `hEl`.** Under `srwLaw m s0`, almost surely: consecutive cells meet
(`srwLaw_cells_meet_ae`, from the edge condition `hedge`), the start is `s0` (`srwLaw_ae_start`) so the start cell is
`cell ε η s0` and meets the frontier by the named input `hst`, and the killed exit is finite
(`ExitAe68.ae_exit_ne_top_of_bounded`, then `GreenTest68.vExitTime_le_of_subset` on the killed set `⊆ meetVerts`). -/
theorem walk_inputs_ae {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {m : ℤ → ℤ → ℕ} (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (s0 : ℤ)
    {Θ F0 : Finset ℤ} {ρ r : ℝ} (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (hst : (cell ε η s0 ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty) :
    ∀ᵐ x ∂srwLaw m s0, (∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty) ∧
      (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty ∧
      vExitTime (Lemma68Admissible.killed ε η Θ F0 r) x ≠ ⊤ := by
  have hU : Bornology.IsBounded (Metric.ball (0 : ℂ) ρ) := Metric.isBounded_ball
  filter_upwards [MatedCRT.TruncatedLaws.srwLaw_cells_meet_ae hε.le hedge s0,
    MatedCRT.srwLaw_ae_start m s0, ExitAe68.ae_exit_ne_top_of_bounded hε hη hp hlf hcons hU s0]
    with x hadj hx0 hx
  refine ⟨hadj, ?_, ?_⟩
  · rw [hx0]
    exact hst
  · refine ne_top_of_le_ne_top hx (GreenTest68.vExitTime_le_of_subset ?_ x)
    intro v hv
    have hvF : v ∈ (↑F0 : Set ℤ) := Finset.mem_coe.2 hv.1
    rw [hF0] at hvF
    have hvF' : (cell ε η v ∩ Metric.ball (0 : ℂ) ρ).Nonempty := hvF
    obtain ⟨p, hp1, hp2⟩ := hvF'
    exact ⟨p, subset_closure hp1, hp2⟩

/-- **`hεα` almost surely.** The a.s. form of `hεα_of_radius` (HoneGoodEvent68.lean:50): on the prefix set,
`ε^α ≤ R/100` for `R = Rf (shellCentre)`, from `R ≥ r² ≥ 100 ε^{2ω}` and `α ≥ 2ω`. -/
theorem hεα_ae (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 2 * K.ω ≤ α) (hrε : 10 * ε ^ K.ω ≤ r)
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ Rf (shellCentre ε η Kset r s d k x) / 100 := by
  intro k hk
  filter_upwards [hRr k hk] with x hx hmem
  have hR := (hx hmem).1
  have hα' : ε ^ α ≤ ε ^ (2 * K.ω) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hα
  have hsq := eps_pow_two_le_sq hε hrε
  linarith

/-- **`hεmass` almost surely.** The a.s. form of `hεmass_of_radius` (HoneGoodEvent68.lean:65): on the prefix set,
`ε^α ≤ (R/4)^βm` from `R ≥ r² ≥ 100 ε^{2ω}` and `α ≥ 2ω βm`. -/
theorem hεmass_ae (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 2 * K.ω * K.βm ≤ α) (hrε : 10 * ε ^ K.ω ≤ r)
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm := by
  intro k hk
  filter_upwards [hRr k hk] with x hx hmem
  have hR := (hx hmem).1
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
  have hb2 : (r ^ 2 / 100) ^ K.βm ≤ (Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg r]) hβ0
  linarith

/-- **`hsc` almost surely (lower volume bound at the exit ball, deterministic smallness form).** The a.s. form of
`hsc_of_volC` (HoneGoodEvent68.lean:91): on the prefix set `4 ε^α ≤ μ(B_{c₀R}(exit vertex)).toReal`, from the a.s.
lower volume bound `hVolC` at radius `c₀ R` and `hεc : 4 ε^α ≤ (c₀ r²)^βm`. -/
theorem hsc_ae_of_volC (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hεc : 4 * ε ^ α ≤ (K.c0 * r ^ 2) ^ K.βm)
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm)
          ≤ μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x)))) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal := by
  intro k hk
  filter_upwards [hRr k hk, hVolC k hk] with x hx hV hmem
  have hR := (hx hmem).1
  have hβ0 : 0 ≤ K.βm := by
    have h1 := K.hβ
    have h2 : 0 ≤ (2 + γ) ^ 2 / 2 := by positivity
    linarith
  have hpow : (K.c0 * r ^ 2) ^ K.βm ≤ (K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm :=
    Real.rpow_le_rpow (mul_nonneg K.hc0.le (sq_nonneg r))
      (mul_le_mul_of_nonneg_left hR K.hc0.le) hβ0
  have hle := (ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top.ne)).1 (hV hmem)
  linarith

/-- **`hsc` almost surely, with the explicit ε-threshold.** The a.s. form of `hsc_of_volC_threshold`
(HoneGoodEvent68.lean:223): the smallness `hεc` is derived from `2 ω βm < α` and the threshold
`ε ≤ ((100 c₀)^βm / 4)^(1/(α - 2 ω βm))`, which is a deterministic input (not an a.s. event). -/
theorem hsc_ae_threshold (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d α : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hε : 0 < ε) (hrε : 10 * ε ^ K.ω ≤ r) (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm)
          ≤ μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x)))) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal :=
  hsc_ae_of_volC K (hεc_of_threshold K hε hrε hα hεs) hRr hVolC

/-- **`hpos` almost surely (full support).** The a.s. form of `hpos_of_fullSupport` (HoneGoodEvent68.lean:142): under
full support of `μ`, the annulus infimum at the walk radius is positive on the prefix set. -/
theorem hpos_ae (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hfull : ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < μ (ball w t))
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hr : 0 < r) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        0 < ⨅ w ∈ annulus (Z k x) (Rf (shellCentre ε η Kset r s d k x))
          (2 * Rf (shellCentre ε η Kset r s d k x)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k x))) := by
  intro k hk
  filter_upwards [hRr k hk] with x hx hmem
  have hR : 0 < Rf (shellCentre ε η Kset r s d k x) :=
    lt_of_lt_of_le (by positivity) (hx hmem).1
  exact pos_iInf_annulus_ball hfull hR K.hc0

/-- **Eligibility of the shell centres almost surely, from the walk.** The a.s. form of `hEl_le_of_walkPath`
(HoneGoodEvent68.lean:279): with `Kset = fillCells Θ` and `s = d^a`, the almost sure walk inputs of
`walk_inputs_ae` give `shellCentre k x ∈ shortEligible ρ d a` for `k ≤ n` (via `shellCentre_eligible_of_walk`,
ShellHde68.lean:215). -/
theorem hEl_ae_of_walk {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a s : ℝ} {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ}
    {m : ℤ → ℤ → ℕ} {s0 : ℤ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20) (hs : s = d ^ a)
    (hmesh : CellDiamLe ε η (d / 100) Set.univ)
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    (hPath : ∀ᵐ x ∂srwLaw m s0, (∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty) ∧
      (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty ∧
      vExitTime (Lemma68Admissible.killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k) τU →
        shellCentre ε η (fillCells ε η ↑Θ) r s d k x ∈ shortEligible ρ d a := by
  intro k hk
  filter_upwards [hPath] with x hx _
  obtain ⟨hadj, hst, hτ⟩ := hx
  exact shellCentre_eligible_of_walk hη hε hr hrρ hd hds hs4 hNs hs hmesh hF0 h0 hKb hRf hadj hst hτ k hk

/-- **`hgood` almost surely on the shells `k ≤ n`.** The a.s. form of `hgood_of_selector_le`
(HoneGoodEvent68.lean:244): the annulus centre is the shell centre (`hZ`), the shell centre is an eligible centre (the
almost sure `hEl`, e.g. from `hEl_ae_of_walk`), and the walk radius is a good radius at every eligible centre (`hsel`). -/
theorem hgood_ae (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {r s d a ρ C_good : ℝ}
    {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {μ : Measure ℂ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {m : ℤ → ℤ → ℕ} {s0 : ℤ} {n : ℕ}
    (hsel : ∀ z ∈ shortEligible ρ d a, IsGoodAnnulusEvent μ K.c0 C_good (Rf z) z)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        shellCentre ε η Kset r s d k x ∈ shortEligible ρ d a)
    (hZ : ∀ k ω, Z k ω = shellCentre ε η Kset r s d k ω) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k x)) (Z k x) := by
  intro k hk
  filter_upwards [hEl k hk] with x hx hmem
  rw [hZ k x]
  exact hsel _ (hx hmem)

end Lemma68HoneGoodEventAe
end MatedCRT

#print axioms MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hεα_ae
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hεmass_ae
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hsc_ae_of_volC
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hsc_ae_threshold
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hpos_ae
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hEl_ae_of_walk
#print axioms MatedCRT.Lemma68HoneGoodEventAe.hgood_ae
