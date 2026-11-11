import MatedCRT.FirstPass.S4S6c.HoneSetup239_68
import MatedCRT.FirstPass.S4S6c.HoneGoodEventAe68

/-!
# The eligibility binder `hEl` at one environment

`shellOneTest_at_of_goodEnv` (B1Assembly68.lean:567) takes the eligibility of the shell centres as the binder `hEl`
(B1Assembly68.lean:~600): at one environment `ω`, under `FullAdmAt`, for every shell `k ≤ shellCount - 1`, almost surely
in the walk `x ∂srwLaw (S.mult ε ω) i.a`, if `x` lies in the leaf prefix set, then the shell centre is short-eligible
`shellCentre … k x ∈ shortEligible ρ (dyadicD r) (shortExp ζ)`.

This file produces `hEl` at ONE fixed environment `ω` (no almost-sure quantifier in `ω`), by the same chain as
`hRr_fixedOmega` (HoneSetup68.lean:75): the walk inputs of `walk_inputs_ae` (HoneGoodEventAe68.lean), the setup
discharges of `hRr_fixedOmega` (the shell count `≥ 1`, `hNs`, `hs4`, `hds`, the window range), and the eligibility
`hEl_ae_of_walk` (HoneGoodEventAe68.lean:196).

Discharged from the landed setup (not binders): `hs4`, `hNs`, `hds`, `hd` (`dyadicD`), the range `hRf`
(`windowRfT_rangeShortEligible`, HoneRadii68.lean:34, for every `ω`), `hrle` (`radius_le_countThreshold_of_oneTest`),
`hF0`, `h0`, `hKb` (from `FullAdmAt`, `ConfigOK`), the start `hst` (`hstart_of_fullAdmAt`, HoneSetup239_68.lean:131),
and the walk inputs (`walk_inputs_ae`).

Named inputs (exact types in the statement):
* `hs₀ : 0 < s₀`. `shellOneTest_at_of_goodEnv` has no positivity of `s₀`; `h0 : 0 ∈ fillCells …` needs `ball 0 s₀ ≠ ∅`.
  The consumer must supply it (the setup `hRr_fixedOmega'` takes it as well).
* The environment facts at `ω`, the fields of `RegularEnvAt68` (B1Assembly68.lean:553): continuity `hηω`,
  `CurveEscapesBothEnds` `hcurveω` (the cocompact limit follows by `tendsto_cocompact_of_escapes`, S6e/Geometry.lean:94),
  the closed-cell edges `hadjω` (converted to cell form by `cell_isCompact`, S6n.lean:289), and the local finiteness
  and loop-weight `hmultω`. The mesh `hmω` is the binder `hmesh` of the B1 theorem.

Terminology: Armstrong-Kuusi-Mourrat (shell centres, good annuli), Armitage-Gardiner (exit times of balls),
Duplantier-Sheffield (the mated-CRT boundary-length parametrisation `η`).

The conclusion writes the leaf prefix set unfolded: `leafPre ε η Θ F0 A r s d Rf k` (B1Assembly68.lean:63) is by
definition `prefixSet (fun j w => w j) (↑A) (shellExit … k) (vExitTime (killed ε η Θ F0 r))`. The unfolded form avoids
importing B1Assembly68, so that B1Assembly68 may later import this file to discharge its binder `hEl`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneElAe

open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf
open MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68HoneRadii
open MatedCRT.Lemma68HoneSetup

/-- **The eligibility binder `hEl` of `shellOneTest_at_of_goodEnv`, at one environment.** Under `FullAdmAt`, for every
shell `k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1`, almost surely in the walk `x` under `srwLaw (S.mult ε ω) i.a`,
if `x` is in the leaf prefix set (`leafPre`, B1Assembly68.lean:63), then the shell centre is short-eligible.
Proof: `hEl_ae_of_walk` (HoneGoodEventAe68.lean:196) with the walk inputs `walk_inputs_ae` (adjacency from `hadjω`, start
from `hstart_of_fullAdmAt`, finite killed exit), `hs4`, `hNs`, `hds`, `hRf` and `h0`, `hKb`, `hF0` from `ConfigOK`. -/
theorem hEl_fixedOmega {γ ρ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hηω : Continuous (S.η ω))
    (hcurveω : MatedCRT.Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hadjω : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 →
      (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k)
            (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ) := by
  intro hFA
  have hr1 : r ≤ 1 := by linarith
  have ha0 : 0 ≤ shortExp ζ := shortExp_nonneg hζ0.le
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (dyadicD_mem hr0 hr1).2
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  -- the shell count is at least 1: `countBound_zeta` with `r ≤ countThreshold ζ` gives `countConst ζ r^(-ζ) ≥ 1`
  have hcb := countBound_zeta hζ0 hr0 hrle (dyadicD_pos r) hdr hd2
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
  have hRf := windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst := MatedCRT.Lemma68HoneSetup239.hstart_of_fullAdmAt S hε hs₀ ω hηω r hr0 i hFA
  -- the cells are compact, so the closed-cell adjacency is the cell adjacency
  have hcl : ∀ k : ℤ, closure (cell ε (S.η ω) k) = cell ε (S.η ω) k :=
    fun k => (MatedCRT.Lemma68C12Geom.cell_isCompact hηω k).isClosed.closure_eq
  have hadjC : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => by
      have h' := hadjω j k h
      rwa [hcl j, hcl k] at h'
  have htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    MatedCRT.Lemma68Geometry.tendsto_cocompact_of_escapes hcurveω
  have hPath := MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae hηω hε htendω hadjC hmultω.1 hmultω.2 i.a
    hF0eq hst
  intro k hk
  exact MatedCRT.Lemma68HoneGoodEventAe.hEl_ae_of_walk (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    hηω hε hr0 hrρ hd hds hs4 hNs rfl hmω hF0eq h0 hKb hRf hPath k hk

/-- **`hstart_of_fullAdmAt` at a generic sparsity exponent `s1`.** Same proof as
`MatedCRT.Lemma68HoneSetup239.hstart_of_fullAdmAt` (HoneSetup239_68.lean:132). That proof reads only the fields
`hFA.1.2.2`, `hFA.2.1.1` and `hFA.2.1.2` of `FullAdmAt`, none of which uses the value of the sparsity exponent, so no
hypothesis on `s1` is needed. -/
theorem hstart_of_fullAdmAt_s1 {γ ρ s₀ ε s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hε : 0 < ε) (hs₀ : 0 < s₀) (ω : Ω) (hηω : Continuous (S.η ω)) (r : ℝ) (hr : 0 < r)
    (i : Lemma68Config.Config68)
    (hFA : Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i) :
    (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty := by
  have hΘ : i.Θ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hFA.1.2.2 (Metric.mem_ball_self hs₀)
    rw [h] at h0
    simp [fillCells] at h0
  exact Lemma68WindowStart.cell_meets_frontier_thickening hε hηω hΘ hr hFA.2.1.1 hFA.2.1.2

/-- **The eligibility binder `hEl` at a generic sparsity exponent `s1`.** Same statement and
proof as `hEl_fixedOmega` (line 58) with `Lemma68Config.sparsityS1 γ` replaced by `s1`; its start `hst` is the generic
copy `hstart_of_fullAdmAt_s1` above. No hypothesis on `s1` is used. -/
theorem hEl_fixedOmega_s1 {γ ρ s1 : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hηω : Continuous (S.η ω))
    (hcurveω : MatedCRT.Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hadjω : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 →
      (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k)
            (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ) := by
  intro hFA
  have hr1 : r ≤ 1 := by linarith
  have ha0 : 0 ≤ shortExp ζ := shortExp_nonneg hζ0.le
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (dyadicD_mem hr0 hr1).2
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  -- the shell count is at least 1: `countBound_zeta` with `r ≤ countThreshold ζ` gives `countConst ζ r^(-ζ) ≥ 1`
  have hcb := countBound_zeta hζ0 hr0 hrle (dyadicD_pos r) hdr hd2
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
  have hRf := windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst := hstart_of_fullAdmAt_s1 S hε hs₀ ω hηω r hr0 i hFA
  -- the cells are compact, so the closed-cell adjacency is the cell adjacency
  have hcl : ∀ k : ℤ, closure (cell ε (S.η ω) k) = cell ε (S.η ω) k :=
    fun k => (MatedCRT.Lemma68C12Geom.cell_isCompact hηω k).isClosed.closure_eq
  have hadjC : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => by
      have h' := hadjω j k h
      rwa [hcl j, hcl k] at h'
  have htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    MatedCRT.Lemma68Geometry.tendsto_cocompact_of_escapes hcurveω
  have hPath := MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae hηω hε htendω hadjC hmultω.1 hmultω.2 i.a
    hF0eq hst
  intro k hk
  exact MatedCRT.Lemma68HoneGoodEventAe.hEl_ae_of_walk (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    hηω hε hr0 hrρ hd hds hs4 hNs rfl hmω hF0eq h0 hKb hRf hPath k hk

/-- **`hEl` at one environment, generic sparsity exponent and window constant.** Same statement
as `hEl_fixedOmega_s1` with the window constant `shellC068` replaced by a free `c0W : ℝ`: the window radius is
`windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`, which is `winRf` at `c0W = shellC068`. The sparsity exponent `s1` is
free as in `hEl_fixedOmega_s1`. The proof uses no hypothesis on `c0W` (`windowRfT_rangeShortEligible` is generic in the
window constant). -/
theorem hEl_fixedOmega_g {γ ρ s1 c0W : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hηω : Continuous (S.η ω))
    (hcurveω : MatedCRT.Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hadjω : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 →
      (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑i.A : Set ℤ)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k)
            (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ) := by
  intro hFA
  have hr1 : r ≤ 1 := by linarith
  have ha0 : 0 ≤ shortExp ζ := shortExp_nonneg hζ0.le
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hd := dyadicD_pos r
  have hd1 := dyadicD_le_one r
  have hdr : r ^ 2 ≤ dyadicD r := (dyadicD_mem hr0 hr1).1
  have hd2 : dyadicD r < 2 * r ^ 2 := (dyadicD_mem hr0 hr1).2
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    simpa using h
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrle hd hd2
  -- the shell count is at least 1: `countBound_zeta` with `r ≤ countThreshold ζ` gives `countConst ζ r^(-ζ) ≥ 1`
  have hcb := countBound_zeta hζ0 hr0 hrle (dyadicD_pos r) hdr hd2
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
  have hRf := windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd hd1 ha1 ω
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst := hstart_of_fullAdmAt_s1 S hε hs₀ ω hηω r hr0 i hFA
  -- the cells are compact, so the closed-cell adjacency is the cell adjacency
  have hcl : ∀ k : ℤ, closure (cell ε (S.η ω) k) = cell ε (S.η ω) k :=
    fun k => (MatedCRT.Lemma68C12Geom.cell_isCompact hηω k).isClosed.closure_eq
  have hadjC : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => by
      have h' := hadjω j k h
      rwa [hcl j, hcl k] at h'
  have htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    MatedCRT.Lemma68Geometry.tendsto_cocompact_of_escapes hcurveω
  have hPath := MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae hηω hε htendω hadjC hmultω.1 hmultω.2 i.a
    hF0eq hst
  intro k hk
  exact MatedCRT.Lemma68HoneGoodEventAe.hEl_ae_of_walk (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    hηω hε hr0 hrρ hd hds hs4 hNs rfl hmω hF0eq h0 hKb hRf hPath k hk

end Lemma68HoneElAe
end MatedCRT

#print axioms MatedCRT.Lemma68HoneElAe.hEl_fixedOmega

#print axioms MatedCRT.Lemma68HoneElAe.hstart_of_fullAdmAt_s1
#print axioms MatedCRT.Lemma68HoneElAe.hEl_fixedOmega_s1

#print axioms MatedCRT.Lemma68HoneElAe.hEl_fixedOmega_g
