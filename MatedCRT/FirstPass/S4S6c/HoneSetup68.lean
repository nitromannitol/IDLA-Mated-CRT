import MatedCRT.FirstPass.S4S6c.HoneRadii68
import MatedCRT.FirstPass.S4S6c.ExitAe68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S6r.Count

/-!
# Setup discharges of the leaf binders at the fixed-radius B1 setting (z12, fp-S4S6c-hone-setup)

* `hRr_fixedOmega` and `hRr_fixedOmega'`: the radius bound `r ^ 2 ≤ Rf (shellCentre …) ≤ 1` along the walk, for every
  `k ≤ n` with `n + 1 ≤ shellCount r (dyadicD r ^ shortExp ζ)`, at ONE environment `ω`. No almost-sure quantifier in `ω`
  remains: the environment facts at `ω` are pointwise hypotheses. Conclusion: almost surely in the walk `x` under
  `srwLaw (S.mult ε ω) i.a`. The primed form derives `hrle : r ≤ countThreshold ζ` from the B1 hypotheses on `q₀`
  (`0 < q₀`, `q₀ ≤ (1/4)²/(4 shellChone68 C_E C_G)`, `r ≤ rAmp q₀ ζ`) through `radius_le_countThreshold_of_oneTest`
  (ShellHoneInst68.lean, q2 item (c)).
* `hRr_ae_setup` and `hRr_ae_setup'`: the almost-sure-in-`ω` forms (`filter_upwards` of the fixed-`ω` ones). The binders
  `hmesh`, `hstart`, `hηc` stay those of the setting (`hmesh`, `hstart` routed to z5).
* `card_lt_of_tRad_lt`: `tRad` below `r` gives the count bound `|B| < s₁ r^{2β} / ε`.
* `hL68_of_clause` and `hL68_fixedOmega`: the leaf binder `hL68` (ShellHoneInst68.lean:74) at one `ω`, for every `r` in
  `[10 ε^{K.ω}, R]`, from the sparsity clause of `Admissible` (write-up (15)) at `(K.s1, K.βm)`, with the cap-radius
  inequality `hcap` as a named input.

Terminology: Armstrong-Kuusi-Mourrat (shells, good annuli), Armitage-Gardiner (exit times of balls),
Duplantier-Sheffield (quantum-length balls, `η` as the boundary-length parametrisation).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneSetup

open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf
open MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68HoneRadii

/-- The window radius at the environment `ω` (mirror of `Lemma68B1Assembly.winRf`, B1Assembly68.lean:50, which
does not build in the current working tree: see the report). Same body, so `winRf` is definitionally that radius. -/
noncomputable def winRf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ζ C r : ℝ) (ω : Ω) : ℂ → ℝ :=
  windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω

/-- Mirror of `Lemma68B1Assembly.hmult_ae_valid` (B1Assembly68.lean:30): the local multiplicity facts a.s. -/
theorem hmult_ae_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ0 hγ2 hS] with ω hω
  obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hω.1 hω.2.1 hω.2.2
  exact ⟨hlf, hsucc⟩

/-- `1 ≤ shellChone68`, so the B1 bound `q₀ ≤ (1/4)²/(4 shellChone68 C_E C_G)` gives `q₀ ≤ 1` with no further
antecedent (ShellConstOrder68.lean:132). -/
theorem q0_le_one_of_shellChone {q0 CE CG : ℝ}
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG)) : q0 ≤ 1 := by
  have hs : (1 : ℝ) ≤ shellChone68 CE CG := one_le_shellChone68 CE CG
  have h4 : (0 : ℝ) < 4 * shellChone68 CE CG := by linarith
  have h5 : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ≤ 1 := by
    rw [div_le_iff₀ h4]
    norm_num
    linarith
  exact hq0c.trans h5

/-- **The almost-sure radius bound at one environment `ω` (setup of `shellOneTest_ae_fixedR`, fixed-`ω` form).**
At `ω` with `ω ∈ E` and `FullAdm`, for every `k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1`, almost surely along the walk
`srwLaw (S.mult ε ω) i.a`, the radius at the shell centre lies in `[r ^ 2, 1]`. The conclusion is the shape of
`radius_bounds_ae` (HoneRadii68.lean). No almost-sure quantifier in `ω` remains: the environment facts at `ω` are the
pointwise hypotheses `hmω`, `hstω`, `hηω`, `htendω`, `hadjω`, `hmultω`. `hmω` and `hstω` are the `r`-dependent binders
of the setting (`hmesh`, `hstart`; routed to z5). `hrle` is the named setup input (see `hRr_fixedOmega'`). -/
theorem hRr_fixedOmega {γ ρ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrle : r ≤ countThreshold ζ)
    (E : Set Ω) (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstω : Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
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
  intro _ hFA k hk
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hτ : ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a, vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ := by
    have hU : Bornology.IsBounded (Metric.ball (0 : ℂ) ρ) := Metric.isBounded_ball
    filter_upwards [ExitAe68.ae_exit_ne_top_of_bounded hε hηω htendω hmultω.1 hmultω.2 hU i.a] with x hx
    refine ne_top_of_le_ne_top hx (GreenTest68.vExitTime_le_of_subset ?_ x)
    intro v hv
    have hvF : v ∈ (↑i.F0 : Set ℤ) := Finset.mem_coe.2 hv.1
    rw [hF0eq] at hvF
    have hvF' : (cell ε (S.η ω) v ∩ Metric.ball (0 : ℂ) ρ).Nonempty := hvF
    obtain ⟨p, hp1, hp2⟩ := hvF'
    exact ⟨p, subset_closure hp1, hp2⟩
  exact radius_bounds_ae hηω hε hadjω i.a hr0 hrρ hd hd1 ha0 hdr hds hs4 hNs hmω hF0eq h0 hKb
    hRf (hstω hFA) hτ k hk

/-- **`hRr_fixedOmega` with `hrle` derived.** The named input `hrle : r ≤ countThreshold ζ` of `hRr_fixedOmega` is
discharged from the B1 hypotheses on `q₀` (`0 < q₀`, `q₀ ≤ (1/4)²/(4 shellChone68 C_E C_G)`, `r ≤ rAmp q₀ ζ`) by
`radius_le_countThreshold_of_oneTest` (ShellHoneInst68.lean; `Lemma68ChainGlue.rAmp_le_countThreshold`, ShellChainGlue68.lean:53). -/
theorem hRr_fixedOmega' {γ ρ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (E : Set Ω) (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstω : Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 :=
  hRr_fixedOmega S hρ1 hζ0 hζ1 hs₀ hε hr0 hrρ
    (radius_le_countThreshold_of_oneTest hq0 (q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl)
    E i ω hmω hstω hηω htendω hadjω hmultω

/-- **The almost-sure radius bound (setup of `shellOneTest_ae_fixedR`, a.s.-in-`ω` form).** The binders `hmesh`,
`hstart`, `hηc` are those of the setting; the environment facts `hmult_ae_valid`, `ae_adjacent`, `ae_tendsto_cocompact`
are almost sure in `ω` and independent of `r`. Each `ω` is then `hRr_fixedOmega`. -/
theorem hRr_ae_setup {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ζ C s₀ ε r : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrle : r ≤ countThreshold ζ)
    (E : Set Ω) (i : Lemma68Config.Config68)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hηc : ∀ᵐ ω ∂S.P, Continuous (S.η ω)) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
  filter_upwards [hmesh, hstart, hηc, hmult_ae_valid hγ0 hγ2 S hS hε,
    TraceInputs68.ae_adjacent hγ0 hγ2 S hS, hS.ae_tendsto_cocompact] with ω hmω hstω hηω hmultω hadjω htendω
  exact hRr_fixedOmega S hρ1 hζ0 hζ1 hs₀ hε hr0 hrρ hrle E i ω hmω hstω hηω htendω (hadjω ε hε) hmultω

/-- **`hRr_ae_setup` with `hrle` derived** (no `hrle` binder): the B1 hypotheses on `q₀` give `hrle` through
`radius_le_countThreshold_of_oneTest`; see `hRr_fixedOmega'`. -/
theorem hRr_ae_setup' {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (E : Set Ω) (i : Lemma68Config.Config68)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (hηc : ∀ᵐ ω ∂S.P, Continuous (S.η ω)) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 :=
  hRr_ae_setup hγ0 hγ2 S hS hρ1 hζ0 hζ1 hs₀ hε hr0 hrρ
    (radius_le_countThreshold_of_oneTest hq0 (q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl)
    E i hmesh hstart hηc

/-- **Count bound from `tRad`.** `tRad ε s₁ β B = (|B| ε / s₁)^{1/(2β)}`; if it is below `r > 0` then
`|B| < s₁ r^{2β} / ε` (write-up (14)-(15), Armitage-Gardiner-free: pure real analysis). -/
theorem card_lt_of_tRad_lt {ε s1 βm r : ℝ} (B : Finset ℤ) (hε : 0 < ε) (hs1 : 0 < s1) (hβ : 0 < βm)
    (h : tRad ε s1 βm B < r) : (B.card : ℝ) < s1 * r ^ (2 * βm) / ε := by
  unfold tRad at h
  have hX0 : 0 ≤ (B.card : ℝ) * ε / s1 := by positivity
  have h2 : (((B.card : ℝ) * ε / s1) ^ (1 / (2 * βm))) ^ (2 * βm) < r ^ (2 * βm) :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hX0 _) h (by positivity)
  rw [← Real.rpow_mul hX0, one_div_mul_cancel (by positivity : (2 * βm) ≠ 0), Real.rpow_one] at h2
  have h3 : (B.card : ℝ) * ε < r ^ (2 * βm) * s1 := (div_lt_iff₀ hs1).mp h2
  rw [lt_div_iff₀ hε]
  linarith [mul_comm (r ^ (2 * βm)) s1]

open scoped Classical in
/-- **The leaf binder `hL68` (ShellHoneInst68.lean:74) from the sparsity clause of `Admissible`.** The clause (15)
at `s₁ = K.s1`, `β = K.βm`, `x = r` gives, for `B = A ∩ V(B_r z)`, either `r ≤ c_B` or `t_B < r`. The second case is
the count bound (`card_lt_of_tRad_lt`). The first case is excluded by the named input `hcap : c_B < r`, which is NOT
derivable from the sources (see the report). `hs1 : 0 < K.s1` is needed for the empty configuration. -/
theorem hL68_of_clause {γ ρc : ℝ} (K : Constants68 γ ρc) {η : ℝ → ℂ} {ε r : ℝ} (A : Finset ℤ) (hε : 0 < ε)
    (hr : 0 < r) (hs1 : 0 < K.s1)
    (hclause : ∀ B ⊆ A, B.Nonempty → r ≤ cRad ε η B ∨ tRad ε K.s1 K.βm B < r)
    (hcap : ∀ z : ℂ, cRad ε η (A.filter (fun v => v ∈ cellVertices ε η (Metric.ball z r))) < r) :
    ∀ z : ℂ, (((↑A : Set ℤ) ∩ cellVertices ε η (Metric.ball z r)).ncard : ℝ)
      < K.s1 * r ^ (2 * K.βm) / ε := by
  intro z
  have hβ : 0 < K.βm := lt_of_le_of_lt (by positivity) K.hβ
  set B := A.filter (fun v => v ∈ cellVertices ε η (Metric.ball z r)) with hBdef
  have hBset : (↑B : Set ℤ) = (↑A : Set ℤ) ∩ cellVertices ε η (Metric.ball z r) := by
    ext v; simp [hBdef]
  rw [← hBset, Set.ncard_coe_finset]
  by_cases hB : B.Nonempty
  · rcases hclause B (Finset.filter_subset _ _) hB with h | h
    · exact absurd (hcap z) (not_lt.mpr h)
    · exact card_lt_of_tRad_lt B hε hs1 hβ h
  · rw [Finset.not_nonempty_iff_eq_empty] at hB
    rw [hB, Finset.card_empty, Nat.cast_zero]
    exact div_pos (mul_pos hs1 (Real.rpow_pos_of_pos hr _)) hε

open scoped Classical in
/-- **The leaf binder `hL68` at one environment `ω`, for every `r ∈ [10 ε^{K.ω}, R]`.** `K.ω` is the mesh exponent
`ω₀` of Lemma 6.8 (`Constants68.ω`). For each such `r`, `FullAdmAt (sparsityS₁ γ)` at `ω` (the guard of `hL68` in
`shellOneTest_ae_fixedR`, B1Assembly68.lean) gives the admissibility clause of `Admissible` at `(sparsityS₁ γ,
(2+γ)²/2+1)`; the rewrites `hK1`, `hK2` identify these with `(K.s1, K.βm)` (for `K = shellK68 …`, these are
`shellK68_params`, ShellHoneInst68.lean). Then `hL68_of_clause` applies, with the cap-radius input `hcap` as a named
hypothesis for every such `r` and `z`. The conclusion carries no almost-sure quantifier. -/
theorem hL68_fixedOmega {γ ρ s₀ ε R : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (hK1 : K.s1 = Lemma68Config.sparsityS1 γ)
    (hK2 : K.βm = (2 + γ) ^ 2 / 2 + 1) (hε : 0 < ε) (ω : Ω) (i : Lemma68Config.Config68)
    (hFA : ∀ r : ℝ, 10 * ε ^ K.ω ≤ r → r ≤ R →
      Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i)
    (hcap : ∀ r : ℝ, 10 * ε ^ K.ω ≤ r → r ≤ R → ∀ z : ℂ,
      cRad ε (S.η ω) (i.A.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r))) < r) :
    ∀ r : ℝ, 10 * ε ^ K.ω ≤ r → r ≤ R → ∀ z : ℂ,
      (((↑i.A : Set ℤ) ∩ cellVertices ε (S.η ω) (Metric.ball z r)).ncard : ℝ)
        < K.s1 * r ^ (2 * K.βm) / ε := by
  intro r h1 h2
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) h1
  have hs1 : 0 < K.s1 := by rw [hK1]; exact Lemma68Config.sparsityS1_pos γ
  have hcl : ∀ B ⊆ i.A, B.Nonempty →
      r ≤ cRad ε (S.η ω) B ∨ tRad ε K.s1 K.βm B < r := by
    have h := ((hFA r h1 h2).2).2.2
    rw [hK1, hK2]
    exact h
  exact hL68_of_clause K i.A hε hr hs1 hcl (hcap r h1 h2)

end Lemma68HoneSetup
end MatedCRT

#print axioms MatedCRT.Lemma68HoneSetup.hRr_fixedOmega
#print axioms MatedCRT.Lemma68HoneSetup.hRr_fixedOmega'
#print axioms MatedCRT.Lemma68HoneSetup.hRr_ae_setup
#print axioms MatedCRT.Lemma68HoneSetup.hRr_ae_setup'
#print axioms MatedCRT.Lemma68HoneSetup.card_lt_of_tRad_lt
#print axioms MatedCRT.Lemma68HoneSetup.hL68_of_clause
#print axioms MatedCRT.Lemma68HoneSetup.hL68_fixedOmega
