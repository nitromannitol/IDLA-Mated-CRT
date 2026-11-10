import MatedCRT.FirstPass.S4S6c.HoneRadii68
import MatedCRT.FirstPass.S4S6c.ExitAe68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S6r.Count

/-!
# Setup discharges of the leaf binders at the fixed-radius B1 setting (z12, fp-S4S6c-hone-setup)

* `hRr_ae_setup`: the almost-sure radius bound `r ^ 2 ≤ Rf (shellCentre …) ≤ 1` along the walk, for `k ≤ n` with
  `n + 1 ≤ shellCount r (dyadicD r ^ shortExp ζ)`, in the setting of `shellOneTest_ae_fixedR`
  (B1Assembly68.lean). The radius is `Rf = winRf` (= `windowRfT`, `c₀ = shellC068`), `d = dyadicD r`,
  `Kset = fillCells ε (S.η ω) i.Θ`, `s = d ^ shortExp ζ`; the walk law is `srwLaw (S.mult ε ω) i.a`.
  Discharged here: the range on `shortEligible` (`windowRfT_rangeShortEligible`), `r ^ 2 ≤ d ≤ 1`, the
  scale bound `d ^ a ≤ r / 4000` (`shell_size_le`, from the named `hrle`), the count bound `hNs`, the edge
  condition `hedge` (`TraceInputs68.ae_adjacent`), the start `i.a` (`hstart`), the killed exit `htau`
  (`ExitAe68.ae_exit_ne_top_of_bounded` with `GreenTest68.vExitTime_le_of_subset`), and `h0`, `hKb`, `hF0` from
  `FullAdm`. Named inputs not in that setting: `hrle : r ≤ countThreshold ζ` (see report); `hmesh` is kept as the
  binder of the setting (routed 55b).
* `card_lt_of_tRad_lt`: `tRad` below `r` gives the count bound `|B| < s₁ r^{2β} / ε`.
* `hL68_of_clause`: the leaf binder `hL68` (ShellHoneInst68.lean:74) from the sparsity clause of `Admissible`
  (write-up (15)) at `s₁ = K.s1`, `β = K.βm`, given the cap-radius inequality `hcap` as a named input. The
  `FullAdm` parameterization `s₁ = K.s1` is not yet in `FullAdm` (q2, chat 237): see the report.

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

/-- **The almost-sure radius bound at the fixed radius `r` (setup of `shellOneTest_ae_fixedR`).**
For `ω ∈ E` with `FullAdm`, and every `k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1` (the index range of the
`htest` binder of `shellOneTest_ae_fixedR`), almost surely along the walk `srwLaw (S.mult ε ω) i.a`, the radius at the
shell centre lies in `[r ^ 2, 1]`. The conclusion is the shape of `radius_bounds_ae` (HoneRadii68.lean). Inputs:
`hrle` (not in the setting of `shellOneTest_ae_fixedR`; it gives `shellCount ≥ 1` via `countBound_zeta`), `hmesh`
and `hstart` (binders of that setting), and `hηc` (its `ae` continuity binder). -/
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
  filter_upwards [hmesh, hstart, hηc, hmult_ae_valid hγ0 hγ2 S hS hε,
    TraceInputs68.ae_adjacent hγ0 hγ2 S hS, hS.ae_tendsto_cocompact] with ω hmω hstω hηω hmultω hadjω htendω
  have hRf := windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω
  intro hωE hFA k hk
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
  exact radius_bounds_ae hηω hε (hadjω ε hε) i.a hr0 hrρ hd hd1 ha0 hdr hds hs4 hNs hmω hF0eq h0 hKb
    hRf (hstω hFA) hτ k hk

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

end Lemma68HoneSetup
end MatedCRT

#print axioms MatedCRT.Lemma68HoneSetup.hRr_ae_setup
#print axioms MatedCRT.Lemma68HoneSetup.card_lt_of_tRad_lt
#print axioms MatedCRT.Lemma68HoneSetup.hL68_of_clause
