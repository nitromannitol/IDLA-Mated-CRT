import MatedCRT.FirstPass.S4S6c.ShellHdePw68
import MatedCRT.FirstPass.S4S6c.HoneSetup68
import MatedCRT.FirstPass.S4S6c.HoneSetup239_68
import MatedCRT.FirstPass.S4S6c.B1Assembly68

/-!
# The hRr chain with a localized mesh bound (fp-S4S6c-hRr-local, z12)

`hRr` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803; binder `hRr` at about l.844) at ONE environment point `ω`.
The univ-form mesh `CellDiamLe ε (η ω) (dyadicD r / 100) Set.univ` of `hRr_fixedOmega'` (HoneSetup68.lean:152) is replaced
by the ball form `CellDiamLe ε (η ω) (dyadicD r / 100) (Metric.ball 0 ρ)`.

Where the univ form was used. The chain `hRr_fixedOmega` → `radius_bounds_ae` (HoneRadii68.lean:150) →
`radius_bounds_of_walk` → `shellCentre_mem_of_walk` → `shell_fin_of_path` (ShellHde68.lean:209) uses the mesh bound once
(ShellHde68.lean:265), on the cell `x C` of the shell hit, at a point `y0` of the two-sided shell with `λ ≤ r/20`. That point
lies in `Metric.ball 0 ρ` (`twoSidedShell_mem_ball`, ShellHdePw68.lean:33), so only the ball form is needed. The localized
`shell_fin_of_path_loc` (ShellHdePw68.lean:49) is reused. The exit cell `x τ` is never measured with the mesh bound.

This file gives the ball-form copies of the three wrappers (`shellCentre_mem_of_walk_loc`, `radius_bounds_of_walk_loc`,
`radius_bounds_ae_loc`) and of the body of `hRr_fixedOmega`. Two changes to that body: the start input `hstω` is derived from
`hstart_of_fullAdmAt` (HoneSetup239_68.lean:132), and the conclusion is the binder `hRr` of `shellOneTest_at_of_goodEnv'`,
including the premise `x ∈ leafPre …`.

Terminology: Armstrong-Kuusi-Mourrat (good annuli, cell-size event), Duplantier-Sheffield (cells, quantum balls),
Armitage-Gardiner (exit times of balls, the killed walk).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneRrLocal

/-! ## 1. The radius wrappers with the ball mesh (copies of HoneRadii68.lean:113-168) -/

section RadiusLoc

open MatedCRT.Lemma68Window MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent MatedCRT.Lemma68Omega
open MatedCRT.Lemma68Admissible

/-- **`shellCentre_mem_of_walk` with the ball mesh.** The shell centres of a walk are eligible, given the mesh bound on the
ball `B(0, ρ)` only (`shell_fin_of_path_loc`, ShellHdePw68.lean:49). -/
theorem shellCentre_mem_of_walk_loc {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {Rf : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρ))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    {x : ℕ → ℤ} (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a :=
  fun k hk => (Lemma68ShellHdePw68.shell_fin_of_path_loc hη hε hr hrρ hd hds hs4 hNs hmesh hF0 h0 hKb hRf hadj hst hτ
    k hk).2

/-- **`radius_bounds_of_walk` with the ball mesh.** -/
theorem radius_bounds_of_walk_loc {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {Rf : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hd1 : d ≤ 1) (ha0 : 0 ≤ a) (hdr : r ^ 2 ≤ d) (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000)
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρ))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    {x : ℕ → ℤ} (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, r ^ 2 ≤ Rf (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) ∧
      Rf (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) ≤ 1 := by
  intro k hk
  obtain ⟨h1, h2⟩ := hRf _ (shellCentre_mem_of_walk_loc hη hε hr hrρ hd hds hs4 hNs hmesh hF0 h0 hKb hRf hadj hst hτ k hk)
  exact ⟨hdr.trans h1, h2.trans (Real.rpow_le_one hd.le hd1 ha0)⟩

/-- **`radius_bounds_ae` with the ball mesh.** Almost surely under `srwLaw m s0`: consecutive cells meet, `x 0 = s0`,
and the killed exit time is finite. -/
theorem radius_bounds_ae_loc {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {m : ℤ → ℤ → ℕ} (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (s0 : ℤ)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {Rf : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hd1 : d ≤ 1) (ha0 : 0 ≤ a) (hdr : r ^ 2 ≤ d) (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000)
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρ))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    (hst : (cell ε η s0 ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : ∀ᵐ x ∂srwLaw m s0, vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0, r ^ 2 ≤ Rf (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) ∧
      Rf (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) ≤ 1 := by
  intro k hk
  filter_upwards [MatedCRT.TruncatedLaws.srwLaw_cells_meet_ae hε.le hedge s0,
    MatedCRT.srwLaw_ae_start m s0, hτ] with x hadj hx0 hτx
  have hst' : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty := by
    rw [hx0]; exact hst
  exact radius_bounds_of_walk_loc hη hε hr hrρ hd hd1 ha0 hdr hds hs4 hNs hmesh hF0 h0 hKb hRf hadj hst' hτx k hk

end RadiusLoc

/-! ## 2. The hRr binder at one point, with the ball mesh -/

section HoneRrLoc

open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf
open MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68HoneRadii

/-- A mesh bound on a set `F` gives the same bound on every smaller set `E ⊆ F`. -/
theorem cellDiamLe_mono_set {ε : ℝ} {η : ℝ → ℂ} {h : ℝ} {E F : Set ℂ} (hEF : E ⊆ F)
    (hF : CellDiamLe ε η h F) : CellDiamLe ε η h E :=
  fun k hk => hF k (by obtain ⟨p, hp1, hp2⟩ := hk; exact ⟨p, hp1, hEF hp2⟩)

/-- **`hRr` at one environment point, with the ball mesh `CellDiamLe ε (η ω) (dyadicD r / 100) (ball 0 ρ)`.** The
conclusion is the binder `hRr` of `shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803): for `k ≤ shellCount - 1` and
almost every walk `x` from `i.a`, if `x` is in `leafPre`, the radius at the shell centre lies in `[r ^ 2, 1]`. The start
input is derived from `FullAdmAt` (`hstart_of_fullAdmAt`); the radius cutoff `r ≤ countThreshold ζ` from `r ≤ rAmp q0 ζ`. -/
theorem hRr_fixedOmega_loc {γ ρ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68B1Assembly.winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (Lemma68HoneSetup.q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
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
  intro hFA k hk
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst : (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    Lemma68HoneSetup239.hstart_of_fullAdmAt S hε hs₀ ω hηω r hr0 i hFA
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
  exact (radius_bounds_ae_loc hηω hε hadjω i.a hr0 hrρ hd hd1 ha0 hdr hds hs4 hNs hmω hF0eq h0 hKb hRf hst hτ k hk).mono
    fun x hx _ => hx

/-- **`hRr_fixedOmega_loc` with the mesh bound on the larger ball `B(0, (1+ρ)/2)`.** The `(1+ρ)/2` form of the mesh
(the q4 interface) implies the `ρ` form, because `B(0, ρ) ⊆ B(0, (1+ρ)/2)` for `ρ < 1`. -/
theorem hRr_fixedOmega_loc_half {γ ρ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ((1 + ρ) / 2)))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68B1Assembly.winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 :=
  hRr_fixedOmega_loc S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω
    (cellDiamLe_mono_set (Metric.ball_subset_ball (by linarith)) hmω) hηω htendω hadjω hmultω


/-- **`hstart_of_fullAdmAt` with a free `s1`.** Copy of `Lemma68HoneSetup239.hstart_of_fullAdmAt`
(HoneSetup239_68.lean:132) with `sparsityS1 γ` replaced by a parameter `s1`. The proof uses only the first and second
components of `FullAdmAt` (`ConfigOK`, `Admissible`), never the value of `s1`: no hypothesis on `s1` is needed. -/
theorem hstart_of_fullAdmAt_s1 {ρ s₀ γ ε s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
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

/-- **`hRr_fixedOmega_loc` with a free `s1` (z12, fp-S4S6c-shellball).** Copy of `hRr_fixedOmega_loc` (l.121) with
`Lemma68Config.sparsityS1 γ` replaced by a parameter `s1`; the proof is unchanged except for the `_s1` start lemma.
No hypothesis on `s1` is used: `FullAdmAt` enters only through `hFA.1` and `hstart_of_fullAdmAt_s1`. -/
theorem hRr_fixedOmega_loc_s1 {γ ρ s1 : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68B1Assembly.winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (Lemma68HoneSetup.q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
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
  intro hFA k hk
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst : (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    hstart_of_fullAdmAt_s1 S hε hs₀ ω hηω r hr0 i hFA
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
  exact (radius_bounds_ae_loc hηω hε hadjω i.a hr0 hrρ hd hd1 ha0 hdr hds hs4 hNs hmω hF0eq h0 hKb hRf hst hτ k hk).mono
    fun x hx _ => hx


/-- **`hRr_fixedOmega_loc_half` with a free `s1` (z12, fp-S4S6c-shellball).** Copy of `hRr_fixedOmega_loc_half`
(l.200), delegating to `hRr_fixedOmega_loc_s1`. No hypothesis on `s1` is used. -/
theorem hRr_fixedOmega_loc_half_s1 {γ ρ s1 : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ((1 + ρ) / 2)))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68B1Assembly.winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            Lemma68B1Assembly.winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 :=
  hRr_fixedOmega_loc_s1 (s1 := s1) S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω
    (cellDiamLe_mono_set (Metric.ball_subset_ball (by linarith)) hmω) hηω htendω hadjω hmultω


/-- **`hRr_fixedOmega_loc` with a free sparsity exponent `s1` and a free window constant `c0W` (`_g`, z12,
fp-S4S6c-shellball; lead operator note 17:07).** Copy of `hRr_fixedOmega_loc_s1` (l.242) in which the window radius
`Lemma68B1Assembly.winRf S ρ ζ C r ω` (= `windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω`, B1Assembly68.lean:63-65)
is written inline with the window constant `c0W` in place of `shellC068`. No hypothesis on `s1` or `c0W` is used: the
only window fact used, `windowRfT_rangeShortEligible` (HoneRadii68.lean:34), holds for every real `c₀`, and the proof
never reads the value of `shellC068`. -/
theorem hRr_fixedOmega_loc_g {γ ρ s1 c0W : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          r ^ 2 ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
  have hrle : r ≤ countThreshold ζ :=
    radius_le_countThreshold_of_oneTest hq0 (Lemma68HoneSetup.q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl
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
  intro hFA k hk
  obtain ⟨hF0eq, hKb0, hs0⟩ := hFA.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hs0 (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := subset_closure.trans hKb0
  have hst : (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    hstart_of_fullAdmAt_s1 S hε hs₀ ω hηω r hr0 i hFA
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
  exact (radius_bounds_ae_loc hηω hε hadjω i.a hr0 hrρ hd hd1 ha0 hdr hds hs4 hNs hmω hF0eq h0 hKb hRf hst hτ k hk).mono
    fun x hx _ => hx

/-- **`hRr_fixedOmega_loc_half` with a free sparsity exponent `s1` and a free window constant `c0W` (`_g`, z12,
fp-S4S6c-shellball).** Copy of `hRr_fixedOmega_loc_half` (l.200) and `hRr_fixedOmega_loc_half_s1` (l.322) with
`sparsityS1 γ` replaced by `s1` and `shellC068` by `c0W`; delegates to `hRr_fixedOmega_loc_g`. No hypothesis on `s1`
or `c0W` is used. -/
theorem hRr_fixedOmega_loc_half_g {γ ρ s1 c0W : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ((1 + ρ) / 2)))
    (hηω : Continuous (S.η ω))
    (htendω : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hadjω : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmultω : IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ Lemma68B1Assembly.leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          r ^ 2 ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 :=
  hRr_fixedOmega_loc_g (s1 := s1) (c0W := c0W) S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hRA i ω
    (cellDiamLe_mono_set (Metric.ball_subset_ball (by linarith)) hmω) hηω htendω hadjω hmultω

end HoneRrLoc

end Lemma68HoneRrLocal
end MatedCRT

#print axioms MatedCRT.Lemma68HoneRrLocal.shellCentre_mem_of_walk_loc
#print axioms MatedCRT.Lemma68HoneRrLocal.radius_bounds_ae_loc
#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc
#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_half

#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_s1
#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_half_s1
#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_g
#print axioms MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_half_g
