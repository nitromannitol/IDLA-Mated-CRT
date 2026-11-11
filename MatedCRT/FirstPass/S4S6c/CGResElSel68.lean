import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.HoneElAe68
import MatedCRT.FirstPass.S4S6c.WalkLoc68
import MatedCRT.FirstPass.S4S6c.StopFinPw68
import MatedCRT.FirstPass.S4S6c.HoneCellGoodSelPw68

/-!
# The CG-residual pointwise premises: `resEl_pt`, `resStopFin_pt`, `resSel_pt`

Step A. For one environment `ω`, one radius `r` and one scale `ε`, each residual of `ShellPtPremCG` (ShellCoreCG68.lean
l.337-509) holds from the individual ω-level clauses it uses, given as named binders with the exact types of
`ShellPtPremCG`, plus the `FullAdmAt` premise. The global full-support clause of `ShellPtPremCG` is never used.

* `resEl_pt` (ShellCGResEl). `hEl_fixedOmega_ball` is `hEl_fixedOmega_g` (HoneElAe68.lean:245) with the univ-form mesh
  `CellDiamLe ε η (dyadicD r / 100) Set.univ` replaced by the ball mesh on `ball 0 (rhoCell68 ρ)`; its walk lemma is
  `Lemma68WalkLoc.hEl_ae_of_walk_loc` (WalkLoc68.lean:105) in place of `hEl_ae_of_walk`. The body is copied verbatim.
* `resStopFin_pt` (ShellCGResStopFin). `hstopFin_pw_g` (StopFinPw68.lean:83); `htend` from `tendsto_cocompact_of_escapes`.
* `resSel_pt` (ShellCGResSel). `hsel_fixedOmega_g` (HoneCellGoodSelPw68.lean:125) with `K := shellKCG`; `hwin` at
  `dyadicD r = (1/2)^k` (`dyadicD_eq_pow`, ShellCorePw68.lean:50). It needs `C ≤ CG`, which is not a clause of
  `ShellPtPremCG`: kept as the named binder `hCCG` and reported.

Terminology: Duplantier-Sheffield (LQG measure, mated-CRT map), Armitage-Gardiner (balls), Armstrong-Kuusi-Mourrat (cells,
mesh, shell exit).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGResElSel

open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf
open MatedCRT.Lemma68ChainGlue MatedCRT.Lemma68HoneRadii
open MatedCRT.Lemma68HoneSetup MatedCRT.Lemma68HoneElAe
open MatedCRT.Lemma68ShellCoreCG MatedCRT.Lemma68HoneCellGoodSelPw
open MatedCRT.Lemma68B1Assembly MatedCRT.Lemma68ShellCorePw

/-- **`hEl` at one environment, with the ball mesh.** Copy of `hEl_fixedOmega_g` (HoneElAe68.lean:245) whose univ-form
mesh is replaced by the cell-diameter bound on `ball 0 (rhoCell68 ρ)`, with the gap `hgap : dyadicD r / 100 ≤ rhoCell68 ρ - ρ`;
the walk lemma is `hEl_ae_of_walk_loc` (WalkLoc68.lean:105). -/
theorem hEl_fixedOmega_ball {γ ρ s1 c0W : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ C s₀ ε r q0 CE CG : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (i : Lemma68Config.Config68) (ω : Ω)
    (hmω : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hgap : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
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
  exact MatedCRT.Lemma68WalkLoc.hEl_ae_of_walk_loc (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ)
    hηω hε hr0 hrρ hd hds hs4 hNs rfl hgap hmω hF0eq h0 hKb hRf hPath k hk

/-- **Step A, `ShellCGResEl` (`resEl_pt`).** The leaf centres are eligible, for one environment `ω` at one radius `r`,
from the clauses of `ShellPtPremCG` that `hEl_fixedOmega_ball` uses (`hmesh` from the cell clause of `meshEventR`,
`hεcell` from `shellKCG_eps_cell`) and the `FullAdmAt` premise. -/
theorem resEl_pt {γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hω₀ : 0 < ω₀) (hω2ζ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    (hCG : 0 < CG) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hrR : r ≤ R) (hRρ : R ≤ ρ / 4) (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) (hr10 : 10 * ε ^ ω₀ ≤ r)
    (hmeshω : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε)
    (hgap : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hηω : Continuous (S.η ω))
    (hcurveω : MatedCRT.Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hmult : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hadjω : ∀ u v : ℤ, S.mult ε ω u v ≠ 0 →
      (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
        shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
          shortEligible ρ (dyadicD r) (shortExp ζ) := by
  have hr0 : 0 < r := by
    have := Real.rpow_pos_of_pos hε ω₀
    linarith
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hεcell := shellKCG_eps_cell (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hε hεe hr10
  have hmesh := cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω hε hρ1 hr0 hrρ
    (shellC0_le_one_cg hCG) hεcell
  have hgap' : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have hd : 0 < dyadicD r := dyadicD_pos r
    have h0 : 0 ≤ dyadicD r ^ shortExp ζ := Real.rpow_nonneg hd.le _
    linarith
  exact hEl_fixedOmega_ball S hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hrA i ω hmesh hgap' hηω hcurveω hadjω
    (hmult ε hε) hFA

/-- **Step A, `ShellCGResStopFin` (`resStopFin_pt`).** The shell exit lands in a finite set, from `hstopFin_pw_g`
(StopFinPw68.lean:83) with `htend` from the curve clause and `hloc` from the multiplicity clause at `ε`. -/
theorem resStopFin_pt {γ ζ ρ CG C s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) (i : Lemma68Config.Config68)
    (hε : 0 < ε) (hs₀ : 0 < s₀)
    (hcurveω : MatedCRT.Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hmult : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hdeg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
      ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x < ⊤ →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x).toNat ∈ F :=
  MatedCRT.Lemma68StopFinPw.hstopFin_pw_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG) S ω i hε hs₀
    (MatedCRT.Lemma68Geometry.tendsto_cocompact_of_escapes hcurveω) (hmult ε hε).1 hdeg hFA

/-- **Step A, `ShellCGResSel` (`resSel_pt`).** The eligible centres carry good annulus events, from `hsel_fixedOmega_g`
(HoneCellGoodSelPw68.lean:125) with `K := shellKCG` (so `K.c0 = shellC0 CG`), `hwin` from the window clause at
`dyadicD r = (1/2)^k`. The named hypothesis `hCCG : C ≤ CG` is NOT derivable from `ShellPtPremCG` (report). -/
theorem resSel_pt {γ ω₀ ζ ρ CG C s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω₀ : 0 < ω₀)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hCG : 0 < CG)
    (hCCG : C ≤ CG)
    (hEwr : ω ∈ Ew (dyadicD r))
    (hwinAll : ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k))
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      IsGoodAnnulusEvent (S.μ ω) (shellC0 CG) CG
        ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) z) z := by
  obtain ⟨k, hk⟩ := dyadicD_eq_pow r
  have hwin : ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) := by
    rw [hk]
    exact hwinAll k (by rw [← hk]; exact hEwr)
  exact hsel_fixedOmega_g (c0W := shellC0 CG) S (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG)
    rfl ω i hwin hCCG hFA

/-- **Step B, `ShellCGResEl` (`shellCGResEl_holds`).** The residual holds for every `𝒮`: the clauses of the new
`ShellPtPremCG` (b51e0dc) feed `resEl_pt`; the mesh membership is `countingMeshEventR_meshR`. -/
theorem shellCGResEl_holds (𝒮 : SpaceFillingSLEModel) : ShellCGResEl 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨hγ0, hγ2, hω₀, _h4, _h5, _h6, _h7, hω2ζ, hCG, _h10, _h11, hζ0, hζ1, hρ0, hρ1, _h16, hq0, _h18, hq0c,
    _h20, hRρ, hRA, _h23, hs₀, _h25, _h26, hε, hεe, hr10, hrR, _h31, hmeshω, hgap, hcurve, hmult, hηω, _h37, _h38,
    _h39, hadj, _h41, _h42, _h43⟩ := hpre
  exact resEl_pt S ω i hγ0 hγ2 hω₀ hω2ζ hCG hζ0 hζ1 hρ0 hρ1 hq0 hq0c hrR hRρ hRA hs₀ hε hεe hr10
    (countingMeshEventR_meshR hmeshω) hgap hηω hcurve hmult hadj hFA

/-- **Step B, `ShellCGResStopFin` (`shellCGResStopFin_holds`).** The residual holds for every `𝒮`, from `resStopFin_pt`. -/
theorem shellCGResStopFin_holds (𝒮 : SpaceFillingSLEModel) : ShellCGResStopFin 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  obtain ⟨_h1, _h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _h14, _h15, _h16, _h17, _h18, _h19,
    _h20, _h21, _h22, _h23, hs₀, _h25, _h26, hε, _h28, _h29, _h30, _h31, _h32, _h33, hcurve, hmult, _h36, _h37, _h38,
    hdeg, _h40, _h41, _h42, _h43⟩ := hpre
  exact resStopFin_pt S ω i hε hs₀ hcurve hmult hdeg hFA

/-- **Step B, `ShellCGResSel` (`shellCGResSel_of_hCCG`).** The residual holds from `resSel_pt` given the named
hypothesis `hCCG : C ≤ CG` under `ShellPtPremCG`. This ordering is NOT a clause of `ShellPtPremCG` and not a binder of
`ShellOneTestPointwiseCGRStmt`; it is the premise `hCCG` of `hsel_fixedOmega_g` (HoneCellGoodSelPw68.lean:125). -/
theorem shellCGResSel_of_hCCG (𝒮 : SpaceFillingSLEModel)
    (hCCG : ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
      (Ew : ℝ → Set Ω) (ω : Ω) (_i : Lemma68Config.Config68),
      ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω → C ≤ CG) :
    ShellCGResSel 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hpre hFA
  have hCC : C ≤ CG := hCCG γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre
  obtain ⟨hγ0, hγ2, hω₀, _h4, _h5, _h6, _h7, _h8, hCG, _h10, _h11, hζ0, hζ1, hρ0, hρ1, _h16, _h17, _h18, _h19,
    _h20, _h21, _h22, _h23, _h24, _h25, _h26, _h27, _h28, _h29, _h30, hEwr, _h32, _h33, _h34, _h35, _h36, _h37,
    _h38, _h39, _h40, _h41, _h42, hwinAll⟩ := hpre
  exact resSel_pt S Ew ω i hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG hCC hEwr hwinAll hFA

#print axioms MatedCRT.Lemma68CGResElSel.shellCGResEl_holds
#print axioms MatedCRT.Lemma68CGResElSel.shellCGResStopFin_holds
#print axioms MatedCRT.Lemma68CGResElSel.shellCGResSel_of_hCCG
#print axioms MatedCRT.Lemma68CGResElSel.hEl_fixedOmega_ball
#print axioms MatedCRT.Lemma68CGResElSel.resEl_pt
#print axioms MatedCRT.Lemma68CGResElSel.resStopFin_pt
#print axioms MatedCRT.Lemma68CGResElSel.resSel_pt

end Lemma68CGResElSel
end MatedCRT
