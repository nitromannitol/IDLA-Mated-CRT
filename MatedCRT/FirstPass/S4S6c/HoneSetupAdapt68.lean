import MatedCRT.FirstPass.S4S6c.HoneSetup239_68
import MatedCRT.FirstPass.S4S6c.B1Assembly68

/-!
# Adapters from the good event to the binders of `shellOneTest_at_of_goodEnv'`

`B1Assembly68.shellOneTest_at_of_goodEnv'` (B1Assembly68.lean:803) takes the binders `hrz`, `hcap`, `hmesh` and `hRr`
at one environment `ω`. This file gives pointwise adapters, at one `ω`, for

* `hrz` (`r ≤ countThreshold ζ`) from the radius cutoff `r ≤ rAmp q₀ ζ` (`hrz_of_rAmp`);
* `hcap` (the cap radius of the vertices of `i.A` meeting a ball `ball z r` is below `r`) from the continuity of `η ω`
  (`hcap_of_continuous`, by the witness-centre argument `cRad_lt_of_subset_cellVertices_ball`);
* `hmesh` in the ball form `CellDiamLe ε (η ω) (dyadicD r / 100) (ball 0 ρ)` from `ω ∈ meshEvent` (the cell-size
  component of `meshEvent` is at radius `ρ`, Guard68S10.lean:45) and the binder `hεcell` (`cellDiamLe_ball_of_meshEvent`).

`hRr` is not adapted here: its derivation uses the univ-form mesh bound(blocker).

Terminology: Armstrong-Kuusi-Mourrat (cell-size event, good annuli), Armitage-Gardiner (exit times of balls),
Duplantier-Sheffield (quantum-length balls; `η` the boundary-length parametrisation).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneSetupAdapt

open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **`hrz` at one radius.** The binder `hrz : r ≤ countThreshold ζ` of `shellOneTest_at_of_goodEnv'` follows from the
radius cutoff `hRA : r ≤ rAmp q₀ ζ` and the B1 bound `hq0c` on `q₀`, by `radius_le_countThreshold_of_oneTest`
(ShellHoneInst68.lean:213) with `R = r`; the bound `q₀ ≤ 1` is `q0_le_one_of_shellChone` (HoneSetup68.lean:59). -/
theorem hrz_of_rAmp {q0 CE CG ζ r : ℝ} (hq0 : 0 < q0)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG)) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ) : r ≤ countThreshold ζ :=
  Lemma68ShellHoneInst.radius_le_countThreshold_of_oneTest hq0
    (MatedCRT.Lemma68HoneSetup.q0_le_one_of_shellChone hq0c) hζ0 hζ1 hRA le_rfl

open Classical in
/-- **`hcap` at one environment.** The binder `hcap` of `shellOneTest_at_of_goodEnv'`: for every centre `z`, the cap
radius of the vertices of `i.A` whose cells meet `ball z r` is below `r`. It uses only the continuity of `η ω`
(part of `RegularEnvAt68`, B1Assembly68.lean:561) and `0 < r`; the premise `FullAdmAt` is not used. -/
theorem hcap_of_continuous {γ ρ s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hηω : Continuous (S.η ω)) (hε : 0 < ε) (hr : 0 < r) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r :=
  fun _ z => MatedCRT.Lemma68HoneSetup239.cRad_lt_of_subset_cellVertices_ball (z := z) hηω hε hr
    (fun _ hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2)

open Classical in
/-- **`hcap_of_continuous` with a free `s1`.** Copy of `hcap_of_continuous` (l.47) with
`sparsityS1 γ` replaced by a parameter `s1`. The proof ignores the `FullAdmAt` premise, so no hypothesis on `s1` is
needed. -/
theorem hcap_of_continuous_s1 {γ ρ s₀ ε r s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hηω : Continuous (S.η ω)) (hε : 0 < ε) (hr : 0 < r) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r :=
  fun _ z => MatedCRT.Lemma68HoneSetup239.cRad_lt_of_subset_cellVertices_ball (z := z) hηω hε hr
    (fun _ hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2)

/-- `shellC068 = exp(-2)/32 ≤ 1`, the constant `c₀ = K.c0` of the leaf constants (`shellK68_params`). -/
theorem shellC068_le_one_adapt : shellC068 ≤ 1 := by
  unfold shellC068
  have h1 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

/-- **`hmesh` in the ball form, from the mesh event.** Let `ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε`. Its cell-size component is
`cellSizeEvent68 S γ ζ ρ ε` (radius `ρ`, Guard68S10.lean:45), so every cell meeting `ball 0 ρ` has
`diam ≤ ε^{2/(2+γ)² - ζ}` and is bounded (its diameter is positive by the lower bound of the event). With the binder
`hεcell : ε^κ ≤ c₀ r²/100` of `shellOneTest_at_of_goodEnv'`, `c₀ ≤ 1`, `r ≤ ρ/4 < 1`, and `dyadicD r ≥ r²`
(`sq_le_dyadicD`), the diameter of each such cell is at most `dyadicD r / 100`.
No cutoff in `ε` and no `2 ω₀ < κ` condition is used: the bound is the binder `hεcell`. The radius of the ball is `ρ`,
the radius of the cell-size event of `meshEvent`; the mesh radius `(1+ρ)/2` of `hmesh_local_of_cellSize` is not needed here. -/
theorem cellDiamLe_ball_of_meshEvent {γ ω₀ ρ CG ζ α CE : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε c0 r : ℝ} (ω : Ω) (hω : ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε) (hε : 0 < ε) (hρ1 : ρ < 1) (hr : 0 < r)
    (hrρ : r ≤ ρ / 4) (hc0 : c0 ≤ 1) (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ c0 * r ^ 2 / 100) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball 0 ρ) := by
  have hcell : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := by
    unfold meshEvent at hω
    exact hω.1.2
  have hr1 : r ≤ 1 := by linarith
  have hbdd : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      Bornology.IsBounded (cell ε (S.η ω) k) := by
    intro k hk
    by_contra hnb
    have hlow := (hcell k hk).1
    rw [diam_eq_zero_of_unbounded hnb] at hlow
    exact absurd hlow (not_le.mpr (Real.rpow_pos_of_pos hε _))
  have hbound : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ dyadicD r / 100 := by
    have hsq : r ^ 2 ≤ dyadicD r := sq_le_dyadicD hr hr1
    have hc : c0 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (sq_nonneg r) hc0
    linarith
  unfold CellDiamLe
  intro k hk p hp q hq
  calc dist p q ≤ diam (cell ε (S.η ω) k) := Metric.dist_le_diam_of_mem (hbdd k hk) hp hq
    _ ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) := (hcell k hk).2
    _ ≤ dyadicD r / 100 := hbound

open Classical in
/-- **`hcap_of_continuous` with a free `s1` and a free window constant (`_g`).** The statement
of `hcap_of_continuous` (l.47) involves neither the sparsity exponent nor any window constant (`cRad` of the cell
vertices of `i.A` meeting `ball z r`), so the `_g` variant is `hcap_of_continuous_s1` (l.58) with `c0W` absent; the
`FullAdmAt` premise is ignored as before. No hypothesis on `s1` is used. -/
theorem hcap_of_continuous_g {γ ρ s₀ ε r s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (hηω : Continuous (S.η ω)) (hε : 0 < ε) (hr : 0 < r) (i : Lemma68Config.Config68) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r :=
  hcap_of_continuous_s1 S ω hηω hε hr i

end Lemma68HoneSetupAdapt
end MatedCRT

#print axioms MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp
#print axioms MatedCRT.Lemma68HoneSetupAdapt.hcap_of_continuous
#print axioms MatedCRT.Lemma68HoneSetupAdapt.shellC068_le_one_adapt
#print axioms MatedCRT.Lemma68HoneSetupAdapt.cellDiamLe_ball_of_meshEvent

#print axioms MatedCRT.Lemma68HoneSetupAdapt.hcap_of_continuous_s1

#print axioms MatedCRT.Lemma68HoneSetupAdapt.hcap_of_continuous_g
