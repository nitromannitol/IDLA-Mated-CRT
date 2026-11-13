import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HoneEnvEvents68
import MatedCRT.FirstPass.S4S6c.HoneWalkAe68
import MatedCRT.FirstPass.S4S6c.HoneRcell68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S6e.Geometry
/-!
# Pointwise environment adapters for the binders of the one-radius assembly

Each theorem here has as conclusion exactly one binder of the one-radius assembly (B1Assembly68.lean),
at one environment point `ω`: `hGreen` (l.874), `hCountGood` (l.881), `hRcell` (l.888) and `hWalk` (l.909). The
almost-sure producers filter over the good events and the regularity of the environment; here each such fact is an
explicit pointwise hypothesis at `ω`:
* `hGreen_pw`: membership of `ω` in the good Green event `greenLowerGoodEvent` (HoneModelInputs68.lean:36), the body of
  `GreenKernelLowerBoundStmt`; the proof is `HoneEnvEvents68.hGreen_of_mem`.
* `hCountGood_pw`: membership of `ω` in the good counting event `countingGoodEvent` (HoneModelInputs68.lean:48) at the
  test function `f ≡ 1`, for `0 < ε ≤ 1` and `0 ≤ β` (so that `ε ^ (-β) ≥ 1`).
* `hRcell_pw`: the cell-control radius bound `Lemma68RcellDischarge.hRcell_of_eligible` (HoneRcell68.lean:53), from the
  pointwise centre eligibility `hEl`, the radius bound of the window radius on the eligible centres, and the
  deterministic cutoff `hcut` (named, see the gap note below).
* `hWalk_pw`: the walk producer `Lemma68HoneWalkAe.hWalk_ae_of_walk` (HoneWalkAe68.lean:103) at `ρmom := ρ`, with the
  environment inputs (continuity, cocompact escape, local finiteness, cell adjacency, edge degrees) taken from
  `RegularEnvAt68` (B1Assembly68.lean:558), and the radius inputs from the dyadic and shell-count bounds.

Named gaps (not derivable from the hypotheses of the one-radius assembly; kept as explicit hypotheses):
* `hcut` in `hRcell_pw`: `dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ`. The target gives only `r ≤ ρ / 4`; the cutoff
  lemma `Guard68S10.lean:477-482` needs `r ≤ Rc(ρ)`.
* `hωm`, `hr10` in `hWalk_pw`: the walk producer's second conjunct `ε ^ K.ω ≤ winRf/8` needs `10 * ε ^ ωm ≤ r` with
  `2 * ωm < K.ω`. The target gives only `10 * ε ^ K.ω ≤ r`, which does not imply it.

Terminology: polynomially high probability (Armstrong-Kuusi-Mourrat), Lemma 2.9 and 2.16 (Berestycki-Gwynne;
Berestycki-Powell), Duplantier-Sheffield (mated-CRT shells), Armitage-Gardiner (balls, spheres, Green kernel).
-/
open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68B1EnvPw

open MatedCRT.Lemma68B1Assembly
open MatedCRT.Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **Binder `hGreen` of the one-radius assembly at one point `ω`.** The lower Green bound (Lemma 2.16,
Berestycki-Powell) on the good event `greenLowerGoodEvent K.ω K.C ρ S ε` at `ω` (HoneEnvEvents68.hGreen_of_mem). -/
theorem hGreen_pw {γ ρ s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hω : ω ∈ HoneModelInputs68.greenLowerGoodEvent K.ω K.C ρ S ε) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b :=
  fun _ => HoneEnvEvents68.hGreen_of_mem hω

/-- **Binder `hCountGood` of the one-radius assembly at one point `ω`.** The counting bound (Lemma 2.9,
Berestycki-Gwynne) on the good event `countingGoodEvent S α β ρ ε` at `ω`, at the test function `f ≡ 1`. The bounds
`0 ≤ 1` and `1 ≤ ε ^ (-β)` need `0 < ε ≤ 1` and `0 ≤ β`; the Lipschitz bound is trivial. -/
theorem hCountGood_pw {γ ρ s₀ ε r α β : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : ω ∈ HoneModelInputs68.countingGoodEvent S α β ρ ε) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ) := by
  intro _ D hD w hw
  have hpow : (1 : ℝ) ≤ ε ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hbound : ∀ x ∈ thickening (ε ^ α) D, 0 ≤ (fun _ : ℂ => (1 : ℝ)) x ∧
      |(fun _ : ℂ => (1 : ℝ)) x| ≤ ε ^ (-β) := fun _ _ => by
    show 0 ≤ (1 : ℝ) ∧ |(1 : ℝ)| ≤ ε ^ (-β)
    rw [abs_one]
    exact ⟨zero_le_one, hpow⟩
  have hlip : ∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D,
      |(fun _ : ℂ => (1 : ℝ)) x - (fun _ : ℂ => (1 : ℝ)) y| ≤ ε ^ (-β) * ‖x - y‖ := fun x _ y _ => by
    show |(1 : ℝ) - 1| ≤ ε ^ (-β) * ‖x - y‖
    rw [sub_self, abs_zero]
    exact mul_nonneg (zero_le_one.trans hpow) (norm_nonneg _)
  exact (hω D (fun _ => (1 : ℝ)) w hD hbound hlip hw).1

/-- The cutoff form of `hRcell` at one point `ω`: the eligibility binder `hEl` (pointwise), the window-radius bound
`winRf z ≤ dyadicD r ^ shortExp ζ` on the eligible centres (`windowRfT_bounds`, ShellWindowRf68.lean:65), and the
deterministic cutoff `hcut`, through `Lemma68RcellDischarge.hRcell_of_eligible` (HoneRcell68.lean:53). -/
theorem hRcell_pw {γ ρ ζ C s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hEl : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hcut : dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  intro hFA
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      winRf S ρ ζ C r ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd hd1 ha1 ω hz).2
  exact Lemma68RcellDischarge.hRcell_of_eligible (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (m := S.mult ε ω) (a0 := i.a) (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := winRf S ρ ζ C r ω)
    (sc := dyadicD r ^ shortExp ζ) (d := dyadicD r) (aW := shortExp ζ) (g := Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    hd hRf (hEl hFA) hcut

/-- The conclusion of `hWalk` from the walk form: the exit vertex `v = vertexPoint k` lies in `ball 0 (ρ - R/4)`, and
`e = ε ^ K.ω ≤ R/8`. Then `k` is a cell vertex of `ball 0 (ρ - e)` (the cell of `k` contains its vertex point) and
`R/8 ≤ infDist v (sphere 0 ρ)` (`‖v‖ < ρ - R/4` and `R > 0`). -/
theorem walk_conclusion_of_ball {ε ρ R e : ℝ} {η : ℝ → ℂ} {k : ℤ} (hε : 0 < ε) (hρ0 : 0 < ρ)
    (hv : vertexPoint ε η k ∈ ball (0 : ℂ) (ρ - R / 4)) (hR8 : e ≤ R / 8) (he : 0 < e) :
    k ∈ cellVertices ε η (ball (0 : ℂ) (ρ - e)) ∧
      R / 8 ≤ infDist (vertexPoint ε η k) (sphere (0 : ℂ) ρ) := by
  have hR : 0 < R := by linarith
  have hv' : ‖vertexPoint ε η k‖ < ρ - R / 4 := by simpa [mem_ball, dist_zero_right] using hv
  refine ⟨⟨vertexPoint ε η k, vertexPoint_mem_cell hε k, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    linarith
  · refine (le_infDist (NormedSpace.sphere_nonempty.2 (by linarith))).2 ?_
    intro y hy
    have hy' : ‖y‖ = ρ := by simpa using hy
    have h1 := norm_sub_norm_le y (vertexPoint ε η k)
    rw [dist_comm, dist_eq_norm]
    linarith

/-- **Binder `hWalk` of the one-radius assembly at one point `ω`.** The walk producer
`Lemma68HoneWalkAe.hWalk_ae_of_walk` at `ρmom := ρ`, with the environment inputs of `RegularEnvAt68` and the dyadic
and shell-count bounds. Named gap: the second conjunct needs `hωm : 2 * ωm < K.ω` and `hr10 : 10 * ε ^ ωm ≤ r`. -/
theorem hWalk_pw {γ ρ ζ C CG α CE s₀ ε r ω₀ ωm : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hs₀ : 0 < s₀)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hωm : 2 * ωm < K.ω) (hr10 : 10 * ε ^ ωm ≤ r) :
    Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ) := by
  intro hFA
  have hcont : Continuous (S.η ω) := hreg.2.2.2.1
  have hr1 : r ≤ 1 := by linarith
  have hdpos : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdpos hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hdpos hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hdpos _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hdpos hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hreg.2.1
  have hlf : IsLocallyFiniteMult (S.mult ε ω) := (hreg.2.2.1 ε hε).1
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := (hreg.2.2.1 ε hε).2
  have hedge : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => hreg.2.2.2.2.2.2.2.2 ε hε j k h
  have hdeg := hreg.2.2.2.2.2.2.1
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (ball 0 ρ) := hFA.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ ball (0 : ℂ) (ρ / 2) := subset_closure.trans hFA.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hFA.1.2.2 (mem_ball_self hs₀)
  have hst := Lemma68HoneSetup239.hstart_of_fullAdmAt S hε hs₀ ω hcont r hr0 i hFA
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ winRf S ρ ζ C r ω z ∧ winRf S ρ ζ C r ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hdpos hd1 ha1 ω hz
  have hW := Lemma68HoneWalkAe.hWalk_ae_of_walk (ε := ε) (η := S.η ω) K hcont hε hε1 hp hedge hlf hcons i.a
    (Θ := i.Θ) (F0 := i.F0) (ρ := ρ) (r := r) (d := dyadicD r) (a := shortExp ζ)
    (s := dyadicD r ^ shortExp ζ) (ρmom := ρ) (ω0 := ωm) (Rf := winRf S ρ ζ C r ω) (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hr0 hrρ hdpos hdr hds hs4 hNs rfl hr10 hωm le_rfl hmesh hF0 h0 hKb hRf hst hdeg
  intro k hk
  filter_upwards [hW k hk] with x hx hpre
  obtain ⟨hv, hR8⟩ := hx hpre
  obtain ⟨hcv, hinf⟩ := walk_conclusion_of_ball hε hρ0 hv hR8 (Real.rpow_pos_of_pos hε _)
  exact ⟨hcv, hR8, hinf⟩

end Lemma68B1EnvPw
end MatedCRT

#print axioms MatedCRT.Lemma68B1EnvPw.hGreen_pw
#print axioms MatedCRT.Lemma68B1EnvPw.hCountGood_pw
#print axioms MatedCRT.Lemma68B1EnvPw.hRcell_pw
#print axioms MatedCRT.Lemma68B1EnvPw.hWalk_pw
