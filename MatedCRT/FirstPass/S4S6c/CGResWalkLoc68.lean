import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.B1EnvPwG68
import MatedCRT.FirstPass.S4S6c.B1EnvPw68
import MatedCRT.FirstPass.S4S6c.WalkLoc68
import MatedCRT.FirstPass.S4S6c.HoneWalkAe68
import MatedCRT.FirstPass.S4S6c.HoneSetupAdapt68
import MatedCRT.FirstPass.S4S6c.CGResGreenWalk68

/-!
# The CG walk producers with the ball-form mesh

`hWalk_ae_of_walk_loc` and `hWalk_pw_g_loc`: copies of `HoneWalkAe68.hWalk_ae_of_walk` and of
`B1EnvPwG68.hWalk_pw_g` whose univ-form mesh `CellDiamLe … Set.univ` is replaced by the ball form
`CellDiamLe ε η (d/100) (ball 0 ρmesh)` with the gap `d/100 ≤ ρmesh - ρ`. The hit-cell interiority and the
exit-cell bounds use the ball-form lemmas of WalkLoc68 (`shellHit_interior_of_mesh_loc`, `hb_ae_of_walk_loc`,
`hEl_ae_of_walk_loc`); `exitVertex_mem_ball_of_sphere` only sees the cells meeting `ball 0 ρ`.
-/

namespace MatedCRT
namespace Lemma68CGResWalkLoc

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly
open Lemma68ShellCoreCG

/-- **`ε^e ≤ r²/100` on the premise.** From `2ω₀ < e` (so `ε^e ≤ ε^(2ω₀) = (ε^ω₀)²`, `ε ≤ 1`) and
`10 ε^ω₀ ≤ r`. Stated with `c0 := 1` for `cellDiamLe_rhoCell_of_meshEventR`. -/
theorem eps_rpow_le_div_hundred {ε ω0 e r : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hr10 : 10 * ε ^ ω0 ≤ r) (hω : 2 * ω0 < e) : ε ^ e ≤ 1 * r ^ 2 / 100 := by
  have h1 : ε ^ e ≤ ε ^ (2 * ω0) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hω.le
  have hsq : ε ^ (2 * ω0) = (ε ^ ω0) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    congr 1
    push_cast
    ring
  have hpos : 0 ≤ ε ^ ω0 := Real.rpow_nonneg hε0.le _
  have hle : ε ^ ω0 ≤ r / 10 := by linarith
  have h2 : (ε ^ ω0) ^ 2 ≤ (r / 10) ^ 2 := by nlinarith
  have h3 : (r / 10) ^ 2 = r ^ 2 / 100 := by ring
  rw [one_mul]
  linarith

/-- **`hb` almost surely, with the ball mesh (walk producer).** Copy of `HoneWalkAe68.hWalk_ae_of_walk` with the
univ mesh replaced by `CellDiamLe ε η (d/100) (ball 0 ρmesh)` and the gap `hgapM`. The exponent `K.ω` is unchanged. -/
theorem hWalk_ae_of_walk_loc {γ ρc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {m : ℤ → ℤ → ℕ} (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (s0 : ℤ)
    {Θ F0 : Finset ℤ} {ρ r d a s ρmom ω0 ρmesh : ℝ} {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d) (hdr : r ^ 2 ≤ d) (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000)
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20) (hs : s = d ^ a)
    (hr10 : 10 * ε ^ ω0 ≤ r) (hω0 : 2 * ω0 < K.ω) (hgap : ρ ≤ ρmom)
    (hgapM : d / 100 ≤ ρmesh - ρ)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRf : ∀ z ∈ shortEligible ρ d a, d ≤ Rf z ∧ Rf z ≤ d ^ a)
    (hst : (cell ε η s0 ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hdeg : ∀ v : ℤ, edgeMeasure m v univ ≠ 0 ∧ edgeMeasure m v univ ≠ ⊤) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k) τU →
        vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k x).toNat) ∈
            ball (0 : ℂ) (ρmom - Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 4) ∧
          ε ^ K.ω ≤ Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 8 := by
  have hPath := MatedCRT.Lemma68HoneGoodEventAe.walk_inputs_ae hη hε hp hedge hlf hcons s0 hF0 hst
  have hadjC : ∀ u v : ℤ, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty :=
    fun u v h => Set.Nonempty.mono (Set.inter_subset_inter subset_closure subset_closure) (hedge u v h)
  have hEl := MatedCRT.Lemma68WalkLoc.hEl_ae_of_walk_loc (A := A) (τU := τU) hη hε hr hrρ hd hds hs4 hNs hs
    hgapM hmesh hF0 h0 hKb hRf hPath
  have hR : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k) τU →
        d ≤ Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) :=
    fun k hk => (hEl k hk).mono fun x hx hxm => (hRf _ (hx hxm)).1
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.rpow_nonneg hd.le _
  have hNs' : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20 := by rw [hs]; exact hNs
  have hb := MatedCRT.Lemma68WalkLoc.hb_ae_of_walk_loc hη hε (fillCells ε η ↑Θ)
    (Z := fun k x => shellCentre ε η (fillCells ε η ↑Θ) r s d k x) m s0 n hdeg hadjC (fun _ _ => rfl)
    hd ⟨0, h0⟩ hKb hr hrρ hs0 hNs' hgapM hmesh hR
  intro k hk
  filter_upwards [hb k hk, hEl k hk] with x hbx helx hpre
  have hbx' : (cell ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k x).toNat) ∩
      Metric.sphere (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
        (4 * Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3)).Nonempty := hbx hpre
  have hz : shellCentre ε η (fillCells ε η ↑Θ) r s d k x ∈ shortEligible ρ d a := helx hpre
  have hRz := hRf _ hz
  have hρle : ρ ≤ ρmesh := by
    have h0' : 0 ≤ d / 100 := div_nonneg hd.le (by norm_num)
    linarith
  have hmeshLoc : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε η k', ∀ q ∈ cell ε η k', dist p q ≤ d / 100 :=
    fun k' hk' => hmesh k' (Set.Nonempty.mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hρle)) hk')
  have hv := MatedCRT.Lemma68HoneWalkAe.exitVertex_mem_ball_of_sphere hε
    (x (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k x).toNat) hd hds hRz.2 hgap hz hmeshLoc hbx'
  have hR8 := MatedCRT.Lemma68HoneWalkAe.eps_pow_le_eighth_of_radius hε hε1 hr10 hω0 (hdr.trans hRz.1)
  exact ⟨hv, hR8⟩

/-- **`hWalk_pw_g` with the ball-form mesh (`hWalk_pw_g_loc`).** Copy of `B1EnvPwG68.hWalk_pw_g` (l.120): the mesh is
`CellDiamLe ε (S.η ω) (dyadicD r / 100) (ball 0 (rhoCell68 ρ))` with the gap `hgapM`; the walk producer is
`hWalk_ae_of_walk_loc`. Same conclusion, exponent `K.ω`. -/
theorem hWalk_pw_g_loc {γ ρ ζ C CG α CE s₀ ε r ω₀ ωm s1 c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hs₀ : 0 < s₀)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hωm : 2 * ωm < K.ω) (hr10 : 10 * ε ^ ωm ≤ r) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat)) (sphere 0 ρ) := by
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
  have hst := Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1 S hε hs₀ ω hcont r hr0 i hFA
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ∧
        windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hdpos hd1 ha1 ω hz
  have hW := hWalk_ae_of_walk_loc (ε := ε) (η := S.η ω) K hcont hε hε1 hp hedge hlf hcons i.a
    (Θ := i.Θ) (F0 := i.F0) (ρ := ρ) (r := r) (d := dyadicD r) (a := shortExp ζ)
    (s := dyadicD r ^ shortExp ζ) (ρmom := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (ω0 := ωm)
    (Rf := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hr0 hrρ hdpos hdr hds hs4 hNs rfl hr10 hωm le_rfl hgapM hmesh hF0 h0 hKb hRf hst hdeg
  intro k hk
  filter_upwards [hW k hk] with x hx hpre
  obtain ⟨hv, hR8⟩ := hx hpre
  obtain ⟨hcv, hinf⟩ := MatedCRT.Lemma68B1EnvPw.walk_conclusion_of_ball hε hρ0 hv hR8 (Real.rpow_pos_of_pos hε _)
  exact ⟨hcv, hR8, hinf⟩

end Lemma68CGResWalkLoc
end MatedCRT

#print axioms MatedCRT.Lemma68CGResWalkLoc.eps_rpow_le_div_hundred
#print axioms MatedCRT.Lemma68CGResWalkLoc.hWalk_ae_of_walk_loc
#print axioms MatedCRT.Lemma68CGResWalkLoc.hWalk_pw_g_loc
