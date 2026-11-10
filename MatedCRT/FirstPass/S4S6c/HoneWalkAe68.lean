import MatedCRT.FirstPass.S4S6c.HoneGoodEventAe68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.HoneInputsDirect

/-!
# Walk-a.s. prefix forms of `hWalk` and `hx1` (fp-S4S6c-hwalk-prefix, z10)

Chat 239 section 5 (`notes/fp-gaps/CHATGPT-239-idla-hU-named-inputs-PRO.md` l.783-801) retires the universal-path
form of `hWalk` and `hx1` (not derivable) and retains the prefix form
`∀ᵐ x ∂srwLaw m i.a, x ∈ prefixSet … → vertexPoint ε η (x (T k x).toNat) ∈ ball 0 (ρmom - R k x / 4) ∧ ε ^ K.ω ≤ R k x / 8`.
Here `T k x = shellExit … k x` and `R k x = Rf (shellCentre … k x)`. The radius `ρmom` is deterministic; `hx1` is the
case `ρmom = 1` of the first conjunct, and the deterministic gap cutoff is `ρ ≤ ρmom`.

Proof of the first conjunct (`exitVertex_mem_ball_of_sphere`):
* the shell centre `z` is eligible, `‖z‖ < ρ - 3 d^a` (`shortEligible`, ShortWindow.lean:54);
* the exit cell meets the sphere `∂B(z, 4R/3)` (`hb_ae_of_walk`, HoneExitGeom68.lean:264; this is the a.s. `hb`);
* the vertex `v = vertexPoint ε η (x T)` lies in the exit cell, whose points are `d/100`-close (localized cell diameter),
  and `d ≤ R ≤ d^a`, so `‖v‖ ≤ ‖z‖ + 4R/3 + d/100` and the gap `ρ ≤ ρmom` absorbs `R/4`.

Proof of the second conjunct (`eps_pow_le_eighth_of_radius`): `R ≥ d ≥ r² ≥ 100 ε^{2ω₀}` and `2ω₀ < K.ω`.

Named inputs (all already binders of the B1 chain, none new): the walk inputs of `walk_inputs_ae` (`hp`, `hedge`, `hlf`,
`hcons`, `hst`), `hdeg` (`hb_ae_of_walk`), `hmesh` (the grid mesh `CellDiamLe (d/100) univ` of `hEl_ae_of_walk`), `hF0`,
`h0`, `hKb`, `hRf`, `hr10`, `hω0`, and the gap `hgap : ρ ≤ ρmom`. The hit-cell interiority `hhit` of `hb_ae_of_walk` is
not an input: it is derived from `hmesh` and `d ≤ Rf` (`shellHit_interior_of_mesh`, HoneExitGeom68). The core lemma
`exitVertex_mem_ball_of_sphere` needs only the mesh on `B_ρ`, not the global one.

Terminology: Duplantier-Sheffield (mated-CRT shells, the walk exit of an annulus), Armitage-Gardiner (balls, spheres).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneWalkAe

open Lemma68Window Lemma68Omega Lemma68ShellChain Lemma68WindowRf
open MatedCRT.Lemma68HoneGoodEvent

variable {γ ρc : ℝ}

/-- **First conjunct, deterministic core.** Let `z` be an eligible shell centre (`z ∈ shortEligible ρ d a`) with
radius `R ∈ [d, d^a]`, and let the vertex `j` have a cell meeting the sphere `∂B(z, 4R/3)`. If the cells meeting
`B_ρ` have all their points `d/100`-close (localized cell diameter), then `vertexPoint ε η j ∈ B(0, ρmom - R/4)`
whenever `ρ ≤ ρmom` (the deterministic gap cutoff). Proof: `‖p‖ ≤ ‖z‖ + 4R/3` for a sphere point `p` of the cell, the
vertex `v` lies in the same cell so `‖v - p‖ ≤ d/100 ≤ R/100`, and `‖z‖ < ρ - 3 d^a` with `R ≤ d^a`. -/
theorem exitVertex_mem_ball_of_sphere {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) {ρ d a ρmom R : ℝ} {z : ℂ} (j : ℤ)
    (hd : 0 < d) (hds : d ≤ d ^ a) (hRa : R ≤ d ^ a) (hgap : ρ ≤ ρmom)
    (hz : z ∈ shortEligible ρ d a)
    (hmesh : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε η k', ∀ q ∈ cell ε η k', dist p q ≤ d / 100)
    (hk : (cell ε η j ∩ Metric.sphere z (4 * R / 3)).Nonempty) :
    vertexPoint ε η j ∈ ball (0 : ℂ) (ρmom - R / 4) := by
  obtain ⟨p, hpc, hps⟩ := hk
  have hz1 : ‖z‖ < ρ - 3 * d ^ a := mem_ball_zero_iff.mp hz.1.1
  have hda : 0 ≤ d ^ a := Real.rpow_nonneg hd.le _
  have hpz : dist p z = 4 * R / 3 := Metric.mem_sphere.mp hps
  have hpn : ‖p‖ ≤ ‖z‖ + 4 * R / 3 := by
    have h := norm_sub_norm_le p z
    rw [← dist_eq_norm, hpz] at h
    linarith
  have hpball : p ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]
    linarith
  have hv : vertexPoint ε η j ∈ cell ε η j := MatedCRT.Lemma68Window.vertexPoint_mem_cell_direct hε j
  have hvp : dist (vertexPoint ε η j) p ≤ d / 100 := hmesh j ⟨p, hpc, hpball⟩ _ hv _ hpc
  have hvn : ‖vertexPoint ε η j‖ ≤ dist (vertexPoint ε η j) p + ‖p‖ := by
    have h := norm_add_le (vertexPoint ε η j - p) p
    rw [sub_add_cancel] at h
    rw [dist_eq_norm]
    exact h
  rw [mem_ball_zero_iff]
  linarith

/-- **Second conjunct, deterministic.** If `10 ε^{ω₀} ≤ r`, `2ω₀ < ω`, `0 < ε ≤ 1` and `r² ≤ R`, then
`ε^ω ≤ R/8`. Proof: `ε^ω ≤ ε^{2ω₀}` (base `≤ 1`), and `100 ε^{2ω₀} = (10 ε^{ω₀})² ≤ r² ≤ R`. -/
theorem eps_pow_le_eighth_of_radius {ε ω0 ω r R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr10 : 10 * ε ^ ω0 ≤ r)
    (hω : 2 * ω0 < ω) (hrR : r ^ 2 ≤ R) : ε ^ ω ≤ R / 8 := by
  have hsq : (ε ^ ω0) ^ 2 = ε ^ (2 * ω0) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have h100 : 100 * ε ^ (2 * ω0) ≤ r ^ 2 := by
    have h0 : 0 ≤ 10 * ε ^ ω0 := mul_nonneg (by norm_num) (Real.rpow_nonneg hε.le _)
    have h1 : (10 * ε ^ ω0) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hr10 2
    have h2 : (10 * ε ^ ω0) ^ 2 = 100 * ε ^ (2 * ω0) := by
      rw [mul_pow, hsq]
      norm_num
    linarith
  have hmono : ε ^ ω ≤ ε ^ (2 * ω0) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hω.le
  have hR0 : 0 ≤ R := le_trans (sq_nonneg r) hrR
  linarith

/-- **`hWalk` and `hx1` in the walk-a.s. prefix form (chat 239 l.787-793).** Under the walk law `srwLaw m s0`,
for every shell `k ≤ n`, almost surely on the prefix set `prefixSet … (shellExit … k) τU`: the exit vertex
`x (T k x).toNat` lies in `B(0, ρmom - R k x / 4)` and `ε^{K.ω} ≤ R k x / 8`, where `R k x = Rf (shellCentre … k x)`.
The radius `ρmom` is any deterministic radius with `ρ ≤ ρmom` (the gap cutoff; the consumer takes `ρmom < 1`).

Proof: `hb_ae_of_walk` (a.s. exit cell meets `∂B(z, 4R/3)`) and `hEl_ae_of_walk` (a.s. `z ∈ shortEligible ρ d a`) on
`k ≤ n`, then `exitVertex_mem_ball_of_sphere` and `eps_pow_le_eighth_of_radius`, with `d ≤ R` and `r² ≤ d`
(`dyadicD`, `r² ≤ d < 2r²`). The per-path inputs of `hEl` are `walk_inputs_ae`. -/
theorem hWalk_ae_of_walk (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {m : ℤ → ℤ → ℕ} (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (s0 : ℤ)
    {Θ F0 : Finset ℤ} {ρ r d a s ρmom ω0 : ℝ} {Rf : ℂ → ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d) (hdr : r ^ 2 ≤ d) (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000)
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20) (hs : s = d ^ a)
    (hr10 : 10 * ε ^ ω0 ≤ r) (hω0 : 2 * ω0 < K.ω) (hgap : ρ ≤ ρmom)
    (hmesh : CellDiamLe ε η (d / 100) Set.univ)
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
  have hEl := MatedCRT.Lemma68HoneGoodEventAe.hEl_ae_of_walk (A := A) (τU := τU) hη hε hr hrρ hd hds hs4 hNs hs
    hmesh hF0 h0 hKb hRf hPath
  -- the hit-cell interiority, from the mesh and `d ≤ Rf` at the eligible centre (`shellHit_interior_of_mesh`)
  have hhit : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m s0,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k) τU →
      ∀ t : ℕ, shellHit ε η (fillCells ε η ↑Θ) r s k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε η
          (ball (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) (4 * Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3)) :=
    fun k hk => (hEl k hk).mono fun x hx hxm t ht =>
      MatedCRT.Lemma68HoneExitGeom.shellHit_interior_of_mesh hε (fillCells ε η ↑Θ) hd hmesh k x
        (hRf _ (hx hxm)).1 t ht
  have hb := MatedCRT.Lemma68HoneExitGeom.hb_ae_of_walk hη (fillCells ε η ↑Θ)
    (Z := fun k x => shellCentre ε η (fillCells ε η ↑Θ) r s d k x) m s0 n hdeg hadjC (fun _ _ => rfl) hhit
  intro k hk
  filter_upwards [hb k hk, hEl k hk] with x hbx helx hpre
  have hbx' : (cell ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k x).toNat) ∩
      Metric.sphere (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
        (4 * Rf (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3)).Nonempty := hbx hpre
  have hz : shellCentre ε η (fillCells ε η ↑Θ) r s d k x ∈ shortEligible ρ d a := helx hpre
  have hRz := hRf _ hz
  have hmeshLoc : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ p ∈ cell ε η k', ∀ q ∈ cell ε η k', dist p q ≤ d / 100 :=
    fun k' hk' => hmesh k' (Set.Nonempty.mono (Set.inter_subset_inter_right _ (Set.subset_univ _)) hk')
  have hv := exitVertex_mem_ball_of_sphere hε (x (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k x).toNat) hd hds
    hRz.2 hgap hz hmeshLoc hbx'
  have hR8 := eps_pow_le_eighth_of_radius hε hε1 hr10 hω0 (hdr.trans hRz.1)
  exact ⟨hv, hR8⟩

end Lemma68HoneWalkAe
end MatedCRT

#print axioms MatedCRT.Lemma68HoneWalkAe.exitVertex_mem_ball_of_sphere
#print axioms MatedCRT.Lemma68HoneWalkAe.eps_pow_le_eighth_of_radius
#print axioms MatedCRT.Lemma68HoneWalkAe.hWalk_ae_of_walk
