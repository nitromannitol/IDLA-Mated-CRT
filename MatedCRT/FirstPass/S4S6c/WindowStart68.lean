import MatedCRT.FirstPass.S6n
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S4S6c.ShellOrderWindow68

/-!
# The start cell meets the frontier of the `r/2`-thickening, under the full guard

The binder `hstart` of `shellOrderAe_window` (ShellOrderWindow68.lean:39-40) asks that the start cell
`H^ε_a` (`a = i.a`) meets the frontier of `thickening (r/2) (fillCells ε η Θ)` (`Θ = i.Θ`).

* The deterministic core `cell_meets_frontier_thickening`: if `2 dd_a ≤ r ≤ 2 M_a` (the bounds of the
  admissibility `Admissible` at radius `r`, S6e/Admissible.lean:46-50, `dd = cellDist`, `M = cellDistMax`), then the
  cell `H_a` contains a point at distance exactly `r/2` from the filled set `K = fillCells Θ`
  (`exists_mem_cell_infDist_eq`, the intermediate value theorem on the connected compact cell, S6n.lean:371), and a point
  at distance exactly `t > 0` from a compact nonempty `K` lies on the frontier of `thickening t K`
  (`frontier_thickening_eq`, S6n.lean:55).
* `hstart_fullAdm_ae`: the guarded form of `hstart`. Under the full guard `FullAdm` (S6h/Core.lean:46) the two
  bounds of `Admissible` at radius `r` give `2 dd_a ≤ r ≤ 2 M_a`, and `ConfigOK` gives `Θ ≠ ∅`
  (`ball 0 s₀ ⊆ fillCells Θ` with `s₀ > 0`). Continuity of `η` holds almost surely (`TraceInputs68.ae_continuous_eta`).

The unguarded `hstart` is NOT provable: if `i.a ∈ i.Θ` then `H_a ⊆ fillCells Θ ⊆ thickening (r/2) (fillCells Θ)`, an open
set, so `H_a` misses its frontier; and if `dd_a > r/2` the cell is too far from `K` to reach distance `r/2`. Hence the
binder of `shellOrderAe_window` must carry the guard `FullAdm` (the same guard as `htest` and `hde`). 
-/

open MeasureTheory Set Filter Topology Metric
open MatedCRT.Lemma68C12Geom
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry MatedCRT.Lemma68WindowRf

namespace MatedCRT
namespace Lemma68WindowStart

/-- A filled set `fillCells ε η Θ` of a finite vertex set is compact (finite union of compact cells). -/
theorem fillCells_isCompact {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (Θ : Finset ℤ) :
    IsCompact (fillCells ε η (↑Θ : Set ℤ)) :=
  (Finset.finite_toSet Θ).isCompact_biUnion fun k _ => cell_isCompact hη k

/-- **The start cell meets the frontier of the `r/2`-thickening (deterministic core).** If the start cell `H_a` has
cell distances `dd_a ≤ r/2 ≤ M_a` to the filled set `fillCells Θ` (Armstrong-Kuusi-Mourrat: the cell distance window of
the admissibility), then some point of `H_a` lies on the frontier of `thickening (r/2) (fillCells Θ)`. -/
theorem cell_meets_frontier_thickening {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hη : Continuous η)
    {Θ : Finset ℤ} (hΘ : Θ.Nonempty) {a : ℤ} {r : ℝ} (hr : 0 < r)
    (hlo : 2 * Lemma68Admissible.dd ε η Θ a ≤ r) (hhi : r ≤ 2 * Lemma68Admissible.ddMax ε η Θ a) :
    (cell ε η a ∩ frontier (thickening (r / 2) (fillCells ε η (↑Θ : Set ℤ)))).Nonempty := by
  obtain ⟨y, hy, hyd⟩ := exists_mem_cell_infDist_eq hε hη hΘ (a := a) (t := r / 2) (by linarith) (by linarith)
  have hne : (fillCells ε η (↑Θ : Set ℤ)).Nonempty :=
    closure_nonempty_iff.1 (clusterK_nonempty (η := η) hε hΘ)
  refine ⟨y, hy, ?_⟩
  rw [frontier_thickening_eq (fillCells_isCompact hη Θ) hne (by linarith : (0 : ℝ) < r / 2)]
  show infDist y (fillCells ε η (↑Θ : Set ℤ)) = r / 2
  rw [← infDist_closure]
  exact hyd

/-- **The guarded form of `hstart`, almost surely.** Under the full admissibility guard `FullAdm` at radius `r`, the
start cell `H^ε_{i.a}` meets the frontier of `thickening (r/2) (fillCells ε η i.Θ)`, for every configuration `i`. -/
theorem hstart_fullAdm_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {ρ s₀ ε r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hr : 0 < r)
    (i : Lemma68Config.Config68) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS] with ω hη hadm
  unfold Lemma68Config.FullAdmAt Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨-, -, hball⟩, hadm'⟩ := hadm
  obtain ⟨hlo, -, -⟩ := hadm'
  have hne : (fillCells ε (S.η ω) (↑i.Θ : Set ℤ)).Nonempty := ⟨0, hball (Metric.mem_ball_self hs₀)⟩
  have hΘ : i.Θ.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨k, hk, -⟩ := Set.mem_iUnion₂.1 (show z ∈ ⋃ k ∈ (↑i.Θ : Set ℤ), cell ε (S.η ω) k from hz)
    exact ⟨k, Finset.mem_coe.1 hk⟩
  exact cell_meets_frontier_thickening hε hη hΘ hr hlo.1 hlo.2

/-- **The window route of 6.8 with the guarded start cell discharged.** `shellOrderAe_window`
(ShellOrderWindow68.lean:34) with its binder `hstart` replaced by `hstart_fullAdm_ae`, the guarded start-cell fact
proved above. All other binders and the conclusion are those of `shellOrderAe_window`, unchanged. -/
theorem shellOrderAe_window_noStart {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r c₀ C : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω) k x ≠ ⊤) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c₀ C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a :=
  MatedCRT.Lemma68ShellOrderWindow.shellOrderAe_window hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i hmesh
    (hstart_fullAdm_ae S hS hε hs₀ hr i) htest

#print axioms MatedCRT.Lemma68WindowStart.cell_meets_frontier_thickening
#print axioms MatedCRT.Lemma68WindowStart.hstart_fullAdm_ae
#print axioms MatedCRT.Lemma68WindowStart.shellOrderAe_window_noStart

end Lemma68WindowStart
end MatedCRT
