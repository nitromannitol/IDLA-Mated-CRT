import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# The cell-control radius of the one-test bound: `hCellGood` at `ρ_cell` (fp-S4S6c-hone-cellgood, z1)

Chat 237, section 3 (`notes/fp-gaps/CHATGPT-237-idla-hU-s1-link-PRO.md`, l.260-369). The leaf binder
`hCellGood` of `shellOneTest_of_direct` (`S4S6c/ShellHoneInst68.lean:107`) is stated on the ball of radius `ρ_c + 3/8`,
which may exceed `1`; `CellSizeEstimateStmt` (Draft/Section2.lean:131, Berestycki-Gwynne Lemma 2.4 / Lemma 2.8) applies only
at radii strictly below `1`. The repair uses a separate cell-control radius

  `ρ_cell := (1 + ρ_c)/2`, so that `ρ_c < ρ_cell < 1`,

and a deterministic shell-radius cutoff `R/4 < ρ_cell - ρ_c`. Contents:

* `cellUpper_polyHighProb`: the cell event at `ρ_cell` from `CellSizeEstimateStmt`. It is a `PolyHighProb` statement
  about the upper cell-diameter bound `diam (cell ε η k) ≤ ε^(2/(2+γ)² - ζ)` on the cells meeting `B_ρ`.
* `vertexPoint_norm_lt_of_cell_meets`: a cell of diameter at most `δ` which meets `B_{ρ_c - δ}` has its vertex in `B_{ρ_c}`.
* `hdiam_test_ball_of_cellGood`: the test-ball bound `diam (cell k') ≤ c₀ R` for the cells meeting `B(x, R/4)`, from the
  cell bound on `B_{ρ_cell}`, when `‖x‖ < ρ_c` and `R/4 < ρ_cell - ρ_c` (chat 237, steps 4-5).
* `hdiam_test_ball_of_walk`: steps 1-5 of chat 237 assembled: the exit cell of the walk gives the test-ball bound.

The cell-diameter exponent is `κ = 2/(2+γ)² - ζ` (upper exponent of `CellSizeEstimateStmt`); the Green and exit estimates keep
the radius `ρ_c`. Terminology: cells `H^ε_a` (Armstrong-Kuusi-Mourrat), `PolyHighProb` (polynomially high probability),
test balls and the walk-centred one-test bound (Armstrong-Kuusi-Mourrat, Lemma 6.8).
-/

open MeasureTheory Set Filter Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT
namespace Lemma68HoneCellGood

/-- The cell-control radius `ρ_cell := (1 + ρ_c)/2` (chat 237, section 3). -/
noncomputable def rhoCell68 (ρc : ℝ) : ℝ := (1 + ρc) / 2

theorem rhoCell68_lt_one {ρc : ℝ} (h : ρc < 1) : rhoCell68 ρc < 1 := by
  unfold rhoCell68; linarith

theorem rhoC_lt_rhoCell68 {ρc : ℝ} (h : ρc < 1) : ρc < rhoCell68 ρc := by
  unfold rhoCell68; linarith

theorem rhoCell68_pos {ρc : ℝ} (h : 0 < ρc) : 0 < rhoCell68 ρc := by
  unfold rhoCell68; linarith

/-- **The cell event at `ρ` from `CellSizeEstimateStmt` (fp-S4S6c-hone-cellgood).** For a valid environment `S` and a
radius `ρ ∈ (0,1)`, the upper cell-diameter bound on the cells meeting `B_ρ` holds with polynomially high probability.
This is the upper half of `CellSizeEstimateStmt` (Draft/Section2.lean:131), with the lower half dropped by monotonicity
of `PolyHighProb` (a larger event has a smaller complement). -/
theorem cellUpper_polyHighProb {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ζ ρ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P (fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}) := by
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ := h28 γ hγ0 hγ2 ζ ρ hζ0 hζ1 hρ0 hρ1 Ω S hS
  refine ⟨p, hp, C, r₀, hr₀, fun r hr0 hr1 => ?_⟩
  refine le_trans (measure_mono (compl_subset_compl.2 ?_)) (hbound r hr0 hr1)
  intro ω hω k hk
  exact (hω k hk).2

/-- **A vertex of a small cell lies in `B_{ρ_c}` (chat 237, step 3).** If the cell of `k` has diameter at most `δ` and
meets `B_{ρ_c - δ}`, then the vertex `vertexPoint ε η k = η(εk)` lies in `B_{ρ_c}`. The vertex is an endpoint of the cell
(`η(εk)` with `ε ≥ 0`), so it is within `δ` of the cell point in `B_{ρ_c - δ}`. -/
theorem vertexPoint_norm_lt_of_cell_meets {ε ρc δ : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 ≤ ε) (k : ℤ)
    (hdiam : diam (cell ε η k) ≤ δ) (hk : (cell ε η k ∩ ball (0 : ℂ) (ρc - δ)).Nonempty) :
    ‖vertexPoint ε η k‖ < ρc := by
  obtain ⟨p, hpc, hpb⟩ := hk
  have hv : vertexPoint ε η k ∈ cell ε η k := by
    refine ⟨ε * (k : ℝ), ⟨?_, le_rfl⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hε
  have hd : dist (vertexPoint ε η k) p ≤ δ :=
    (Metric.dist_le_diam_of_mem (TraceInputs68.cell_isBounded hη k) hv hpc).trans hdiam
  have hp : ‖p‖ < ρc - δ := by simpa [mem_ball_zero_iff] using hpb
  have h3 : ‖vertexPoint ε η k‖ - ‖p‖ ≤ ‖vertexPoint ε η k - p‖ := norm_sub_norm_le _ _
  rw [← dist_eq_norm] at h3
  linarith

/-- **The test-ball cell bound from the cell bound on `B_{ρ_cell}` (chat 237, steps 4-5).** If `‖x‖ < ρ_c` and
`R/4 < ρ_cell - ρ_c`, every cell meeting the test ball `B(x, R/4)` meets `B_{ρ_cell}`, so the cell bound
`diam ≤ ε^κ` at `ρ_cell` applies to it; with `ε^κ ≤ c₀ R` this is `diam ≤ c₀ R`. -/
theorem hdiam_test_ball_of_cellGood {ε ρc ρcell κ c0 R : ℝ} {η : ℝ → ℂ} {x : ℂ} (hx : ‖x‖ < ρc)
    (hR : R / 4 < ρcell - ρc)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty → diam (cell ε η k') ≤ ε ^ κ)
    (hsmall : ε ^ κ ≤ c0 * R) :
    ∀ k : ℤ, (cell ε η k ∩ ball x (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R := by
  intro k hk
  obtain ⟨y, hyc, hyb⟩ := hk
  have hxd : dist x (0 : ℂ) < ρc := by rw [dist_zero_right]; exact hx
  have hyd : dist y (0 : ℂ) < ρcell := by
    have h1 : dist y x < R / 4 := hyb
    linarith [dist_triangle y x (0 : ℂ)]
  exact le_trans (hCellGood k ⟨y, hyc, mem_ball.2 hyd⟩) hsmall

/-- **The `ε^κ ≤ c₀ R` side condition from the minimal mesh (chat 237, step 5).** From `ε^κ ≤ rmin/100` and
`rmin ≤ c₀ R` (the binders `hεcell` and `hRmin` of `shellOneTest_of_direct`) with `c₀ R ≥ 0`. -/
theorem rpow_le_of_rmin {ε κ rmin c0 R : ℝ} (hεcell : ε ^ κ ≤ rmin / 100) (hRmin : rmin ≤ c0 * R)
    (hc : 0 ≤ c0 * R) : ε ^ κ ≤ c0 * R := by
  linarith

/-- **The cutoff `hRcell` (chat 237, deterministic cutoff).** If `0 ≤ R ≤ x < ρ_cell - ρ_c`, then `R/4 < ρ_cell - ρ_c`. -/
theorem div4_lt_of_cutoff {R x ρc ρcell : ℝ} (hR0 : 0 ≤ R) (hRx : R ≤ x) (hx : x < ρcell - ρc) :
    R / 4 < ρcell - ρc := by
  linarith

/-- **Steps 1-5 of chat 237, section 3, for the walk (fp-S4S6c-hone-cellgood).** Let `k` be the exit cell index of the
walk, with `hWalk : cell k ∩ B_{ρ_c - ε^e}` nonempty (`hWalk` of the one-test bound, `e = K.ω`). If `ε^κ ≤ ε^e` (from
`e ≤ κ`, `0 < ε ≤ 1`), the cell bound `hCellGood` at `ρ_cell` applies to the exit cell (step 2), its vertex lies in `B_{ρ_c}`
(step 3), and the cells meeting the test ball `B(vertexPoint k, R/4)` satisfy `diam ≤ c₀ R` (steps 4-5), given `R/4 < ρ_cell - ρ_c`
(the cutoff) and `ε^κ ≤ c₀ R`. -/
theorem hdiam_test_ball_of_walk {ε ρc ρcell κ e c0 R : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (he : e ≤ κ) (hρgap : ρc < ρcell) {k : ℤ}
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty → diam (cell ε η k') ≤ ε ^ κ)
    (hWalk : (cell ε η k ∩ ball (0 : ℂ) (ρc - ε ^ e)).Nonempty)
    (hR : R / 4 < ρcell - ρc) (hsmall : ε ^ κ ≤ c0 * R) :
    ∀ k' : ℤ, (cell ε η k' ∩ ball (vertexPoint ε η k) (R / 4)).Nonempty → diam (cell ε η k') ≤ c0 * R := by
  have hpos : 0 ≤ ε ^ e := Real.rpow_nonneg hε.le e
  have hmeet : (cell ε η k ∩ ball (0 : ℂ) ρcell).Nonempty :=
    hWalk.mono (inter_subset_inter_right _ (ball_subset_ball (by linarith)))
  have hκe : ε ^ κ ≤ ε ^ e := Real.rpow_le_rpow_of_exponent_ge hε hε1 he
  have hdk : diam (cell ε η k) ≤ ε ^ e := (hCellGood k hmeet).trans hκe
  have hv : ‖vertexPoint ε η k‖ < ρc :=
    vertexPoint_norm_lt_of_cell_meets hη hε.le k hdk hWalk
  exact hdiam_test_ball_of_cellGood hv hR hCellGood hsmall

end Lemma68HoneCellGood
end MatedCRT

#print axioms MatedCRT.Lemma68HoneCellGood.cellUpper_polyHighProb
#print axioms MatedCRT.Lemma68HoneCellGood.vertexPoint_norm_lt_of_cell_meets
#print axioms MatedCRT.Lemma68HoneCellGood.hdiam_test_ball_of_cellGood
#print axioms MatedCRT.Lemma68HoneCellGood.hdiam_test_ball_of_walk
#print axioms MatedCRT.Lemma68HoneCellGood.rpow_le_of_rmin
#print axioms MatedCRT.Lemma68HoneCellGood.div4_lt_of_cutoff
