import Mathlib
import MatedCRT.Defs.Map
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S6e.Inputs

/-!
# FIRST PASS: the geometric quantities of LEMMA68 (B2) (task fp-S6e-lemma68-C17, z9)

Source: `notes/fp-gaps/CHATGPT-z9-lemma68-B1B2.md` §4 (B2.1-B2.4, formulas (2)-(6)) and §5.1 (formula (9)).
Fixed mesh `ε > 0`; a vertex is an integer `k`, its cell is `H_k = cell ε η k = η([ε(k-1), εk])` (`MatedCRT.cell`),
and `D_k = I_k ∩ ℚ` (`ratInt`). The quantities of the write-up are given by their countable formulas (3)-(6), with
values in `ℝ≥0∞` (an empty infimum is `⊤`, an empty supremum `0`):
* `cellDist ε η Θ k` = `d_k`, the distance of `H_k` to the filled set `K = ⋃_{w ∈ Θ} H_w` (formula (3));
* `cellDistMax ε η Θ k` = `M_k`, the maximal distance of `H_k` to `K` (formula (4));
* `capRadius ε η B` = `c_B` (formula (5));
* `ballMeetCriterion ε η ρ k` = `k ∈ V(B_ρ)` (formula (6)).
The countable formulas are measurable in `ω` whenever `ω ↦ η ω q` is measurable at every rational `q` (no regularity
event is needed for measurability). Their agreement with the geometric definitions for continuous `η` (B2.1 (1)-(2))
is NOT proved in this file. Finiteness of `V(B_ρ)` uses properness, which follows from `CurveEscapesBothEnds`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Geometry

/-- The rational parameters `D_k = I_k ∩ ℚ` of the cell `k`, `I_k = [ε(k-1), εk]` (write-up B2). -/
def ratInt (ε : ℝ) (k : ℤ) : Set ℚ := {q | (q : ℝ) ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k)}

/-- Distance of `η q` to the filled set `K = ⋃_{w ∈ Θ} H_w`, through the dense parameters `D_w` (write-up (2)). -/
noncomputable def pointDist (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (q : ℚ) : ℝ≥0∞ :=
  ⨅ w : Θ, ⨅ t : ratInt ε w.1, edist (η q) (η (t : ℚ))

/-- `d_k = inf_{q ∈ D_k} dist(η q, K)`: the distance of the cell `H_k` to `K` (write-up (3)). -/
noncomputable def cellDist (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (k : ℤ) : ℝ≥0∞ :=
  ⨅ q : ratInt ε k, pointDist ε η Θ (q : ℚ)

/-- `M_k = sup_{q ∈ D_k} dist(η q, K)`: the maximal distance of the cell `H_k` to `K` (write-up (4)). -/
noncomputable def cellDistMax (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (k : ℤ) : ℝ≥0∞ :=
  ⨆ q : ratInt ε k, pointDist ε η Θ (q : ℚ)

/-- `c_B = inf_{z ∈ ℚ²} max_{v ∈ B} inf_{q ∈ D_v} |z − η q|`: the least radius of a ball centred at a rational point
meeting all cells of the finite set `B` (write-up (5)). -/
noncomputable def capRadius (ε : ℝ) (η : ℝ → ℂ) (B : Finset ℤ) : ℝ≥0∞ :=
  ⨅ z : ℚ × ℚ, ⨆ v : B, ⨅ q : ratInt ε v.1, edist (Complex.mk (z.1 : ℝ) (z.2 : ℝ)) (η (q : ℚ))

/-- The countable criterion `k ∈ V(B_ρ)` (write-up (6)): `inf_{q ∈ D_k} |η q| < ρ`. -/
def ballMeetCriterion (ε : ℝ) (η : ℝ → ℂ) (ρ : ℝ) (k : ℤ) : Prop :=
  ⨅ q : ratInt ε k, edist (η (q : ℚ)) 0 < ENNReal.ofReal ρ

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {η : Ω → ℝ → ℂ}

lemma measurable_pointDist (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ) (q : ℚ) :
    Measurable fun ω => pointDist ε (η ω) Θ q := by
  unfold pointDist
  exact Measurable.iInf fun w => Measurable.iInf fun t => (hη q).edist (hη (t : ℚ))

lemma measurable_cellDist (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ) (k : ℤ) :
    Measurable fun ω => cellDist ε (η ω) Θ k := by
  unfold cellDist
  exact Measurable.iInf fun q => measurable_pointDist hη ε Θ (q : ℚ)

lemma measurable_cellDistMax (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ) (k : ℤ) :
    Measurable fun ω => cellDistMax ε (η ω) Θ k := by
  unfold cellDistMax
  exact Measurable.iSup fun q => measurable_pointDist hη ε Θ (q : ℚ)

lemma measurable_capRadius (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (B : Finset ℤ) :
    Measurable fun ω => capRadius ε (η ω) B := by
  unfold capRadius
  exact Measurable.iInf fun z => Measurable.iSup fun v =>
    Measurable.iInf fun q => (measurable_const).edist (hη (q : ℚ))

lemma measurableSet_ballMeetCriterion (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (ρ : ℝ)
    (k : ℤ) : MeasurableSet {ω | ballMeetCriterion ε (η ω) ρ k} := by
  have h : Measurable fun ω => ⨅ q : ratInt ε k, edist (η ω (q : ℚ)) 0 :=
    Measurable.iInf fun q => (hη (q : ℚ)).edist measurable_const
  exact measurableSet_lt h measurable_const

/-- Threshold events `d_k < R(ω)` are measurable for a measurable radius `R` (write-up Step 1 of §6). -/
lemma measurableSet_cellDist_lt (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ) (k : ℤ)
    {R : Ω → ℝ} (hR : Measurable R) :
    MeasurableSet {ω | cellDist ε (η ω) Θ k < ENNReal.ofReal (R ω)} :=
  measurableSet_lt (measurable_cellDist hη ε Θ k) (ENNReal.measurable_ofReal.comp hR)

end Measurability

/-- Properness of a curve that escapes both ends: `η` is proper, `Tendsto η (cocompact ℝ) (cocompact ℂ)`
(write-up §1.2, the short proof of B2.4). -/
theorem tendsto_cocompact_of_escapes {η : ℝ → ℂ} (h : Lemma68Inputs.CurveEscapesBothEnds η) :
    Tendsto η (cocompact ℝ) (cocompact ℂ) := by
  rw [hasBasis_cocompact.tendsto_iff hasBasis_cocompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨T, hT0, hT⟩ := h (max R 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨Icc (-T) T, isCompact_Icc, fun x hx => ?_⟩
  have hTx : T ≤ |x| := by
    rcases le_or_gt x (-T) with h1 | h1
    · exact le_abs.2 (Or.inr (by linarith))
    · rcases le_or_gt x T with h2 | h2
      · exact absurd ⟨by linarith, h2⟩ hx
      · exact le_abs.2 (Or.inl h2.le)
  intro hmem
  have hK' := hR hmem
  rw [mem_closedBall, dist_zero_right] at hK'
  have := hT x hTx
  linarith [le_max_left R 1]

/-- The vertices whose cells meet `B_ρ` are finite when `η` escapes both ends (write-up B2.4, via
`TraceInputs68.cellVertices_finite_of_tendsto`). -/
theorem cellVertices_ball_finite_of_escapes {ε ρ : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (h : Lemma68Inputs.CurveEscapesBothEnds η) : (cellVertices ε η (ball 0 ρ)).Finite :=
  TraceInputs68.cellVertices_finite_of_tendsto hε (tendsto_cocompact_of_escapes h) isBounded_ball

/-- Almost surely, `V(B_ρ)` is finite under the measurable-environment hypotheses (write-up §1.2). -/
theorem ae_cellVertices_ball_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ → ℂ}
    (hesc : ∀ᵐ ω ∂P, Lemma68Inputs.CurveEscapesBothEnds (η ω)) {ε ρ : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, (cellVertices ε (η ω) (ball 0 ρ)).Finite :=
  hesc.mono fun _ h => cellVertices_ball_finite_of_escapes hε h

end Lemma68Geometry

end MatedCRT
