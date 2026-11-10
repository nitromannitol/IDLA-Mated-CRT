import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.S5c.CellFirstHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellAnnulusEvent

/-!
# The good event `E_ε` of the approved Lemma 3.6 route, and the start clause (q4, task fp-S3i-hLens-good-event)

Source: `docs/campaign/LEMMA36-REPLACEMENT.md`, inputs (b) cell size and (c) GMS annulus, l.122-181; exponents l.182-258.
`E_ε` is the intersection of the cell-size event `LensCellSizeGood` (BG20 Lemma 2.4, `CellSizeEstimateStmt`, frozen) with
the GMS annulus event `LensAnnulusGood` (GMS (3.35), `GMSAnnulusDisconnectionStmt`), and of the almost sure regularity
`LensCurveGood` of `η ω` (continuous, proper, surjective).

Proved here:
* `lensGood_prob_le_full`: `S.P (LensGood ..)ᶜ ≤ ofReal (C * ε ^ κ)`. It mirrors the proof of
  `MatedCRTEnv.IsValid.cellSize_and_annulus_polyHighProb` (GMSCellAnnulusEvent.lean), with the annulus exponent `β`
  supplied in advance, so that it can be chosen before `ρ` as `QuenchedLensStep` requires.
* `vertexPoint_vertexOf_mem_ball`: deterministic start clause. On the cell-size event, the vertex point of
  `vertexOf ε η y` lies in `B_r(z)` when `dist y z + ε^a < r`.
* `interpolatedWalk_zero'`: the interpolated walk at time `0` is the vertex point of its start.

Not here: the excursion (exit) clause of the first quenched clause and the far-exit clause; these are the statement of
`MatedCRT/FirstPass/S3i/LensExcursion.lean` (z1), which has not landed.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT
namespace FirstPass36

variable {Ω : Type} [MeasurableSpace Ω]

/-- Item (b) of `E_ε`: every cell meeting `B_ρ` has diameter at most `ε^a` (the cell-size event). -/
def LensCellSizeGood (S : MatedCRTEnv Ω) (ρ a ε : ℝ) : Set Ω :=
  {ω | ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) i) ≤ ε ^ a}

/-- Item (c) of `E_ε`: the GMS annulus disconnection event at radii `≥ ε^β`, with constant `p`
(the event `F` of `cellSize_and_annulus_polyHighProb`). -/
def LensAnnulusGood (S : MatedCRTEnv Ω) (ρ p β ε : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ → ball z (2 * s) ⊆ ball 0 ρ →
    ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
        {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω) (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}}

/-- The almost sure regularity of `η ω` used by the walk: continuous, proper and surjective. -/
def LensCurveGood (S : MatedCRTEnv Ω) : Set Ω :=
  {ω | Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective (S.η ω)}

/-- The good event `E_ε` of the approved route (LEMMA36-REPLACEMENT.md l.122-130). -/
def LensGood (S : MatedCRTEnv Ω) (ρ a p β ε : ℝ) : Set Ω :=
  LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε ∩ LensCurveGood S

/-- The polynomial bound on the cell-size and annulus part of `E_ε`. The proof is that of
`MatedCRTEnv.IsValid.cellSize_and_annulus_polyHighProb`, with the annulus exponent `β` and the annulus bound `hA`
given as inputs. -/
theorem lensCellAnnulus_prob_le {𝒮 : SpaceFillingSLEModel} {γ ρ a p β α : ℝ} (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) (hcell : CellSizeEstimateStmt 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : a < 2 / (2 + γ) ^ 2) (hα : 0 < α)
    (hA : ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ε < 1 →
      S.P (LensAnnulusGood S ρ p β ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ α)) :
    ∃ κ C ε₀ : ℝ, 0 < κ ∧ 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P (LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ) := by
  obtain ⟨k, hk, C, ε₁, hε₁, hE⟩ := cellSize_polyHighProb_of_lt_critical 𝒮 hcell hγ hγ2 hρ hρ1 ha S hS
  obtain ⟨D, δ, hD, hδ, hG⟩ := hA
  refine ⟨min k α, max C 0 + D, min ε₁ (min δ 1), lt_min hk hα, add_nonneg (le_max_right _ _) hD,
    lt_min hε₁ (lt_min hδ one_pos), ?_⟩
  intro ε hε hsmall
  have hε₁' : ε < ε₁ := hsmall.trans_le (min_le_left _ _)
  have hδ' : ε < δ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he : S.P (LensCellSizeGood S ρ a ε)ᶜ ≤ ENNReal.ofReal (max C 0 * ε ^ k) := by
    apply (hE ε hε hε₁').trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _)
  have hf : S.P (LensAnnulusGood S ρ p β ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ α) := hG ε hε hδ' hε1
  exact measure_compl_inter_le_polynomial S.P _ _ hε hε1.le (le_max_right _ _) hD he hf

/-- The curve regularity holds almost surely: `η ω` is continuous and surjective (`isAreaParametrized`), and proper
(`ae_tendsto_cocompact`). Same pattern as `HolderGoodEventCorrected.lean:63-68`. -/
theorem lensCurveGood_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ω ∈ LensCurveGood S := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hη hp
  exact ⟨hη.1, hp, hη.2.2.1⟩

/-- **The good event `E_ε` has polynomially small complement** (`S.P (E ε)ᶜ ≤ ofReal (C ε^κ)`): the cell-size and
annulus bound of `lensCellAnnulus_prob_le`, plus the null set of the curve regularity. -/
theorem lensGood_prob_le {𝒮 : SpaceFillingSLEModel} {γ ρ a p β α : ℝ} (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) (hcell : CellSizeEstimateStmt 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : a < 2 / (2 + γ) ^ 2) (hα : 0 < α)
    (hA : ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ε < 1 →
      S.P (LensAnnulusGood S ρ p β ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ α)) :
    ∃ κ C ε₀ : ℝ, 0 < κ ∧ 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P (LensGood S ρ a p β ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ) := by
  obtain ⟨κ, C, ε₀, hκ, hC, hε₀, h⟩ :=
    lensCellAnnulus_prob_le S hS hcell hγ hγ2 hρ hρ1 ha hα hA
  refine ⟨κ, C, ε₀, hκ, hC, hε₀, fun ε hε hεε₀ => ?_⟩
  have hnull : S.P {ω | ¬ ω ∈ LensCurveGood S} = 0 := ae_iff.1 (lensCurveGood_ae S hS)
  have hsub : (LensGood S ρ a p β ε)ᶜ ⊆
      (LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε)ᶜ ∪ {ω | ¬ ω ∈ LensCurveGood S} := by
    intro ω hω
    by_cases h1 : ω ∈ LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε
    · right
      exact fun hc => hω ⟨h1, hc⟩
    · left
      exact h1
  calc S.P (LensGood S ρ a p β ε)ᶜ
      ≤ S.P ((LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε)ᶜ ∪ {ω | ¬ ω ∈ LensCurveGood S}) :=
        measure_mono hsub
    _ ≤ S.P (LensCellSizeGood S ρ a ε ∩ LensAnnulusGood S ρ p β ε)ᶜ + S.P {ω | ¬ ω ∈ LensCurveGood S} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ε ^ κ) := by
        rw [hnull, add_zero]
        exact h ε hε hεε₀

/-- **Start clause (Step 1, start part), deterministic.** Let `η` be continuous, surjective and proper, and let the cells
meeting `B_ρ` have diameter at most `ε^a`. If `y ∈ B_r(z) ⊆ B_ρ` and `dist y z + ε^a < r`, then the vertex point of the
cell of `y` lies in `B_r(z)`. -/
theorem vertexPoint_vertexOf_mem_ball {η : ℝ → ℂ} {ε ρ a r : ℝ} {y z : ℂ}
    (hη : Continuous η) (hsurj : Function.Surjective η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hmesh : ∀ i : ℤ, (cell ε η i ∩ ball 0 ρ).Nonempty → diam (cell ε η i) ≤ ε ^ a)
    (hmarg : dist y z + ε ^ a < r) :
    vertexPoint ε η (vertexOf ε η y) ∈ ball z r := by
  have hycell : y ∈ cell ε η (vertexOf ε η y) :=
    MatedCRT.S5c.mem_cell_vertexOf_of_first_hit hε hsurj (TruncatedLaws.cellGeom_bddBelow_preimage hp) y
  have hvcell : vertexPoint ε η (vertexOf ε η y) ∈ cell ε η (vertexOf ε η y) :=
    TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε.le _
  have hdiam : diam (cell ε η (vertexOf ε η y)) ≤ ε ^ a :=
    hmesh _ ⟨y, hycell, hball hy⟩
  have hbd : Bornology.IsBounded (cell ε η (vertexOf ε η y)) := by
    unfold cell
    exact (isCompact_Icc.image hη).isBounded
  have hd : dist (vertexPoint ε η (vertexOf ε η y)) y ≤ ε ^ a :=
    (dist_le_diam_of_mem hbd hvcell hycell).trans hdiam
  rw [mem_ball]
  calc dist (vertexPoint ε η (vertexOf ε η y)) z
      ≤ dist (vertexPoint ε η (vertexOf ε η y)) y + dist y z := dist_triangle _ _ _
    _ ≤ ε ^ a + dist y z := by linarith
    _ < r := by linarith

/-- The interpolated walk at time `0` is the vertex point of its start. -/
theorem interpolatedWalk_zero' {ε : ℝ} {η : ℝ → ℂ} {m : ℝ} (x : ℕ → ℤ) :
    interpolatedWalk ε η m x 0 = vertexPoint ε η (x 0) := by
  simp [interpolatedWalk]

#print axioms MatedCRT.FirstPass36.lensGood_prob_le
#print axioms MatedCRT.FirstPass36.vertexPoint_vertexOf_mem_ball

end FirstPass36
end MatedCRT
