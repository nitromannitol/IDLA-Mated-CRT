import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.S5c.CellFirstHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellAnnulusEvent
import MatedCRT.FirstPass.S3i.LensExcursion
import MatedCRT.Proofs.Infra.RandomWalk

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

Assembly: `quenchedLensStep_of_boundaryContinuity` derives `QuenchedLensStep` from the excursion statement
`QuenchedLensExcursionStmt` (z1, `LensExcursion.lean`; far-exit clause, a binder until proved) and the exit statement
`QuenchedLensExitStmt` (defined here; no-exit clause, a binder until proved), together with the GMS annulus input
`hgms` (a binder pending the operator). `firstPass_3_6_annealed_closed` is `firstPass_3_6_annealed` with `hLens` removed.
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

/-- **Exit clause of the first quenched clause (statement, q4).** For a disc `ball z r ⊆ ball 0 ρ` with `ρ < ρ₁ < 1` and
`0 < p ≤ 1/2`, there are `C, ε₀` such that for `0 < ε < ε₀`, every environment `ω` with `LensExcursionGood` at scale `ε`,
and with the start vertex `vertexOf ε (S.η ω) y` an interior cell vertex of `ball z r`, the quenched probability that the
interpolated walk never leaves `ball z r` (`pathExitTime = ⊤`) is at most `C ε^{νb/2}`, where `b = min a β` and
`ν = -log(1-p)/log 2`. Source: LEMMA36 l.259-339 (stage survival `(1-p)^{j+1}`; exit by the visit to `V(∂O)`).
Terminology: exit time of a disc `pathExitTime` (Armitage-Gardiner); quenched law `srwLaw` (Armstrong-Kuusi-Mourrat). -/
def QuenchedLensExitStmt : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ρ₁ a β p r : ℝ) (z y : ℂ),
    0 < ρ → ρ < ρ₁ → ρ₁ < 1 → 0 < r → ball z r ⊆ ball 0 ρ → 0 < a → 0 < β → 0 < p → p ≤ 1 / 2 →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ω : Ω,
      LensExcursionGood S ρ₁ a β p ε ω →
      vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          {x | HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) = ⊤} ≤
        ENNReal.ofReal (C * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2))

/-- A disc `B_{2s}(c)` inside `B_R(0)`, with `c ∈ B_R(0)`, forces `s ≤ R` (a disc inside a disc, Armitage-Gardiner).
Used to drop the radius condition `s ≤ ρ` of `LensAnnulusGood` when passing to `LensExcursionGood`. -/
theorem radius_le_of_ball_subset {c : ℂ} {s R : ℝ} (hc : c ∈ ball (0 : ℂ) R)
    (hsub : ball c (2 * s) ⊆ ball (0 : ℂ) R) : s ≤ R := by
  by_contra hlt
  have hlt' : R < s := not_le.1 hlt
  have hcn : ‖c‖ < R := by simpa [mem_ball] using hc
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg c) hcn
  rcases eq_or_ne c 0 with rfl | hc0
  · have hw : ((R : ℝ) : ℂ) ∈ ball (0 : ℂ) (2 * s) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hR.le]
      linarith
    have h' := hsub hw
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hR.le] at h'
    exact lt_irrefl _ h'
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have hnw : ‖((R / ‖c‖ : ℝ) : ℂ) * c‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hR.le hcpos.le)]
      field_simp
    have key : (R / ‖c‖ - 1) * ‖c‖ = R - ‖c‖ := by
      field_simp
    have habs : |R / ‖c‖ - 1| * ‖c‖ = R - ‖c‖ := by
      have h1 : |(R / ‖c‖ - 1) * ‖c‖| = |R / ‖c‖ - 1| * ‖c‖ := by
        rw [abs_mul, abs_of_pos hcpos]
      rw [← h1, key, abs_of_pos (sub_pos.2 hcn)]
    have hwc : ((R / ‖c‖ : ℝ) : ℂ) * c - c = (((R / ‖c‖ - 1 : ℝ)) : ℂ) * c := by
      push_cast
      ring
    have hdw : dist (((R / ‖c‖ : ℝ) : ℂ) * c) c < 2 * s := by
      rw [dist_eq_norm, hwc, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
      linarith [norm_nonneg c]
    have h' := hsub (Metric.mem_ball.2 hdw)
    rw [mem_ball, dist_zero_right, hnw] at h'
    exact lt_irrefl _ h'

/-- Lowering the annulus constant `p` enlarges the GMS annulus event (`ofReal p' ≤ ofReal p ≤ srwLaw`). -/
theorem lensAnnulusGood_anti_p {S : MatedCRTEnv Ω} {ρ p p' β ε : ℝ} (hpp : p' ≤ p) :
    LensAnnulusGood S ρ p β ε ⊆ LensAnnulusGood S ρ p' β ε := by
  intro ω hω z hz s hs1 hs2 hsub j hj
  exact (ENNReal.ofReal_le_ofReal hpp).trans (hω z hz s hs1 hs2 hsub j hj)

/-- **QuenchedLensStep from the boundary input (q4, item 3).** The good event is `LensGood S ρ₁ a p β` with
`ρ₁ = (1+ρ)/2`; `a = 1/(2+γ)^2`-type cell exponent, `β` and the annulus base from `hgms` at `γ`, and `p ≤ 1/2` the GMS
constant at `ρ₁` (replaced by `min p₀ (1/2)`, which only weakens the annulus event). On the good event the start is
interior (`vertexOf_mem_interiorCellVertices_of_mesh`) and lies in `B_r(z)` (`vertexPoint_vertexOf_mem_ball`); the walk
starts at its vertex (`srwLaw_ae_start`); the no-exit bound is `hExit` and the far-exit bound is `hExc`. `hBE` is not used
in this proof: `firstPass_3_6_annealed` consumes it through the implication `hLens`, whose shape this matches. -/
theorem quenchedLensStep_of_boundaryContinuity {𝒮 : SpaceFillingSLEModel}
    (_hBE : FrozenOneSidedBoundaryContinuity 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hgms : GMSAnnulusDisconnectionStmt 𝒮) (hExc : QuenchedLensExcursionStmt)
    (hExit : QuenchedLensExitStmt) : QuenchedLensStep 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨α, β, hα, hβ, hρg⟩ := hgms.with_subunit_probability γ hγ0 hγ2
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℝ, 0 < a ∧ a < 2 / (2 + γ) ^ 2 :=
    ⟨1 / (2 + γ) ^ 2, by positivity, by gcongr; norm_num⟩
  refine ⟨min a β, lt_min ha0 hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hρρ₁ : ρ < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁def]; linarith
  have hρ₁0 : 0 < ρ₁ := by linarith
  obtain ⟨p₀, hp₀, -, henv⟩ := hρg ρ₁ hρ₁0 hρ₁1
  obtain ⟨p, hp0, hp12, hpp₀⟩ : ∃ p : ℝ, 0 < p ∧ p ≤ 1 / 2 ∧ p ≤ p₀ :=
    ⟨min p₀ (1 / 2), lt_min hp₀ (by norm_num), min_le_right _ _, min_le_left _ _⟩
  intro Ω _ S hS r z hr hball ψ H χ y hadm
  obtain ⟨-, -, -, hy⟩ := hadm
  obtain ⟨Dα, δα, hDα, hδα, hAp₀⟩ : ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ε < 1 →
      S.P (LensAnnulusGood S ρ₁ p₀ β ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ α) := by
    obtain ⟨C, ε₀, hC, hε₀, h⟩ := henv Ω S hS
    exact ⟨C, ε₀, hC, hε₀, h⟩
  have hAp : ∀ ε : ℝ, 0 < ε → ε < δα → ε < 1 →
      S.P (LensAnnulusGood S ρ₁ p β ε)ᶜ ≤ ENNReal.ofReal (Dα * ε ^ α) :=
    fun ε hε hδ hε1 => (measure_mono (Set.compl_subset_compl.2
      (lensAnnulusGood_anti_p hpp₀))).trans (hAp₀ ε hε hδ hε1)
  obtain ⟨κ, Cg, εg, hκ, hCg, hεg, hG⟩ :=
    lensGood_prob_le S hS hcell hγ0 hγ2 hρ₁0 hρ₁1 ha hα ⟨Dα, δα, hDα, hδα, hAp⟩
  have hν : 0 < -Real.log (1 - p) / Real.log 2 := by
    refine div_pos ?_ (Real.log_pos one_lt_two)
    linarith [Real.log_neg (by linarith : (0 : ℝ) < 1 - p) (by linarith : 1 - p < 1)]
  have hm0 : 0 < r - dist y z := by
    rw [mem_ball] at hy
    linarith
  have hmpow : ((r - dist y z) ^ a⁻¹) ^ a = r - dist y z := by
    rw [← Real.rpow_mul hm0.le, inv_mul_cancel₀ ha0.ne', Real.rpow_one]
  obtain ⟨Ce, εe, hCe, hεe, hE⟩ :=
    hExc Ω S ρ ρ₁ a β p r z y hρ0 hρρ₁ hρ₁1 hr hball ha0 hβ hp0 hp12
  obtain ⟨Cx, εx, hCx, hεx, hX⟩ :=
    hExit Ω S ρ ρ₁ a β p r z y hρ0 hρρ₁ hρ₁1 hr hball ha0 hβ hp0 hp12
  have hball₁ : ball z r ⊆ ball 0 ρ₁ := hball.trans (Metric.ball_subset_ball hρρ₁.le)
  refine ⟨κ, -Real.log (1 - p) / Real.log 2, Ce + Cx,
    min εg (min εe (min εx ((r - dist y z) ^ a⁻¹))), hκ, hν, add_nonneg hCe hCx,
    lt_min hεg (lt_min hεe (lt_min hεx (Real.rpow_pos_of_pos hm0 _))),
    LensGood S ρ₁ a p β, Cg, hCg, ?_⟩
  intro ε hε hεε₀
  have hεg' : ε < εg := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have hεe' : ε < εe :=
    lt_of_lt_of_le hεε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεx' : ε < εx :=
    lt_of_lt_of_le hεε₀ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεM : ε < (r - dist y z) ^ a⁻¹ :=
    lt_of_lt_of_le hεε₀ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεa : ε ^ a < r - dist y z :=
    calc ε ^ a < ((r - dist y z) ^ a⁻¹) ^ a := Real.rpow_lt_rpow hε.le hεM ha0
      _ = r - dist y z := hmpow
  refine ⟨hG ε hε hεg', ?_⟩
  intro ω hω
  have hη : Continuous (S.η ω) := hω.2.1
  have hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) := hω.2.2.1
  have hsurj : Function.Surjective (S.η ω) := hω.2.2.2
  have hmesh : ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) i) ≤ ε ^ a :=
    hω.1.1
  have hexc : LensExcursionGood S ρ₁ a β p ε ω := by
    unfold LensExcursionGood
    exact ⟨hmesh, fun c s hc hs hsub => hω.1.2 c hc s hs (radius_le_of_ball_subset hc hsub) hsub⟩
  have hmarg : dist y z + ε ^ a < r := by linarith
  have hmesh' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ a := by
    rw [← hρ₁def]
    exact hmesh
  have hint : vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) :=
    TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh hη hsurj hp hε hball hρ1 hy hmesh' hmarg
  have hstart : vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y) ∈ ball z r :=
    vertexPoint_vertexOf_mem_ball hη hsurj hp hε hball₁ hy hmesh hmarg
  have hsub : {x | ¬ SameWalkGood S r z ε ω x} ⊆
      {x | x 0 ≠ vertexOf ε (S.η ω) y} ∪
        {x | HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) = ⊤} := by
    intro x hx
    have hx' : ¬ SameWalkGood S r z ε ω x := hx
    by_cases h0 : x 0 = vertexOf ε (S.η ω) y
    · right
      by_contra hne
      apply hx'
      unfold SameWalkGood
      exact ⟨by rw [interpolatedWalk_zero', h0]; exact hstart, lt_top_iff_ne_top.2 hne⟩
    · exact Or.inl h0
  have hzero : srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | x 0 ≠ vertexOf ε (S.η ω) y} = 0 :=
    ae_iff.1 (srwLaw_ae_start _ _)
  have hfirst : srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x}
      ≤ ENNReal.ofReal ((Ce + Cx) * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2)) := by
    calc srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x}
        ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
            ({x | x 0 ≠ vertexOf ε (S.η ω) y} ∪
              {x | HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) = ⊤}) :=
          measure_mono hsub
      _ ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | x 0 ≠ vertexOf ε (S.η ω) y} +
          srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
            {x | HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) = ⊤} :=
          measure_union_le _ _
      _ = srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
            {x | HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) = ⊤} := by
          rw [hzero, zero_add]
      _ ≤ ENNReal.ofReal (Cx * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2)) :=
          hX ε hε hεx' ω hexc (TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh hη hsurj hp hε hball hρ1 hy hmesh' hmarg)
      _ ≤ ENNReal.ofReal ((Ce + Cx) * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2)) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hε.le _))
  have hfar : srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
      {x | SameWalkGood S r z ε ω x ∧
        ε ^ (min a β / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal ((Ce + Cx) * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2)) :=
    (hE ε hε hεe' ω hexc (TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh hη hsurj hp hε hball hρ1 hy hmesh' hmarg)).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hε.le _)))
  exact ⟨hfirst, hfar⟩

/-- **Lemma 3.6, annealed clause, without the named Steps 1-6 (q4).** `firstPass_3_6_annealed` with `hLens` replaced by
`quenchedLensStep_of_boundaryContinuity`. Remaining inputs: `hgms` (GMS annulus disconnection; operator decision pending,
not in External and not frozen), `hExc` (`QuenchedLensExcursionStmt`, z1) and `hExit` (`QuenchedLensExitStmt`, this file). -/
theorem firstPass_3_6_annealed_closed {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮)
    (hgms : GMSAnnulusDisconnectionStmt 𝒮) (hExc : QuenchedLensExcursionStmt)
    (hExit : QuenchedLensExitStmt) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed h211 h28 hm hexc h32 hBE
    (fun hBE' => quenchedLensStep_of_boundaryContinuity hBE' h28 hgms hExc hExit)

#print axioms MatedCRT.FirstPass36.lensGood_prob_le
#print axioms MatedCRT.FirstPass36.vertexPoint_vertexOf_mem_ball
#print axioms MatedCRT.FirstPass36.quenchedLensStep_of_boundaryContinuity
#print axioms MatedCRT.FirstPass36.firstPass_3_6_annealed_closed

end FirstPass36
end MatedCRT
