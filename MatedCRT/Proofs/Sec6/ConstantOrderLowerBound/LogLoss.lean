import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Statement
import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv

/-!
# Lemma 6.7, route (b) of E-A10 (lemma:constant-order-lower-bound, line 2410)

The proof of Lemma 6.7 from Lemma 6.8 (lines 2449-2461) is deterministic given the map
(`ConstantOrder.constantOrderLowerBound_core`) and uses the bound `1 - s₂` of Lemma 6.8 at one radius `r` only. With
Lemma 6.8 in its route (b) form (`ConstantOrderLowerBoundDivLogStmt`, bound `1 - s₂ / (1 + |log r|)²`), the same proof
gives Lemma 6.7 with the absorption probability `s₂ / (1 + |log r|)²` (`ConstantOrderLowerBoundLogStmt`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

open ConstantOrder in
/-- **Lemma 6.7, route (b), from Lemma 6.8, route (b)** (proof of lines 2449-2461), with the same `ω₀`, `s₁`, `s₂`
and with `𝛅 ∧ ρ/4` in place of the `𝛅` of Lemma 6.8. -/
theorem constantOrderLowerBoundLog_of_steps (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hW : SrwHitDecompositionStep) (hN : SrwAeAdjacentStep) (hF : CellVerticesBallFiniteStep 𝒮)
    (hE : WalkExitsStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβ
  obtain ⟨ω₀, hω₀, h⟩ := h68 γ hγ hγ2 ρ hρ hρ1 βm hβ
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h'⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hP⟩ := h' Ω S hS
  refine ⟨fun ω => min (dd ω) (ρ / 4), hdd.min measurable_const, fun ω => lt_min (hddpos ω) (by positivity), ?_⟩
  have hcont : ∀ᵐ ω ∂S.P, ω ∈ {ω | Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty} :=
    (hS.isAreaParametrized.and (hcell γ hγ hγ2 Ω S hS)).mono fun ω hω => ⟨hω.1.1, hω.2⟩
  have hall := ((hP.inter (hF γ hγ hγ2 ρ hρ hρ1 Ω S hS)).inter
    (hE γ hγ hγ2 ρ s₀ hρ hρ1 hs₀ Ω S hS)).inter (probTendsToOne_of_ae hcont)
  refine hall.mono_pos fun ε hε ω hω => ?_
  obtain ⟨⟨⟨h68ω, hfinω⟩, hexitω⟩, hcontω⟩ := hω
  simp only [mem_ofPred_eq] at h68ω hfinω hexitω hcontω ⊢
  intro r hr1 hr2 Θ hΘ1 hΘ2 a ha S' hS' hcard
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hrρ : r ≤ ρ / 4 := hr2.trans (min_le_right _ _)
  have hL : 1 ≤ (1 + |Real.log r|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hs₂r : 0 ≤ s₂ / (1 + |Real.log r|) ^ 2 := div_nonneg hs₂.le (by positivity)
  have hs₂r1 : s₂ / (1 + |Real.log r|) ^ 2 ≤ 1 := (div_le_self hs₂.le hL).trans hs₂1.le
  have hthick : ∀ δ, δ ≤ ρ / 2 → thickening δ (fillCells ε (S.η ω) Θ) ⊆ ball 0 ρ :=
    fun δ hδ => thickening_subset_ball hΘ1 hδ
  exact constantOrderLowerBound_core hW hN hε.le hcontω.1 (hcontω.2 ε hε)
    (U := cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)))
    (O := thickening (r / 2) (fillCells ε (S.η ω) Θ)) isOpen_thickening
    (self_subset_thickening (by linarith) _)
    (cellVertices_mono ((closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' hr (by linarith) _)))
    (hfinω.subset (cellVertices_mono (hthick r (by linarith))))
    (fun b => hexitω _ isOpen_thickening (hΘ2.trans (self_subset_thickening (by linarith) _))
      (hthick _ (by linarith)) b)
    (h68ω r hr1 (hr2.trans (min_le_left _ _)) Θ hΘ1 hΘ2) hs₂r hs₂r1 ha hS' hcard

/-- **Lemma 6.7, route (b)** from Lemma 6.8, route (b), and Lemmas 2.7, 2.8, 2.19, and `AdjacentCellsMeetAeStep`
(adjacent vertices of the map of Definition 1.1 have intersecting cells, MatedCRT/Steps/Infra/MatingOfTrees.lean). -/
theorem constantOrderLowerBoundLog (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 :=
  constantOrderLowerBoundLog_of_steps 𝒮 h68 srwHitDecompositionStep srwAeAdjacentStep
    (cellVerticesBallFiniteStep 𝒮 h27 h28) (walkExitsStep 𝒮 h27 h219) hcell

end MatedCRT
