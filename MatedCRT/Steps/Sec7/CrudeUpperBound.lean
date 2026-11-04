import MatedCRT.Steps.Sec7.OdometerBoundMass
import MatedCRT.Draft.Section4
import MatedCRT.External.SLE
import MatedCRT.Proofs.Sec7.CrudeUpperBound.GreedyPath
import MatedCRT.Proofs.Sec7.CrudeUpperBound.PolyHighProb

/-!
# Lemma 7.4 (lemma:crude-upper-bound, line 3058; proof lines 3068-3086; Levine-Peres 2009, Lemma 4.2): steps

`CrudeUpperBoundStmt` (MatedCRT/Draft/Section7.lean, after review-S (S4)) asks for the increasing paths from the
points `a ∈ Λ^ε_t \ {0}` of the discrete cluster, inside `Λ^ε_t`: the correction of the printed statement (paths in
`D_ε(t ε⁻¹)` for the stopped odometer, false, ESCALATIONS E-c3-1), and the form used at line 3240 (paths from the
support of `u^ε_t`, which is `Λ^ε_t`: `Sec7.mem_matedDiscreteCluster_of_stoppedOdometer_pos`).

The proof is the printed one (lines 3073-3085): from `a ∈ Λ^ε_t \ {0}` the neighbour `b` maximizing `u^ε_t` has
`u^ε_t(b) ≥ u^ε_t(a) + deg(a)⁻¹ ≥ u^ε_t(a) + log(ε⁻¹)⁻²`, so `b ∈ Λ^ε_t`; the strictly increasing chain cannot cycle in
the finite set `Λ^ε_t`, hence reaches `0` (MatedCRT/Proofs/Sec7/CrudeUpperBound/GreedyPath.lean).

## Steps
* `DegreeBoundInput` (literature: GMS19 Lemma 2.6, eq:degree-bound, line 3071; MatedCRT/External/SLE.lean);
* `MatedMapStructureStep`, `StoppedOdometerLaplacianStep` (MatedCRT/Steps/Sec7/OdometerBoundMass.lean), both
  discharged there from Lemma 4.4 and `AdjacentCellsMeetAeStep`.
The finiteness of `Λ^ε_t` (line 3085, Lemma 4.5 in the paper) follows from `Λ^ε_t ⊆ V^ε(B_ρ)` and the map structure,
so `crudeUpperBound_of_draft` rests on Lemma 4.4, `DegreeBoundInput` and `AdjacentCellsMeetAeStep` only.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- **Lemma 7.4** from the map structure, eq:laplacian-of-uteps and the degree bound. The finiteness of `Λ^ε_t`
(line 3085, from Lemma 4.5 in the paper) follows from `Λ^ε_t ⊆ V^ε(B_ρ)` and the map structure. -/
theorem crudeUpperBound_of_mapSteps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (hlap : StoppedOdometerLaplacianStep 𝒮) (hdeg : DegreeBoundInput 𝒮) : CrudeUpperBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht
  refine polyHighProb_mono_ae (hdeg γ hγ hγ2 ρ hρ hρ1 Ω S hS)
    ((hstr γ hγ hγ2 Ω S hS).and (hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS)) ?_
  rintro ε hε ω hωdeg ⟨hωstr, hωlap⟩
  have hωdeg' : ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2 := hωdeg
  obtain ⟨hlf, hfin⟩ := hωstr ε hε
  have hsucc : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := fun k =>
    Sec7.bmEdgeCount_succ_ne_zero hε (S.bm ω).continuous.fst _ k
  have hΛfin : (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite :=
    (hfin ρ).subset fun a ha => Sec7.cellVertices_mono ball_subset_closedBall
      (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from ha).1
  have hD : ∀ c, (0 : ℝ) < (mdeg (S.mult ε ω) c : ℕ) := fun c => by
    exact_mod_cast Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (hsucc c))
  have hstep : ∀ c ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t, c ≠ 0 → ∃ b ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      S.mult ε ω c b ≠ 0 ∧
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := by
    intro c hc hc0
    have hcV : c ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
      (show c ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from hc).1
    have hL : mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) c =
        ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := hωlap ε t hε ht c hc hc0
    obtain ⟨b, hmb, hub⟩ := exists_nbr_add_inv_le hlf (hsucc c) hL
    have hδle : (Real.log ε⁻¹)⁻¹ ^ 2 ≤ ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (hD c) (hωdeg' c hcV)
    have hbpos : 0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := by
      have h0 := Sec7.stoppedOdometer_nonneg (m := S.mult ε ω) (η := S.η ω) (ρ := ρ) hε ht c
      have h1 := inv_pos.2 (hD c)
      linarith
    exact ⟨b, Sec7.mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht hbpos, hmb, by linarith⟩
  rw [mem_ofPred_eq]
  rintro a ⟨haΛ, ha0⟩
  have haV : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from haΛ).1
  have hδ : 0 < (Real.log ε⁻¹)⁻¹ ^ 2 := by
    rw [inv_pow]
    exact inv_pos.2 ((hD a).trans_le (hωdeg' a haV))
  exact exists_vPath_chain hΛfin hδ hstep a haΛ

/-- **Lemma 7.4** from its steps (Lemma 4.5 is not needed: see `crudeUpperBound_of_mapSteps`). -/
theorem crudeUpperBound_of_steps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (hlap : StoppedOdometerLaplacianStep 𝒮) (hdeg : DegreeBoundInput 𝒮) (_h45 : DiscreteConservationOfMassStmt 𝒮) :
    CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_mapSteps 𝒮 hstr hlap hdeg

/-- **Lemma 7.4** from Lemma 4.4 (its first conjunct), the degree bound (GMS19 Lemma 2.6) and
`AdjacentCellsMeetAeStep` only. -/
theorem crudeUpperBound_of_draft (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundStmt 𝒮)
    (hdeg : DegreeBoundInput 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) : CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_mapSteps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 hcell)
    (stoppedOdometerLaplacianStep_of_draft 𝒮 h44 hcell) hdeg

end MatedCRT
