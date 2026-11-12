import MatedCRT.FirstPass.Derived.GreenRandomPathAE
import MatedCRT.FirstPass.Derived.GreenCellCrudeEventually
import MatedCRT.FirstPass.Derived.GreenCrudeOfSegmentBalls

/-!
# The crude Green function bound with segment paths for almost every direction

Versions of the reductions of `GreenFunctionCrudeBoundStmt` (BG20 Lemma 2.15 / Lemma 5.6) in
which the segment paths from `u` are required to be nodup chains of `𝒢^ε` through `V^ε(B_ρ)`
ending outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` only for almost every direction `θ` (for the uniform law on
the circle), as allowed by the random-path form of Thomson's principle
(`MatedCRT.greenFn_interiorCellVertices_le_of_segmentPaths_ae`). The every-direction events are
contained in the almost-every-direction ones, so these results contain the earlier ones.

* `MatedCRT.MatedCRTEnv.IsValid.ae_greenFn_interiorCellVertices_le_of_segmentPaths_ae`
* `MatedCRT.MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds_ae`
* `MatedCRT.MatedCRTEnv.segmentPathEventAE`, `MatedCRT.MatedCRTEnv.segmentReachEventAE`
* `MatedCRT.greenFunctionCrudeBoundStmt_of_inball_of_segmentPathsAE`
* `MatedCRT.greenFunctionCrudeBoundStmt_of_segmentBalls_of_reachableAE`
-/

open Set Metric MeasureTheory Filter Topology

namespace MatedCRT

section Pathwise

open LatticeProb

/-- **Crude Green function bound for the cells meeting `B_ρ`, almost surely, with segment paths
for almost every direction.** For a valid environment, almost surely, for every `ε > 0` and every
`x ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`, the Green function of the walk on `𝒢^ε` killed on exiting
`V^ε(B_ρ) \ V^ε(∂B_ρ)` satisfies the bound of `greenFn_interiorCellVertices_le_of_segmentPaths_ae`,
given the bounds on the cells meeting `B_ρ` (inscribed discs, diameters in `[r, M]`, degrees at
most `Δ`) and segment paths with the required properties for almost every direction. -/
theorem MatedCRTEnv.IsValid.ae_greenFn_interiorCellVertices_le_of_segmentPaths_ae
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ (ρ : ℝ) (x : ℤ),
      x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ) →
      ∀ (c : ℤ → ℂ) (u : ℂ) (ℓ κ r M Δ : ℝ), 0 < κ → 0 < r → r ≤ M → 0 ≤ Δ →
      (∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        ball (c a) (κ * diam (cell ε (S.η ω) a)) ⊆ cell ε (S.η ω) a) →
      (∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), r ≤ diam (cell ε (S.η ω) a)) →
      (∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), diam (cell ε (S.η ω) a) ≤ M) →
      (∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), (mdeg (S.mult ε ω) a : ℝ) ≤ Δ) →
      ∀ (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) →
      (∀ᵐ θ ∂uniformDirection, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).Nodup) →
      (∀ᵐ θ ∂uniformDirection, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).IsChain
        fun a b => S.mult ε ω a b ≠ 0) →
      (∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath u ℓ (cell ε (S.η ω)) Y F θ = x :: p ∧
        (∀ v ∈ x :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧
        (x :: p).getLast (List.cons_ne_nil x p) ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ)) →
      ∀ a : ℤ, greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a x ≤
        (mdeg (S.mult ε ω) x : ℝ) * ((1 / 2) * (Δ *
          ((Real.logb 2 (M / r) + 1) * (16 / κ ^ 2) +
            8 * Real.log ((ρ + M + ‖u‖) / r) / κ ^ 2))) := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    hS.isAreaParametrized, TraceInputs68.ae_adjacent hγ hγ2 S hS] with ω hc hp hap hadj
  intro ε hε ρ x hx c u ℓ κ r M Δ hκ hr hrM hΔ hball hlo hhi hdeg Y F hF hnd hchain hpath a
  have hfin : (cellVertices ε (S.η ω) (ball 0 ρ)).Finite :=
    (cellVertices_finite_of_isCompact hc hp hε (isCompact_closedBall 0 ρ)).subset
      fun k ⟨z, hzk, hz⟩ => ⟨z, hzk, ball_subset_closedBall hz⟩
  exact greenFn_interiorCellVertices_le_of_segmentPaths_ae hc hap hε
    (isLocallyFiniteMult_of_cells_meet hc hp hε (hadj ε hε)) (S.mult_succ_ne_zero hε.le ω)
    (S.mult_symm ε ω) (fun j k h => by rw [inter_comm]; exact hadj ε hε k j h) hfin hx hκ hr
    hrM hΔ hball hlo hhi hdeg hF hnd hchain hpath a


/-- **Crude Green function bound on the good event, with segment paths for almost every
direction (BG20 Lemma 5.6, pathwise part).** As
`MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds`, with the segment paths required
to be nodup chains staying in `V^ε(B_ρ)` and ending outside `A` only for almost every
direction. -/
theorem MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds_ae
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {p q δ ζ ρ U : ℝ}
    (hq : 0 ≤ q) (hρ : 0 ≤ ρ) (hU : 0 ≤ U) (hζ : 5 * δ / 2 < ζ) :
    ∃ ε₀ > 0, ∀ᵐ ω ∂S.P, ∀ ε ∈ Ioo 0 ε₀,
      (∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        ε ^ p ≤ diam (cell ε (S.η ω) k) ∧ diam (cell ε (S.η ω) k) ≤ ε ^ q) →
      (∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∃ c : ℂ,
        ball c (ε ^ (δ / 4) * diam (cell ε (S.η ω) k)) ⊆ cell ε (S.η ω) k) →
      (∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), (mdeg (S.mult ε ω) k : ℝ) ≤ ε ^ (-δ)) →
      (∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ)
        (F : Finset ℤ → List ℤ), ‖u‖ ≤ U ∧ (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).IsChain
          fun a b => S.mult ε ω a b ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ l, segmentPath u ℓ (cell ε (S.η ω)) Y F θ = x :: l ∧
          (∀ v ∈ x :: l, v ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧
          (x :: l).getLast (List.cons_ne_nil x l) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ρ))) →
      ∀ a b : ℤ,
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-ζ) := by
  have hR : 0 < ρ + 1 + U := by linarith
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ((eventually_fatCell_energy_rpow_le (p := p) (q := q) hR hζ).and (Ioo_mem_nhdsGT one_pos))
  refine ⟨ε₀, hε₀, ?_⟩
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    TraceInputs68.ae_adjacent hγ hγ2 S hS,
    hS.ae_greenFn_interiorCellVertices_le_of_segmentPaths_ae hγ hγ2] with ω hc hp hadj hG
  intro ε hε hE1 hE2 hE3 hP
  obtain ⟨hbound, hε0, hε1⟩ := hsub hε
  have hfin : (cellVertices ε (S.η ω) (ball 0 ρ)).Finite :=
    (cellVertices_finite_of_isCompact hc hp hε0 (isCompact_closedBall 0 ρ)).subset
      fun k ⟨z, hzk, hz⟩ => ⟨z, hzk, ball_subset_closedBall hz⟩
  refine greenFn_le_of_diag_le (isLocallyFiniteMult_of_cells_meet hc hp hε0 (hadj ε hε0))
    (S.mult_succ_ne_zero hε0.le ω) (hfin.subset sdiff_subset)
    (Real.rpow_nonneg hε0.le _) (fun x hx => ?_)
  choose! c hcb using hE2
  obtain ⟨u, ℓ, Y, F, hu, hF, hnd, hchain, hpath⟩ := hP x hx
  have hxV : x ∈ cellVertices ε (S.η ω) (ball 0 ρ) := hx.1
  have hκ : 0 < ε ^ (δ / 4) := Real.rpow_pos_of_pos hε0 _
  have hr : 0 < ε ^ p := Real.rpow_pos_of_pos hε0 _
  have hrM : ε ^ p ≤ ε ^ q := (hE1 x hxV).1.trans (hE1 x hxV).2
  have hM1 : ε ^ q ≤ 1 := Real.rpow_le_one hε0.le hε1.le hq
  have hΔ : 0 ≤ ε ^ (-δ) := Real.rpow_nonneg hε0.le _
  have hG' := hG ε hε0 ρ x hx c u ℓ (ε ^ (δ / 4)) (ε ^ p) (ε ^ q) (ε ^ (-δ)) hκ hr hrM hΔ hcb
    (fun k hk => (hE1 k hk).1) (fun k hk => (hE1 k hk).2) hE3 Y F hF hnd hchain hpath x
  refine hG'.trans (le_trans ?_ hbound)
  have hL1 : 0 ≤ Real.logb 2 (ε ^ q / ε ^ p) :=
    Real.logb_nonneg one_lt_two ((one_le_div hr).2 hrM)
  have hL2 : 0 ≤ Real.log ((ρ + 1 + U) / ε ^ p) :=
    Real.log_nonneg ((one_le_div hr).2 (by linarith))
  have hlog : Real.log ((ρ + ε ^ q + ‖u‖) / ε ^ p) ≤ Real.log ((ρ + 1 + U) / ε ^ p) := by
    have hpos : 0 < ρ + ε ^ q + ‖u‖ := by
      have := Real.rpow_pos_of_pos hε0 q
      linarith [norm_nonneg u]
    exact Real.log_le_log (div_pos hpos hr) (div_le_div_of_nonneg_right (by linarith) hr.le)
  have hT : 0 ≤ (1 / 2 : ℝ) * (ε ^ (-δ) * ((Real.logb 2 (ε ^ q / ε ^ p) + 1) *
      (16 / (ε ^ (δ / 4)) ^ 2) + 8 * Real.log ((ρ + 1 + U) / ε ^ p) / (ε ^ (δ / 4)) ^ 2)) := by
    have h16 : 0 ≤ 16 / (ε ^ (δ / 4)) ^ 2 := by positivity
    have h8 : 0 ≤ 8 * Real.log ((ρ + 1 + U) / ε ^ p) / (ε ^ (δ / 4)) ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hL2) (by positivity)
    exact mul_nonneg (by norm_num) (mul_nonneg hΔ (add_nonneg (mul_nonneg (by linarith) h16) h8))
  calc (mdeg (S.mult ε ω) x : ℝ) * ((1 / 2) * (ε ^ (-δ) *
        ((Real.logb 2 (ε ^ q / ε ^ p) + 1) * (16 / (ε ^ (δ / 4)) ^ 2) +
          8 * Real.log ((ρ + ε ^ q + ‖u‖) / ε ^ p) / (ε ^ (δ / 4)) ^ 2)))
      ≤ (mdeg (S.mult ε ω) x : ℝ) * ((1 / 2) * (ε ^ (-δ) *
        ((Real.logb 2 (ε ^ q / ε ^ p) + 1) * (16 / (ε ^ (δ / 4)) ^ 2) +
          8 * Real.log ((ρ + 1 + U) / ε ^ p) / (ε ^ (δ / 4)) ^ 2))) := by
        have h8 : 8 * Real.log ((ρ + ε ^ q + ‖u‖) / ε ^ p) / (ε ^ (δ / 4)) ^ 2 ≤
            8 * Real.log ((ρ + 1 + U) / ε ^ p) / (ε ^ (δ / 4)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add_right h8 _) hΔ) (by norm_num)) (Nat.cast_nonneg _)
    _ ≤ ε ^ (-δ) * ((1 / 2) * (ε ^ (-δ) *
        ((Real.logb 2 (ε ^ q / ε ^ p) + 1) * (16 / (ε ^ (δ / 4)) ^ 2) +
          8 * Real.log ((ρ + 1 + U) / ε ^ p) / (ε ^ (δ / 4)) ^ 2))) :=
        mul_le_mul_of_nonneg_right (hE3 x hxV) hT


end Pathwise

section PolyHigh

open Asymptotics HarmonicBalls

/-- The segment-path event for almost every direction: every vertex `x` of
`V^ε(B_ρ) \ V^ε(∂B_ρ)` has a family of segment paths (from a point `u` with `‖u‖ ≤ U`, indexed by
the angle) which, for almost every angle, are nodup chains of the mated-CRT map starting at `x`,
staying in `V^ε(B_ρ)` and ending outside `V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
def MatedCRTEnv.segmentPathEventAE {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ U ε : ℝ) : Set Ω :=
  {ω | ∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ)
    (F : Finset ℤ → List ℤ), ‖u‖ ≤ U ∧ (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
    (∀ᵐ θ ∂LatticeProb.uniformDirection,
      (LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
    (∀ᵐ θ ∂LatticeProb.uniformDirection,
      (LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ).IsChain
        fun a b => S.mult ε ω a b ≠ 0) ∧
    (∀ᵐ θ ∂LatticeProb.uniformDirection,
      ∃ l, LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ = x :: l ∧
        (∀ v ∈ x :: l, v ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧
        (x :: l).getLast (List.cons_ne_nil x l) ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ))}


theorem MatedCRTEnv.segmentPathEvent_subset_segmentPathEventAE {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ U ε : ℝ) : S.segmentPathEvent ρ U ε ⊆ S.segmentPathEventAE ρ U ε := by
  intro ω h x hx
  obtain ⟨u, ℓ, Y, F, hu, hF, hnd, hchain, hpath⟩ := h x hx
  exact ⟨u, ℓ, Y, F, hu, hF, ae_of_all _ hnd, ae_of_all _ hchain, ae_of_all _ hpath⟩

/-- **Crude Green function bound with polynomially high probability (BG20 Lemma 5.6), with
segment paths for almost every direction.** As
`MatedCRTEnv.IsValid.polyHighProb_greenFn_le_of_inball_of_segmentPaths`, with the segment-path
event replaced by the larger event `MatedCRTEnv.segmentPathEventAE`. -/
theorem MatedCRTEnv.IsValid.polyHighProb_greenFn_le_of_inball_of_segmentPathsAE
    {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {δ ζ ρ U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hδ : 0 < δ)
    (hζ : 5 * δ / 2 < ζ) (hU : 0 ≤ U) (hE2 : PolyHighProb S.P (S.cellInballEvent δ ρ))
    (hP : PolyHighProb S.P (S.segmentPathEventAE ρ U)) :
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-ζ)} := by
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hζ'0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hζ'1 : 1 / (2 + γ) ^ 2 < 1 := by rw [div_lt_one h2γ]; nlinarith
  have hq : 0 ≤ 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    have e : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
    rw [e]
    exact hζ'0.le
  obtain ⟨ε₀, hε₀, hae⟩ := hS.exists_ae_greenFn_le_rpow_of_cellBounds_ae hγ hγ2
    (p := 2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) hq hρ.le hU hζ
  obtain ⟨ε₁, hε₁, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (eventually_log_inv_sq_le_rpow_neg hδ)
  refine Sec7.polyHighProb_of_inter_ae
    ((hcell γ hγ hγ2 _ ρ hζ'0 hζ'1 hρ hρ1 Ω S hS).inter hE2)
    ((hdeg γ hγ hγ2 ρ hρ hρ1 Ω S hS).inter hP) hae (lt_min hε₀ hε₁) ?_
  rintro ε hε hεr ω ⟨h1, h2⟩ ⟨h3, h4⟩ hω a - b -
  have hlog : Real.log ε⁻¹ ^ 2 ≤ ε ^ (-δ) := hsub ⟨hε, hεr.trans_le (min_le_right _ _)⟩
  exact hω ε ⟨hε, hεr.trans_le (min_le_left _ _)⟩ (fun k hk => h1 k hk) h2
    (fun k hk => (h3 k hk).trans hlog) h4 a b

/-- **Lemma 2.15 from the cell events, with segment paths for almost every direction.** The cell
size estimate, the degree bound, the inradius event at every exponent and the
almost-every-direction segment-path event (at some radius `U`) with polynomially high probability
give `GreenFunctionCrudeBoundStmt`. -/
theorem greenFunctionCrudeBoundStmt_of_inball_of_segmentPathsAE {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hE2 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ δ ρ : ℝ, 0 < δ → 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        PolyHighProb S.P (S.cellInballEvent δ ρ))
    (hP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ U : ℝ, 0 ≤ U ∧ PolyHighProb S.P (S.segmentPathEventAE ρ U)) :
    GreenFunctionCrudeBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ ζ hρ hρ1 hζ _ Ω _ S hS
  obtain ⟨U, hU, hPU⟩ := hP γ hγ hγ2 ρ hρ hρ1 Ω S hS
  have hδ : 0 < ζ / 5 := by positivity
  exact hS.polyHighProb_greenFn_le_of_inball_of_segmentPathsAE hcell hdeg hγ hγ2 hρ hρ1 hδ
    (by linarith) hU (hE2 γ hγ hγ2 _ ρ hδ hρ hρ1 Ω S hS) hPU


/-- The segment reachability event for almost every direction: every vertex `x` of
`V^ε(B_ρ) \ V^ε(∂B_ρ)` has a point `u` with `‖u‖ ≤ U`, a length `ℓ` and a finite set `Y` of cells
such that, for almost every direction `θ`, the cell of `x` is met by the segment from `u` and a
vertex outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` is reachable from `x` in `𝒢^ε` through cells of
`V^ε(B_ρ)` met by the segment. -/
def MatedCRTEnv.segmentReachEventAE {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ U ε : ℝ) : Set Ω :=
  {ω | ∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ),
    ‖u‖ ≤ U ∧ ∀ᵐ θ ∂LatticeProb.uniformDirection,
      x ∈ LatticeProb.hitFinset Y
        (fun y => LatticeProb.segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
      ∃ b ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ), Relation.ReflTransGen
        (fun a c => (c ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
          c ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧ S.mult ε ω a c ≠ 0) x b}

theorem MatedCRTEnv.segmentReachEvent_subset_segmentReachEventAE {Ω : Type}
    [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ U ε : ℝ) :
    S.segmentReachEvent ρ U ε ⊆ S.segmentReachEventAE ρ U ε := by
  intro ω h x hx
  obtain ⟨u, ℓ, Y, hu, hθ⟩ := h x hx
  exact ⟨u, ℓ, Y, hu, ae_of_all _ hθ⟩

/-- **The almost-every-direction segment-path event from reachability.** The selection rule
`chainSelect` (a nodup chain through the cells met by the segment, chosen independently of the
direction) turns reachability for almost every direction into segment paths for almost every
direction. -/
theorem MatedCRTEnv.segmentReachEventAE_subset_segmentPathEventAE {Ω : Type}
    [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ U ε : ℝ) :
    S.segmentReachEventAE ρ U ε ⊆ S.segmentPathEventAE ρ U ε := by
  intro ω h x hx
  obtain ⟨u, ℓ, Y, hU, hθ⟩ := h x hx
  refine ⟨u, ℓ, Y, chainSelect (fun a c => S.mult ε ω a c ≠ 0)
    (· ∈ cellVertices ε (S.η ω) (ball 0 ρ)) (· ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ)) x,
    hU, fun T a ha => mem_of_mem_chainSelect ha, ae_of_all _ fun θ => nodup_chainSelect _,
    ae_of_all _ fun θ => isChain_chainSelect _, ?_⟩
  filter_upwards [hθ] with θ hθ
  obtain ⟨hxT, b, hb, hreach⟩ := hθ
  exact exists_chainSelect_eq_cons_of_reflTransGen hxT hx.1 hb hreach

/-- **Lemma 2.15 from the segment-ball estimate and segment reachability for almost every
direction.** The cell size estimate, the degree bound, the segment-ball estimate `E_ε(2, r)` for
every `r ∈ (0, 1)` and the almost-every-direction segment reachability event (at some radius
`U`), each with polynomially high probability for every valid environment, give
`GreenFunctionCrudeBoundStmt`. This contains
`greenFunctionCrudeBoundStmt_of_segmentBalls_of_reachable`
(by `MatedCRTEnv.segmentReachEvent_subset_segmentReachEventAE`). -/
theorem greenFunctionCrudeBoundStmt_of_segmentBalls_of_reachableAE {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hseg : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ r ∈ Ioo (0 : ℝ) 1, PolyHighProb S.P (S.segmentBallEvent r))
    (hR : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ U : ℝ, 0 ≤ U ∧ PolyHighProb S.P (S.segmentReachEventAE ρ U)) :
    GreenFunctionCrudeBoundStmt 𝒮 := by
  refine greenFunctionCrudeBoundStmt_of_inball_of_segmentPathsAE hcell hdeg
    (fun γ hγ hγ2 δ ρ hδ hρ hρ1 Ω _ S hS =>
      hS.polyHighProb_cellInballEvent_of_segmentBalls hcell hγ hγ2 hδ hρ hρ1
        (hseg γ hγ hγ2 Ω S hS))
    (fun γ hγ hγ2 ρ hρ hρ1 Ω _ S hS => ?_)
  obtain ⟨U, hU, hRU⟩ := hR γ hγ hγ2 ρ hρ hρ1 Ω S hS
  exact ⟨U, hU, hRU.mono fun ε => S.segmentReachEventAE_subset_segmentPathEventAE ρ U ε⟩

end PolyHigh

end MatedCRT
