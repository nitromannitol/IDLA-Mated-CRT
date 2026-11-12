import MatedCRT.FirstPass.Derived.GreenCellSegmentPaths
import MatedCRT.FirstPass.S5c.GreenDiagDomination
import LatticeProb.Analysis.FatCellEnergyAsymptotics

/-!
# The crude Green function bound on the good event of the cell estimates

BG20 Lemma 5.6, pathwise part: for a valid environment there is `ε₀ > 0` such that almost
surely, for every `ε ∈ (0, ε₀)`, if

* (E1) the cells meeting `B_ρ` have diameters in `[ε^p, ε^q]`,
* (E2) each of them contains a disc of radius `ε^{δ/4}` times its diameter,
* (E3) the vertices of `V^ε(B_ρ)` have degree at most `ε^{-δ}`,
* every vertex `x` of `A = V^ε(B_ρ) \ V^ε(∂B_ρ)` has segment paths from a point `u` with
  `‖u‖ ≤ U` that stay in `V^ε(B_ρ)` and end outside `A`,

then the Green function of the walk on `𝒢^ε` killed on exiting `A` is at most `ε^{-ζ}`
everywhere, provided `5δ/2 < ζ`. The probabilistic inputs (E1)-(E3) and the segment paths
are hypotheses; the bound itself combines the almost sure segment-path estimate
(`MatedCRTEnv.IsValid.ae_greenFn_interiorCellVertices_le_of_segmentPaths`), the domination
of the Green function by its diagonal (`greenFn_le_of_diag_le`) and the exponent bookkeeping
`LatticeProb.eventually_fatCell_energy_rpow_le`.

## Main statements

* `MatedCRT.MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds`
-/

open Set Metric MeasureTheory Filter Topology LatticeProb

namespace MatedCRT

/-- **Crude Green function bound on the good event (BG20 Lemma 5.6, pathwise part).** For a
valid environment and exponents with `0 ≤ q`, `5δ/2 < ζ`, there is `ε₀ > 0` such that almost
surely, for every `ε ∈ (0, ε₀)`: if the cells meeting `B_ρ` have diameters in `[ε^p, ε^q]`,
contain discs of radius `ε^{δ/4}` times their diameters, have degrees at most `ε^{-δ}`, and
every vertex of `A = V^ε(B_ρ) \ V^ε(∂B_ρ)` has segment paths (from a point of norm at most `U`)
staying in `V^ε(B_ρ)` and ending outside `A`, then `G_A(a, b) ≤ ε^{-ζ}` for all `a, b`. -/
theorem MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds
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
        (∀ θ, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ θ, (segmentPath u ℓ (cell ε (S.η ω)) Y F θ).IsChain
          fun a b => S.mult ε ω a b ≠ 0) ∧
        (∀ θ, ∃ l, segmentPath u ℓ (cell ε (S.η ω)) Y F θ = x :: l ∧
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
    hS.ae_greenFn_interiorCellVertices_le_of_segmentPaths hγ hγ2] with ω hc hp hadj hG
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

end MatedCRT
