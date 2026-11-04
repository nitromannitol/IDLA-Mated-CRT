import MatedCRT.Proofs.Sec5.LLowerBound.ApplyKernel
import MatedCRT.Proofs.Sec5.LLowerBound.MassProb
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# The Green-sum local event

The Green and counting estimates, together with uniform cell diameter and
mass bounds, imply the local witnesses. Local finiteness uses the separately
stated adjacency-of-cells step of the mating-of-trees coupling.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology

/-- The local Green-sum event follows from the mating-of-trees adjacency
step and the two estimates cited in the paper. -/
theorem lLowerBoundLocalStep_of_adjacentCellsMeet
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    LLowerBoundLocalStep 𝒮 := by
  intro h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  let ρ' : ℝ := (1 + ρ) / 2
  have hρ'0 : 0 < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  have hρρ' : ρ < ρ' := by dsimp [ρ']; linarith
  obtain ⟨ω, hω, h216a⟩ := h216 γ hγ hγ2
  obtain ⟨C, hC, h216b⟩ := h216a ρ' hρ'0 hρ'1
  obtain ⟨α, β, hα, hβ, h29a⟩ := h29 γ hγ hγ2
  obtain ⟨R, r, d, hR0, hr0, hd0, hRδ, hRρ, hrR, hgap, hdδ, hscale⟩ :=
    exists_green_lower_radii (C := C) hδ hρ1
  have hsep : ρ + R ≤ ρ' := by dsimp [ρ']; linarith
  have hgood : ∀ᵐ ξ ∂S.P, IsAreaParametrized (S.μ ξ) (S.η ξ) ∧
      Tendsto (S.η ξ) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ξ) :=
    (hS.isAreaParametrized.and (hS.ae_tendsto_cocompact.and
      (hS.ae_isLocallyFiniteMult hγ hγ2 hcell)))
  have hall := (((((probTendsToOne_of_ae hgood).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h216b Ω S hS))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h29a ρ' hρ'0 hρ'1 Ω S hS))).inter
    (hS.probTendsToOne_small_cells (ρ + δ / 2) d hd0)).inter
    (hS.probTendsToOne_ball_mass_rpow ρ r α (1 / 2) hr0 hα (by norm_num))).inter
    (hS.probTendsToOne_ball_mass_rpow ρ r (1 / 4) (1 / 4) hr0 (by norm_num) (by norm_num))
  have hfull : ProbTendsToOne S.P fun ε => {ξ |
      let m := S.mult ε ξ
      let A := matedDiscreteCluster m ε (S.η ξ) ρ t
      let B := ballInterior ε (S.η ξ) ρ
      (∀ a, {b | m a b ≠ 0}.Finite) ∧ (∀ a, m a (a + 1) ≠ 0) ∧
      A.Finite ∧ B.Finite ∧ A ⊆ B ∧ A ⊆ cellVertices ε (S.η ξ) (ball 0 ρ) ∧
      ∀ a ∈ A, δ < infDist (vertexPoint ε (S.η ξ) a) (frontier (fillCells ε (S.η ξ) A)) →
        ∃ (D Cset : Set ℤ) (α' M : ℝ), Cset.Finite ∧ D ⊆ Cset ∧ Cset ⊆ A ∧
          (∀ b ∈ D, (1 / 2 : ℝ) ≤ greenKernel m Cset a b) ∧
          ε⁻¹ * M - ε ^ (-1 + α') ≤ (D.ncard : ℝ) ∧
          ε ^ α' ≤ M / 2 ∧ ε ^ (1 / 4 : ℝ) ≤ M / 4} := by
    refine hall.mono_ev ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
      (tendsto_rpow_nhdsGT_zero hω).eventually (Iio_mem_nhds (lt_min hR0 (sub_pos.mpr hρρ'))),
      Ioo_mem_nhdsGT (Real.exp_pos (-(3 / 2) * C))] with ε hε hε1 hpow hexp ξ hξ
    obtain ⟨⟨⟨⟨⟨⟨hη, hp, hlf⟩, hg⟩, hc⟩, hsmall⟩, hmass1⟩, hmass2⟩ := hξ
    have hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹ := by
      have h := inv_anti₀ hε hexp.2.le
      rwa [← Real.exp_neg, show -(-(3 / 2) * C) = 3 / 2 * C by ring] at h
    have hpowR : ε ^ ω ≤ R := (lt_of_lt_of_le hpow (min_le_left _ _)).le
    have hpowρ : ρ ≤ ρ' - ε ^ ω := by
      have := lt_of_lt_of_le hpow (min_le_right _ _)
      linarith
    let A := matedDiscreteCluster (S.mult ε ξ) ε (S.η ξ) ρ t
    let B := ballInterior ε (S.η ξ) ρ
    have hAB : A ⊆ B := matedDiscreteCluster_subset_ballInterior hε ht
    have hB : B.Finite := ballInterior_finite hη.1 hp hε
    have hA : A.Finite := hB.subset hAB
    refine ⟨hlf ε hε, S.mult_succ_ne_zero hε.le ξ, hA, hB, hAB,
      hAB.trans ballInterior_subset_cellVertices_ball, ?_⟩
    intro a ha hdist
    have hpoint : vertexPoint ε (S.η ξ) a ∈ ball 0 ρ :=
      mem_ball_of_mem_cell hη.1 (hAB ha) (ConstantOrderDiv.vertexPoint_mem_cell hε.le _ _)
    apply localData_of_green_counting hη hε hε1.2.le hδ hβ hA ha hdist hpoint
      hρ'0.le hsep hpowρ hpowR hRδ hrR hR0.le hgap hdδ hC hinv hscale hg hc hsmall
    · simpa [div_eq_mul_inv, mul_comm] using hmass1 _ hpoint
    · simpa [div_eq_mul_inv, mul_comm] using hmass2 _ hpoint
  unfold TendsToOneOn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfull
    (fun _ => zero_le) fun ε => ?_
  exact measure_mono (inter_subset_right)

/-- The Green-sum step follows once adjacent cells are known to meet. -/
theorem lLowerBoundSumStep_of_adjacentCellsMeet
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    LLowerBoundSumStep 𝒮 :=
  lLowerBoundSumStep_of_local 𝒮 (lLowerBoundLocalStep_of_adjacentCellsMeet 𝒮 hcell)

end MatedCRT
