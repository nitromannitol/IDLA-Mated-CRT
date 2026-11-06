import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableDiscrete
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.UniformSecondMoment
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.AreaParametrizedMass
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Draft.Section2
import MatedCRT.External.SLE

/-!
# LBM exit time: good events and the walk bound

The polynomially-high-probability events used for the discrete part of `LBMExitTimeIntegrableStep`:
the second-moment event (`scaled_secondMoment_finite_bound_polyHighProb`), the mass event of a disk, the
cell-size event (`CellSizeEstimateStmt`) and the a.s. geometry of the curve. On their intersection the
expectation of the truncated exit functional of the interpolated walk is bounded by a random constant that does
not depend on the mesh.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The second-moment event of `scaled_secondMoment_finite_bound_polyHighProb` at radius `ρ`. -/
def lbmMomEv (S : MatedCRTEnv Ω) (ρ α B : ℝ) (ε : ℝ) : Set Ω :=
  {ω | largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ ∧
    ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
      ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D,
        ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
          ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2}

/-- The cell-size event of `CellSizeEstimateStmt`, for the cells meeting `B(0, ρ)`. -/
def lbmCellEv (S : MatedCRTEnv Ω) (ρ γ ζ : ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
    ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ Metric.diam (cell ε (S.η ω) k) ∧
      Metric.diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}

/-- The mass event: the mass of the disk `D` is at least `ε ^ α`. -/
def lbmMassEv (S : MatedCRTEnv Ω) (D : Set ℂ) (α ε : ℝ) : Set Ω :=
  {ω | ENNReal.ofReal (ε ^ α) ≤ S.μ ω D}

/-- The a.s. geometry of the curve: continuous, surjective and proper. -/
def lbmGeoEv (S : MatedCRTEnv Ω) : Set Ω :=
  {ω | Continuous (S.η ω) ∧ Function.Surjective (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)}

/-- The good event at scale `ε` for the disk `D`: the intersection of the four events. -/
def lbmGoodEv (S : MatedCRTEnv Ω) (ρ α B ρ' γ ζ : ℝ) (D : Set ℂ) (ε : ℝ) : Set Ω :=
  lbmMomEv S ρ α B ε ∩ lbmMassEv S D α ε ∩ lbmCellEv S ρ' γ ζ ε ∩ lbmGeoEv S

/-- `P(E ε)ᶜ → 0` as `ε → 0⁺` for a polynomially-high-probability family. -/
theorem tendsto_measure_compl_of_polyHighProb {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : _root_.HarmonicBalls.PolyHighProb P E) :
    Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => C * ε ^ p) :=
      continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hp.le)
    have h0 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne', mul_zero] at h0
    have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal.tendsto _).comp h0
    rwa [ENNReal.ofReal_zero] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun ε => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ε hε
  exact h ε hε.1 hε.2

/-- `ε ^ α ≤ q` for small `ε`, when `α > 0` and `q > 0`. -/
theorem eventually_rpow_le {α : ℝ} (hα : 0 < α) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ α ≤ q := by
  have hc : Continuous (fun ε : ℝ => ε ^ α) := continuous_id.rpow_const fun _ => Or.inr hα.le
  have h0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ α)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hα.ne'] at h0
  exact h0.eventually (Iic_mem_nhds hq)

/-- The mass event fails with vanishing probability, by the lower bound on the mass of a fixed disk. -/
theorem tendsto_measure_mass_compl (S : MatedCRTEnv Ω) (D : Set ℂ) {α : ℝ} (hα : 0 < α)
    (hmass : ∀ δ : ℝ≥0∞, 0 < δ → ∃ q : ℝ, 0 < q ∧ S.P {ω | S.μ ω D < ENNReal.ofReal q} < δ) :
    Tendsto (fun ε => S.P (lbmMassEv S D α ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨q, hq, hPq⟩ := hmass δ hδ
  filter_upwards [eventually_rpow_le hα hq] with ε hε
  refine le_of_lt (lt_of_le_of_lt (measure_mono ?_) hPq)
  intro ω hω
  simp only [lbmMassEv, mem_compl_iff, mem_ofPred_eq, not_le] at hω ⊢
  exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal hε)

/-- The good event fails with vanishing probability, given the moment and cell events and the a.s. geometry. -/
theorem tendsto_compl_lbmGoodEv (S : MatedCRTEnv Ω) (ρ α B ρ' γ ζ : ℝ) (D : Set ℂ)
    (hmomE : _root_.HarmonicBalls.PolyHighProb S.P (lbmMomEv S ρ α B))
    (hcellE : _root_.HarmonicBalls.PolyHighProb S.P (lbmCellEv S ρ' γ ζ))
    (hmassD : ∀ δ : ℝ≥0∞, 0 < δ → ∃ q : ℝ, 0 < q ∧ S.P {ω | S.μ ω D < ENNReal.ofReal q} < δ)
    (hα : 0 < α) (hgeo : ∀ᵐ ω ∂S.P, ω ∈ lbmGeoEv S) :
    Tendsto (fun ε => S.P (lbmGoodEv S ρ α B ρ' γ ζ D ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_measure_compl_of_polyHighProb hmomE
  have h2 := tendsto_measure_mass_compl S D hα hmassD
  have h3 := tendsto_measure_compl_of_polyHighProb hcellE
  have h4 : S.P (lbmGeoEv S)ᶜ = 0 := ae_iff.1 hgeo
  have hbound : ∀ ε, S.P (lbmGoodEv S ρ α B ρ' γ ζ D ε)ᶜ ≤
      S.P (lbmMomEv S ρ α B ε)ᶜ + S.P (lbmMassEv S D α ε)ᶜ + S.P (lbmCellEv S ρ' γ ζ ε)ᶜ := by
    intro ε
    have hset : (lbmGoodEv S ρ α B ρ' γ ζ D ε)ᶜ =
        ((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ ∪ (lbmCellEv S ρ' γ ζ ε)ᶜ) ∪
          (lbmGeoEv S)ᶜ := by
      simp only [lbmGoodEv, Set.compl_inter]
    have e1 : S.P ((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ) ≤
        S.P (lbmMomEv S ρ α B ε)ᶜ + S.P (lbmMassEv S D α ε)ᶜ :=
      measure_union_le _ _
    have e2 : S.P ((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ ∪ (lbmCellEv S ρ' γ ζ ε)ᶜ) ≤
        S.P ((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ) + S.P (lbmCellEv S ρ' γ ζ ε)ᶜ :=
      measure_union_le _ _
    have e3 : S.P (((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ ∪ (lbmCellEv S ρ' γ ζ ε)ᶜ) ∪
        (lbmGeoEv S)ᶜ) ≤
        S.P ((lbmMomEv S ρ α B ε)ᶜ ∪ (lbmMassEv S D α ε)ᶜ ∪ (lbmCellEv S ρ' γ ζ ε)ᶜ) +
          S.P (lbmGeoEv S)ᶜ :=
      measure_union_le _ _
    rw [hset]
    rw [h4, add_zero] at e3
    exact e3.trans (e2.trans (add_le_add e1 le_rfl))
  have hlim : Tendsto (fun ε => S.P (lbmMomEv S ρ α B ε)ᶜ + S.P (lbmMassEv S D α ε)ᶜ +
      S.P (lbmCellEv S ρ' γ ζ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    simpa using (h1.add h2).add h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun ε => zero_le) (Eventually.of_forall hbound)

/-- **Walk bound on a good event.** For a point `ω` of the good event at scale `ε`, the expectation of the truncated
exit functional of the interpolated walk from the inner disk `B(z, r - δ)` is at most the random constant
`(1 + B · L²)` (real part), where `L` is the largest exit-time random variable. -/
theorem walk_integral_le_of_good (S : MatedCRTEnv Ω) {ρ ρ' α B δ : ℝ} {ε : ℝ} {ω : Ω}
    (hε : 0 < ε) (hm : 0 < S.mε ε) {z y : ℂ} {r : ℝ} (hr : 0 < r) (hδ : 0 < δ) (n : ℕ)
    (hy : y ∈ ball z r) (hD : ball z r ⊆ ball 0 ρ) (hρρ' : ρ < ρ')
    (hgeo : ω ∈ lbmGeoEv S) (hmomω : ω ∈ lbmMomEv S ρ α B ε)
    (hmassω : ω ∈ lbmMassEv S (ball z r) α ε)
    (hcellω : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ').Nonempty →
      Metric.diam (cell ε (S.η ω) k) ≤ δ) :
    ∫ x, truncatedExitFunctional (ball z (r - δ)) n (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) ≤
      (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2).toReal := by
  obtain ⟨hL, hmom⟩ := hmomω
  obtain ⟨hcont, hsurj, hprop⟩ := hgeo
  have hstart : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (ball z r) := by
    have hy_cell := Tightness.mem_cell_vertexOf hcont hprop hsurj hε y
    have hne : (cell ε (S.η ω) (vertexOf ε (S.η ω) y) ∩ ball z r).Nonempty := ⟨y, hy_cell, hy⟩
    exact hne
  have hK := hmom (ball z r) measurableSet_ball hD hmassω (vertexOf ε (S.η ω) y) hstart
  have hfrontier : frontier (ball z r) ⊆ ball 0 ρ' := by
    intro q hq
    have h1 : q ∈ closure (ball z r) := frontier_subset_closure hq
    have h2 : closure (ball z r) ⊆ closure (ball 0 ρ) := closure_mono hD
    have h3 : closure (ball (0 : ℂ) ρ) ⊆ closedBall (0 : ℂ) ρ := closure_ball_subset_closedBall
    have h4 : dist q 0 ≤ ρ := mem_closedBall.1 (h3 (h2 h1))
    exact mem_ball.2 (lt_of_le_of_lt h4 hρρ')
  have hcell : ∀ k : ℤ, (cell ε (S.η ω) k ∩ frontier (ball z r)).Nonempty →
      ∀ p ∈ cell ε (S.η ω) k, ∀ q ∈ cell ε (S.η ω) k, dist p q ≤ δ := by
    intro k hne p hp q hq
    obtain ⟨c, hc1, hc2⟩ := hne
    have hne' : (cell ε (S.η ω) k ∩ ball 0 ρ').Nonempty := ⟨c, hc1, hfrontier hc2⟩
    have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := (isCompact_Icc.image hcont).isBounded
    exact (Metric.dist_le_diam_of_mem hbdd hp hq).trans (hcellω k hne')
  have key := lintegral_ofReal_truncatedExit_le hε.le hm (S.mult ε ω) (vertexOf ε (S.η ω) y)
    hr hδ.le n hcell hK
  have hGm : AEStronglyMeasurable
      (fun x => truncatedExitFunctional (ball z (r - δ)) n (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) :=
    (measurable_truncatedExitFunctional_interpolatedWalk ε (S.η ω) (S.mε ε) z (r - δ) n).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)]
      fun x => truncatedExitFunctional (ball z (r - δ)) n (interpolatedWalk ε (S.η ω) (S.mε ε) x) :=
    Eventually.of_forall fun x => truncatedExitFunctional_nonneg _ _ _
  rw [integral_eq_lintegral_of_nonneg_ae hnn hGm]
  have hfin : (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hL.ne)⟩
  exact ENNReal.toReal_mono hfin key

end MatedCRT
