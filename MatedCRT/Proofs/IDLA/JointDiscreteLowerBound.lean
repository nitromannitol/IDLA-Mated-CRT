import MatedCRT.Proofs.IDLA.JointRelaxedLowerBound
import MatedCRT.Proofs.IDLA.DiscreteClusterMeasurable
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! # Joint-law lower bound for the discrete obstacle cluster -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

open IDLALowerBound in
/-- Proposition 5.1 in the joint-law form, with walkers optionally stopped at the discrete cluster. -/
theorem joint_iDLALowerBound_discrete_of_steps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
          ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
          ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
            (stoppedIDLACluster (matedDiscreteCluster (S.mult ε p.1) ε (S.η p.1) ρ t) p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ4ρ : δ / 4 < ρ := by linarith
  obtain ⟨q, hq, h54'⟩ := h54 γ hγ hγ2 ρ hρ hρ1
  have h4 := h54' Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  obtain ⟨s, hsm, hspos, h3⟩ := h53 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  have hI' := hI γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 2) t (by positivity) (by linarith) ht
  unfold TendsToOneOn at h3 h4 hI'
  -- the cell-size estimate with `ζ = 1/(2+γ)²`
  set e : ℝ := 1 / (2 + γ) ^ 2 with he_def
  have he : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he_def]
    ring
  have hcell := probTendsToOne_of_polyHighProb' (h28 γ hγ hγ2 e ρ he he1 hρ hρ1 Ω S hS)
  unfold ProbTendsToOne at hcell
  -- Lemma 5.2 with `O₁ = {a ∈ Λ^ε_t : dist(η(a), ∂Λ̄^ε_t) > δ/4}` (empty off `{t < T}`), `O₂ = Λ^ε_t`, `K = t/ε`
  set F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ} with hF
  set L : ℝ → Ω → Set ℤ := fun ε ω => matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t with hL
  set O₁ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ L ε ω | ω ∈ F ∧
    δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} with hO₁
  have hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ L ε ω ∧ L ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) :=
    fun ε _ => ae_of_all _ fun ω => ⟨fun a ha => ha.1, fun a ha => ha.1⟩
  have h34 := h3.add h4
  rw [zero_add] at h34
  have hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : L ε ω, greenFn (S.mult ε ω) (L ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (L ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : L ε ω, greenFn (S.mult ε ω) (L ε ω) b a) / greenFn (S.mult ε ω) (L ε ω) a a}) := by
    unfold ProbTendsToOne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h34
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    rw [mem_compl_iff] at hω
    have hωF : ω ∈ F := by
      by_contra hωF
      exact hω fun a ha => absurd ha.2.1 hωF
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hcon
    exact hω fun a ha => ⟨hcon.1 hωF a ha.1 ha.2.2, hcon.2 hωF a ha.1 ha.2.2⟩
  have hlf := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ2 hadj
  have hLmeas : ∀ ε, 0 < ε → ∀ k, NullMeasurableSet {ω | k ∈ L ε ω} S.P := by
    intro ε hε k
    apply hS.nullMeasurableSet_mem_matedDiscreteCluster hγ hγ2 hε ρ t ht k
    filter_upwards [hlf] with ω hω
    exact hω ε hε
  obtain ⟨hA, hB⟩ := hS.joint_relaxedIDLABounds_of_pos hγ hγ2 hρ hρ1 h52
    O₁ L (fun ε => t / ε) q s hLmeas hO hq hsm hspos hgood
  -- from `O₁ ⊆ A` to `B⁻_δ(Λ_t) ⊆ Ā`, off the bad events of the cell size and of Proposition 4.2
  have hbad : Tendsto (fun ε => S.P ((F ∩ {ω | innerNbhd (δ / 2) (Λ ω t) ⊆
      fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪ {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - e)}ᶜ)) (𝓝[>] 0) (𝓝 0) := by
    have h := hI'.add hcell
    rw [zero_add] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun _ => measure_union_le _ _)
  have fin : ∀ clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ,
      Tendsto (fun ε => S.idlaJointMeasure ε {p | ¬ O₁ ε p.1 ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (clus ε p.1 p.2)}) (𝓝[>] 0) (𝓝 0) := by
    intro clus hcl
    have h := hcl.add hbad
    rw [zero_add] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin, (tendsto_rpow_nhdsGT_zero' he).eventually (gt_mem_nhds hδ4)]
      with ε (hε : 0 < ε) hεe
    refine hS.idlaJointMeasure_le_add_env ε _ _ _ fun ω hω xs hxs => ?_
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hω
    obtain ⟨hωF, hnot⟩ := hxs
    have hin := hω.1 hωF
    have hcs := hω.2
    intro hsub
    apply hnot
    have hcellL : ∀ a ∈ L ε ω, (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := fun a ha => ha.1
    have hdiam : ∀ a ∈ L ε ω, ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) a) ∧
        diam (cell ε (S.η ω) a) ≤ ε ^ e := by
      intro a ha
      have := hcs a (hcellL a ha)
      rwa [hexp] at this
    have hb : ∀ a ∈ L ε ω, Bornology.IsBounded (cell ε (S.η ω) a) := by
      intro a ha
      by_contra hnb
      have h1 := (hdiam a ha).1
      rw [diam_eq_zero_of_unbounded hnb] at h1
      exact absurd h1 (not_le.2 (Real.rpow_pos_of_pos hε _))
    have hd : ∀ a ∈ L ε ω, diam (cell ε (S.η ω) a) < δ / 4 := fun a ha => (hdiam a ha).2.trans_lt hεe
    calc innerNbhd δ (Λ ω t)
        ⊆ fillCells ε (S.η ω) {a ∈ L ε ω |
            δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} :=
          innerNbhd_subset_fillCells_deep hε.le hδ hb hd hcellL hin
      _ ⊆ fillCells ε (S.η ω) (O₁ ε ω) := fillCells_mono' fun a ha => ⟨ha.1, hωF, ha.2⟩
      _ ⊆ fillCells ε (S.η ω) (clus ε ω xs) := fillCells_mono' hsub
  exact ⟨fin (fun ε _ xs => idlaCluster xs ⌊t / ε⌋₊) hA,
    fin (fun ε ω xs => stoppedIDLACluster (L ε ω) xs ⌊t / ε⌋₊) hB⟩


/-- Proposition 5.1 from the relaxed lower bound, geometric estimates, and the stopped step. -/
theorem iDLALowerBound_of_steps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) (hstop : IDLALowerBoundStoppedStep 𝒮) : IDLALowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hj := (joint_iDLALowerBound_discrete_of_steps 𝒮 h52 h53 h54 h28 hI
    (adjacentCellsMeetAeStep 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht).1
  exact ⟨hj, hstop γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht⟩

end MatedCRT
