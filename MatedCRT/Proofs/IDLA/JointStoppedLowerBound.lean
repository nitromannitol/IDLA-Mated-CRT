import MatedCRT.Proofs.Sec5.IDLALowerBound.Stopped
import MatedCRT.Proofs.IDLA.RandomOpenCell
import MatedCRT.Proofs.IDLA.JointRelaxedLowerBound
import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound

/-! Joint-law stopped lower bound for the harmonic-ball vertex domain. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open IDLALowerBound

theorem joint_iDLALowerBoundStopped_of_steps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h53 : StoppedMeanValueInequalityStep 𝒮) (h54 : StoppedLLowerBoundStep 𝒮) (h28 : CellSizeEstimateStmt 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆
          fillCells ε (S.η p.1) (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ4ρ : δ / 4 < ρ := by linarith
  obtain ⟨q, hq, h54'⟩ := h54 γ hγ hγ2 ρ hρ hρ1
  have h4 := h54' Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  obtain ⟨s, hsm, hspos, h3⟩ := h53 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  unfold TendsToOneOn at h3 h4
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
  -- Lemma 5.2 with `O₁ = {a ∈ V^ε(Λ_t) : dist(η(a), ∂V̄^ε(Λ_t)) > δ/4}`, `O₂ = V^ε(Λ_t)` (both empty off
  -- `{t < T, Λ_t ⊆ B_ρ}`) and `K = t/ε`
  set F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ} with hF
  set V : ℝ → Ω → Set ℤ := fun ε ω => cellVertices ε (S.η ω) (Λ ω t) with hV
  set G : Set Ω := {ω | ω ∈ F ∧ Λ ω t ⊆ ball 0 ρ} with hG
  set O₂ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ V ε ω | ω ∈ G} with hO₂
  set O₁ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ V ε ω | ω ∈ G ∧
    δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (V ε ω)))} with hO₁
  have hO₂eq : ∀ ε ω, ω ∈ G → O₂ ε ω = V ε ω := fun ε ω hω => by
    ext a
    exact ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
  have hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro ε _
    refine ae_of_all _ fun ω => ⟨fun a ha => ⟨ha.1, ha.2.1⟩, fun a ha => ?_⟩
    obtain ⟨x, hx1, hx2⟩ := ha.1
    exact ⟨x, hx1, ha.2.2 hx2⟩
  have h34 := h3.add h4
  rw [zero_add] at h34
  have hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) / greenFn (S.mult ε ω) (O₂ ε ω) a a}) := by
    unfold ProbTendsToOne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h34
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    rw [mem_compl_iff] at hω
    have hωG : ω ∈ G := by
      by_contra hωG
      exact hω fun a ha => absurd ha.2.1 hωG
    have hωF : ω ∈ F := hωG.1
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hcon
    apply hω
    rw [mem_ofPred_eq, hO₂eq ε ω hωG]
    exact fun a ha => ⟨hcon.1 hωF a ha.1 ha.2.2, hcon.2 hωF a ha.1 ha.2.2⟩
  have hO₂meas : ∀ ε, 0 < ε → ∀ k, NullMeasurableSet {ω | k ∈ O₂ ε ω} S.P := by
    intro ε hε k
    refine (hS.nullMeasurableSet_cellVertices_coneFamily hγ hγ2 hfam h24 hρ hρ1 hΛ ht ε hε.le k).congr ?_
    filter_upwards [hΛ] with ω hω
    have hmono := hω.2.1.monotoneOn
    simp only [hO₂, hV, hG, hF, mem_ofPred_eq]
    apply propext
    constructor
    · rintro ⟨hF, hk⟩
      exact ⟨hk, hF, (subset_ball_div_three_of_lt_clusterExitTime hmono ht hF).trans
        (ball_subset_ball (by linarith))⟩
    · rintro ⟨hk, hF, -⟩
      exact ⟨hF, hk⟩
  obtain ⟨-, hB⟩ := hS.joint_relaxedIDLABounds_of_pos hγ hγ2 hρ hρ1 h52
    O₁ O₂ (fun ε => t / ε) q s hO₂meas hO hq hsm hspos hgood
  -- the bad environments: large or degenerate cells, and the null set where `η` is not surjective or `Λ` not
  -- increasing
  set N : Set Ω := {ω | ¬ (Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} with hN_def
  have hN : S.P N = 0 := by
    have hae : ∀ᵐ ω ∂S.P, Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) := by
      filter_upwards [hS.isAreaParametrized, hΛ] with ω h1 h2
      exact ⟨h1.2.2.1, h2.2.1.monotoneOn⟩
    exact ae_iff.1 hae
  have hbad : Tendsto (fun ε => S.P ({ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - e)}ᶜ ∪ N)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcell
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun _ => (measure_union_le _ _).trans (by rw [hN, add_zero]))
  have h := hB.add hbad
  rw [zero_add] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, (tendsto_rpow_nhdsGT_zero' he).eventually (gt_mem_nhds hδ4)]
    with ε (hε : 0 < ε) hεe
  refine hS.idlaJointMeasure_le_add_env ε _ _ _ fun ω hω xs hxs => ?_
  simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hω
  obtain ⟨hcs, hωN⟩ := hω
  obtain ⟨hsurj, hmono⟩ :=
    not_not.1 (hωN : ¬¬ (Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0)))
  obtain ⟨hωF, hnot⟩ := hxs
  have hΛb : Λ ω t ⊆ ball 0 ρ :=
    (subset_ball_div_three_of_lt_clusterExitTime hmono ht hωF).trans (ball_subset_ball (by linarith))
  have hωG : ω ∈ G := ⟨hωF, hΛb⟩
  intro hsub
  apply hnot
  change O₁ ε ω ⊆ stoppedIDLACluster (O₂ ε ω) xs ⌊t / ε⌋₊ at hsub
  rw [hO₂eq ε ω hωG] at hsub
  have hcellL : ∀ a ∈ V ε ω, (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := by
    intro a ha
    obtain ⟨x, hx1, hx2⟩ := ha
    exact ⟨x, hx1, hΛb hx2⟩
  have hdiam : ∀ a ∈ V ε ω, ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) a) ∧
      diam (cell ε (S.η ω) a) ≤ ε ^ e := by
    intro a ha
    have := hcs a (hcellL a ha)
    rwa [hexp] at this
  have hb : ∀ a ∈ V ε ω, Bornology.IsBounded (cell ε (S.η ω) a) := by
    intro a ha
    by_contra hnb
    have h1 := (hdiam a ha).1
    rw [diam_eq_zero_of_unbounded hnb] at h1
    exact absurd h1 (not_le.2 (Real.rpow_pos_of_pos hε _))
  have hd : ∀ a ∈ V ε ω, diam (cell ε (S.η ω) a) < δ / 4 := fun a ha => (hdiam a ha).2.trans_lt hεe
  have hin : innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (V ε ω) :=
    fun x hx => subset_fillCells_cellVertices hε hsurj _ hx.1
  calc innerNbhd δ (Λ ω t)
      ⊆ fillCells ε (S.η ω) {a ∈ V ε ω |
          δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (V ε ω)))} :=
        innerNbhd_subset_fillCells_deep hε.le hδ hb hd hcellL hin
    _ ⊆ fillCells ε (S.η ω) (O₁ ε ω) := fillCells_mono' fun a ha => ⟨ha.1, hωG, ha.2⟩
    _ ⊆ fillCells ε (S.η ω) (stoppedIDLACluster (V ε ω) xs ⌊t / ε⌋₊) := fillCells_mono' hsub


/-- Proposition 5.1 in joint-law form, including its harmonic-ball stopped clause. -/
theorem joint_iDLALowerBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮) (h53 : MeanValueInequalityStmt 𝒮)
    (h54 : LLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (hSM : StoppedMeanValueInequalityStep 𝒮)
    (hSL : StoppedLLowerBoundStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
          (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  exact ⟨(joint_iDLALowerBound_discrete_of_steps 𝒮 h52 h53 h54 h28 hI
    (adjacentCellsMeetAeStep 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht).1,
    joint_iDLALowerBoundStopped_of_steps 𝒮 h52 hfam h24 hSM hSL h28
      γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht⟩

end MatedCRT
