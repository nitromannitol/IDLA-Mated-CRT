import MatedCRT.FirstPass.S5r.NullMeasurableCorrected
import MatedCRT.FirstPass.S2b
import MatedCRT.FirstPass.S5d.StoppedSteps
import MatedCRT.FirstPass.S5d.Transfer

/-!
# Reduction of the stopped clause of Proposition 5.1 to the two Green steps

`iDLALowerBoundStopped_of_greenSteps`: `IDLALowerBoundStoppedStep` (Steps/Sec5/IDLALowerBound.lean:68) follows from the
relaxed Lemma 5.2 (`GeneralIDLALowerBoundRelaxedStep`), the cone-family measurability inputs, and the NEW Green steps
`StoppedFirstGreenStep` and `StoppedSecondGreenStep`. The proof: apply Lemma 5.2 with killing set
`I^ε_t = stoppedKillSet` and targets `Z^ε_t ∩ I^ε_t`; the exceptional environments have probability tending to `0`
(first Green event, and the null set where `η` is not onto); on the rest, the cover of `B⁻_δ(Λ_t)` by the cells of
`Z^ε_t` is inherited by the stopped cluster on `V^ε(Λ_t)` through the monotonicity of stopped IDLA in its stopping
domain (`stoppedIDLACluster_mono`, referee section 5.4).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

theorem iDLALowerBoundStopped_of_greenSteps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG1 : StoppedFirstGreenStep 𝒮) (hG2 : StoppedSecondGreenStep 𝒮) : IDLALowerBoundStoppedStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  obtain ⟨s, hsm, hspos, hF1⟩ := hG1 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  have hF2 := hG2 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  -- measurability of the killing sets (as in Proofs/IDLA/JointDiscreteLowerBound.lean:66-70)
  have hlf := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ2 (adjacentCellsMeetAeStep 𝒮)
  have hM : ∀ ε, 0 < ε → ∀ k : ℤ,
      NullMeasurableSet {ω | k ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t} S.P := by
    intro ε hε k
    apply hS.nullMeasurableSet_mem_matedDiscreteCluster hγ hγ2 hε ρ t ht k
    filter_upwards [hlf] with ω hω
    exact hω ε hε
  have hsurjAe : ∀ᵐ ω ∂S.P, Function.Surjective (S.η ω) := by
    filter_upwards [hS.isAreaParametrized] with ω h1
    exact h1.2.2.1
  have hU : ∀ ε, 0 < ε → ∀ k : ℤ, NullMeasurableSet {ω | k ∈ stoppedKillSet S Λ ρ t ε ω} S.P := by
    intro ε hε k
    have hB := hS.nullMeasurableSet_cellVertices_coneFamily_corrected hγ hγ2 hfam h24c hρ hρ1 hΛ ht ε hε.le k
    have hset : {ω | k ∈ stoppedKillSet S Λ ρ t ε ω} =
        {ω | k ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t} ∩
          {ω | t < clusterExitTime (Λ ω) ρ ∧ k ∈ cellVertices ε (S.η ω) (Λ ω t)} := by
      ext ω
      simp only [stoppedKillSet, mem_ofPred_eq, mem_inter_iff]
      tauto
    rw [hset]
    exact (hM ε hε k).inter hB
  -- the targets in the killing set, and the killing set in `V^ε(B_ρ)`
  have hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      {a | a ∈ stoppedKillSet S Λ ρ t ε ω ∧ a ∈ stoppedTargetSet S Λ δ t ε ω} ⊆ stoppedKillSet S Λ ρ t ε ω ∧
        stoppedKillSet S Λ ρ t ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro ε _
    refine Filter.Eventually.of_forall fun ω => ⟨fun a ha => ha.1, fun a ha => ?_⟩
    have hM' : a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t := (show _ ∧ _ from ha).2.1
    exact (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from hM').1
  -- the first Green event on `{t < T}` gives the Green event of the relaxed Lemma 5.2 off a set of small probability
  have hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈
      {a | a ∈ stoppedKillSet S Λ ρ t ε ω ∧ a ∈ stoppedTargetSet S Λ δ t ε ω},
      (1 + s ω) * ∑' b : stoppedKillSet S Λ ρ t ε ω,
          greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) 0 a ∧
      ε ^ (-(1 / 4 : ℝ)) ≤
        (∑' b : stoppedKillSet S Λ ρ t ε ω, greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) b a) /
          greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a a}) := by
    unfold TendsToOneOn at hF1 hF2
    unfold ProbTendsToOne
    have hsum := hF1.add hF2
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε _
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    have hωF : ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} := by
      by_contra hn
      apply hω
      intro a ha
      exact absurd (show t < clusterExitTime (Λ ω) ρ ∧ _ from ha.1).1 hn
    by_cases h1 : ω ∈ stoppedFirstGreenEvent S Λ ρ t δ s ε
    · by_cases h2 : ω ∈ stoppedSecondGreenEvent S Λ ρ t δ ε
      · exfalso
        apply hω
        intro a ha
        exact ⟨h1.2 a ha.2, h2 a ha.2⟩
      · exact Or.inr ⟨hωF, h2⟩
    · exact Or.inl ⟨hωF, h1⟩
  obtain ⟨-, hB⟩ := hS.joint_relaxedIDLABounds_of_pos hγ hγ2 hρ hρ1 h52
    (fun ε ω => {a | a ∈ stoppedKillSet S Λ ρ t ε ω ∧ a ∈ stoppedTargetSet S Λ δ t ε ω})
    (fun ε ω => stoppedKillSet S Λ ρ t ε ω) (fun ε => t / ε) (1 / 4) s hU hO (by norm_num) hsm hspos hgood
  -- the exceptional sets: `X^ε = (F ∩ (first Green event)ᶜ) ∪ N`, where `N` is the null set where `η` is not onto
  set N : Set Ω := {ω | ¬ Function.Surjective (S.η ω)} with hN_def
  have hN : S.P N = 0 := ae_iff.1 hsurjAe
  set X : ℝ → Set Ω := fun ε =>
    ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (stoppedFirstGreenEvent S Λ ρ t δ s ε)ᶜ) ∪ N with hX_def
  have hX0 : Tendsto (fun ε => S.P (X ε)) (𝓝[>] 0) (𝓝 0) := by
    have hF1' : Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
        (stoppedFirstGreenEvent S Λ ρ t δ s ε)ᶜ)) (𝓝[>] 0) (𝓝 0) := hF1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF1'
      (Filter.Eventually.of_forall fun _ => zero_le) (Filter.Eventually.of_forall fun ε => ?_)
    calc S.P (X ε) ≤ S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (stoppedFirstGreenEvent S Λ ρ t δ s ε)ᶜ) + S.P N :=
          measure_union_le _ _
      _ = S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (stoppedFirstGreenEvent S Λ ρ t δ s ε)ᶜ) := by
          rw [hN, add_zero]
  -- the inclusion of the stopped event into the relaxed event and the exceptional set
  have hsub : ∀ ε, 0 < ε →
      {p : Ω × (ℕ → ℕ → ℤ) | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆
          fillCells ε (S.η p.1) (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)} ⊆
      {p : Ω × (ℕ → ℕ → ℤ) | ¬ (fun ε ω => {a | a ∈ stoppedKillSet S Λ ρ t ε ω ∧
          a ∈ stoppedTargetSet S Λ δ t ε ω}) ε p.1 ⊆
            stoppedIDLACluster ((fun ε ω => stoppedKillSet S Λ ρ t ε ω) ε p.1) p.2 ⌊t / ε⌋₊} ∪
        (X ε ×ˢ univ) := by
    intro ε hε p hp
    obtain ⟨hpT, hpnot⟩ := hp
    by_contra hcon
    have hpX : p.1 ∉ X ε := fun h => hcon (Or.inr ⟨h, mem_univ _⟩)
    have hpE1 : {a | a ∈ stoppedKillSet S Λ ρ t ε p.1 ∧ a ∈ stoppedTargetSet S Λ δ t ε p.1} ⊆
        stoppedIDLACluster (stoppedKillSet S Λ ρ t ε p.1) p.2 ⌊t / ε⌋₊ := by
      by_contra h
      exact hcon (Or.inl h)
    have hE1 : p.1 ∈ stoppedFirstGreenEvent S Λ ρ t δ s ε := by
      by_contra h
      exact hpX (Or.inl ⟨hpT, h⟩)
    have hsurj : Function.Surjective (S.η p.1) := by
      by_contra h
      exact hpX (Or.inr h)
    -- the targets are in the killing set, hence in the stopped cluster of the killing set
    have hZO : stoppedTargetSet S Λ δ t ε p.1 ⊆ stoppedIDLACluster (stoppedKillSet S Λ ρ t ε p.1) p.2 ⌊t / ε⌋₊ :=
      fun a ha => hpE1 ⟨hE1.1 ha, ha⟩
    -- monotonicity in the stopping domain: `I^ε_t ⊆ V^ε(Λ_t)` (referee section 5.4)
    have hUA : stoppedKillSet S Λ ρ t ε p.1 ⊆ cellVertices ε (S.η p.1) (Λ p.1 t) := fun a ha =>
      (show t < clusterExitTime (Λ p.1) ρ ∧ _ ∧ a ∈ cellVertices ε (S.η p.1) (Λ p.1 t) from ha).2.2
    have hZA : stoppedTargetSet S Λ δ t ε p.1 ⊆
        stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊ :=
      hZO.trans (stoppedIDLACluster_mono_domain hUA p.2 ⌊t / ε⌋₊)
    have hgeom := innerNbhd_subset_fillCells_cellVertices hε hsurj δ (Λ p.1 t)
    have hcov : innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (stoppedTargetSet S Λ δ t ε p.1) :=
      hgeom.trans (IDLALowerBound.fillCells_mono' fun _ ha => ha)
    exact hpnot (hcov.trans (IDLALowerBound.fillCells_mono' hZA))
  -- conclusion: the stopped event has probability at most the relaxed one plus the exceptional set
  have hfin := hB.add hX0
  rw [add_zero] at hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfin
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact idlaProb_le_of_subset_union_env_fp hS ε (hsub ε hε)

end MatedCRT
