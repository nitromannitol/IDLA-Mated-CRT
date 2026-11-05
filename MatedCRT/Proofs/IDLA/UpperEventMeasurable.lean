import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellDomainMeasurable
import MatedCRT.Proofs.IDLA.EnvironmentalClusterEvents

/-! Measurable distance from a point to a random open set. -/

namespace MatedCRT

open Set MeasureTheory Metric Topology Filter
open scoped ENNReal
open Classical

/-- An open set has the same distance function as its trace on the fixed dense sequence. -/
theorem infEDist_open_eq_iInf_densePoint (U : Set ℂ) (hU : IsOpen U) (z : ℂ) :
    infEDist z U = ⨅ j : ℕ, if densePoint j ∈ U then edist z (densePoint j) else ⊤ := by
  classical
  let D : Set ℂ := U ∩ range densePoint
  have hcl : U ⊆ closure D := Dense.open_subset_closure_inter denseRange_densePoint hU
  have heq : infEDist z U = infEDist z D := by
    apply le_antisymm (infEDist_anti (inter_subset_left))
    rw [← infEDist_closure]
    exact infEDist_anti hcl
  rw [heq]
  apply le_antisymm
  · refine le_iInf fun j => ?_
    split_ifs with hj
    · exact infEDist_le_edist_of_mem ⟨hj, mem_range_self j⟩
    · exact le_top
  · rw [le_infEDist]
    rintro y ⟨hy, j, rfl⟩
    exact (iInf_le (fun j : ℕ => if densePoint j ∈ U then edist z (densePoint j) else ⊤) j).trans (by simp [hy])

/-- A random point's distance to a random open set is measurable when its dense trace is measurable. -/
theorem measurable_infEDist_open_of_trace {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → Set ℂ) (hU : ∀ ω, IsOpen (U ω))
    (htrace : ∀ j, MeasurableSet {ω | densePoint j ∈ U ω})
    (z : Ω → ℂ) (hz : Measurable z) :
    Measurable (fun ω => infEDist (z ω) (U ω)) := by
  classical
  have heq : (fun ω => infEDist (z ω) (U ω)) =
      fun ω => ⨅ j : ℕ, if densePoint j ∈ U ω then edist (z ω) (densePoint j) else ⊤ := by
    funext ω
    exact infEDist_open_eq_iInf_densePoint _ (hU ω) _
  rw [heq]
  exact Measurable.iInf fun j => Measurable.ite (htrace j) (hz.edist measurable_const) measurable_const

/-- A continuous curve's cells escape a random closed outer neighborhood in a measurable way. -/
theorem measurableSet_fillCells_not_subset_outerNbhd {Ω : Type*} [MeasurableSpace Ω]
    (ε δ : ℝ) (hε : 0 ≤ ε) (A : Set ℤ) (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (U : Ω → Set ℂ) (hU : ∀ ω, IsOpen (U ω))
    (htrace : ∀ j, MeasurableSet {ω | densePoint j ∈ U ω}) :
    MeasurableSet {ω | ¬ fillCells ε (η ω) A ⊆ outerNbhd δ (U ω)} := by
  classical
  let I (k : ℤ) : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  have hI (k : ℤ) : (I k).Nonempty := by
    apply nonempty_Icc.mpr
    have : (0 : ℝ) ≤ ε := hε
    nlinarith
  let sample (k : ℤ) : ℕ → I k := by
    let : Nonempty (I k) := (hI k).to_subtype
    exact TopologicalSpace.denseSeq (I k)
  have hdense (k : ℤ) : DenseRange (sample k) := by
    let : Nonempty (I k) := (hI k).to_subtype
    exact TopologicalSpace.denseRange_denseSeq (I k)
  have heq : {ω | ¬ fillCells ε (η ω) A ⊆ outerNbhd δ (U ω)} =
      ⋃ k : ℤ, ⋃ (_ : k ∈ A), ⋃ j : ℕ,
        {ω | ENNReal.ofReal δ < infEDist (η ω (sample k j)) (U ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, not_subset, fillCells, mem_iUnion, cell, mem_image,
      outerNbhd, mem_ofPred_eq, not_le]
    constructor
    · rintro ⟨x, ⟨k, hk, s, hs, rfl⟩, hx⟩
      let V : Set (I k) := {s | ENNReal.ofReal δ < infEDist (η ω s) (U ω)}
      have hV : IsOpen V := by
        have hclosed : IsClosed (outerNbhd δ (U ω)) := Metric.isClosed_cthickening
        convert hclosed.isOpen_compl.preimage ((η ω).continuous.comp continuous_subtype_val) using 1
        ext s
        simp [V, outerNbhd, not_le]
      have hne : V.Nonempty := ⟨⟨s, hs⟩, hx⟩
      obtain ⟨j, hj⟩ := (hdense k).exists_mem_open hV hne
      exact ⟨k, hk, j, hj⟩
    · rintro ⟨k, hk, j, hj⟩
      exact ⟨η ω (sample k j), ⟨k, hk, sample k j, (sample k j).property, rfl⟩, hj⟩
  rw [heq]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun j => ?_
  have hm : Measurable (fun ω => η ω (sample k j)) :=
    (continuous_eval_const ((sample k j : I k) : ℝ)).measurable.comp hη
  exact measurableSet_lt measurable_const (measurable_infEDist_open_of_trace U hU htrace _ hm)

/-- Open reconstruction from the dense trace, valid even for non-open input sets. -/
def openSetOfTrace (V : Set ℂ) : Set ℂ :=
  ⋃ (d : ℕ) (k : ℕ), ⋃ (_ : innerBallTest V d k), ball (densePoint d) (1 / ((k : ℝ) + 1))

theorem isOpen_openSetOfTrace (V : Set ℂ) : IsOpen (openSetOfTrace V) := by
  unfold openSetOfTrace
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem openSetOfTrace_eq {V : Set ℂ} (hV : IsOpen V) (hreg : interior (closure V) = V) :
    openSetOfTrace V = V := by
  ext x
  simpa [openSetOfTrace] using (mem_iff_exists_innerBallTest hV hreg (x := x)).symm

theorem measurable_openSetOfTrace_mem {Ω : Type*} [MeasurableSpace Ω]
    (V : Ω → Set ℂ) (hV : ∀ j, MeasurableSet {ω | densePoint j ∈ V ω}) (z : ℂ) :
    MeasurableSet {ω | z ∈ openSetOfTrace (V ω)} := by
  apply measurableSet_setOfPred.2
  simp only [openSetOfTrace, mem_iUnion, exists_prop]
  refine Measurable.exists fun d => Measurable.exists fun k => ?_
  apply Measurable.and
  · unfold innerBallTest
    exact Measurable.forall fun j => measurable_const.imp (measurableSet_setOfPred.1 (hV j))
  · exact measurable_const

/-- The fixed-cluster upper-bound event is null measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_upper_cluster_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) (ε δ : ℝ) (hε : 0 ≤ ε) (A : Set ℤ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      ¬ fillCells ε (S.η ω) A ⊆ outerNbhd δ (Λ ω t)} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess hγ hγ2 hfam h24
  obtain ⟨Y, Y₀, hIG₀, B, B', B₀, B₀', W, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let V : Ω → Set ℂ := fun ω => {z | X ω (t, z)}
  let U : Ω → Set ℂ := fun ω => openSetOfTrace (V ω)
  have hV (j : ℕ) : MeasurableSet {ω | densePoint j ∈ V ω} :=
    measurableSet_setOfPred.2 (hXm (t, densePoint j))
  have hE : MeasurableSet {ω | ¬ fillCells ε (η' ω) A ⊆ outerNbhd δ (U ω)} :=
    measurableSet_fillCells_not_subset_outerNbhd ε δ hε A η' hc.measurable_curves.2.1 U
      (fun ω => isOpen_openSetOfTrace (V ω)) (fun j => measurable_openSetOfTrace_mem V hV _)
  have hF := measurableSet_exitTest hXm t ρ
  refine (hF.inter hE).nullMeasurableSet.congr ?_
  filter_upwards [hΛ, hX, hbridge] with ω hΛω hXω hηω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  obtain ⟨hcl, htT⟩ := lt_clusterExitTime_iff_of_familyProcess hΛω hT hΛ' hstop hXω hρ hρ1 ht
  have heq : EqOn Λ' (Λ ω) (Ioo 0 T) := by
    have h := (hΛω.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h
  have hU : t < clusterExitTime (Λ ω) ρ → U ω = Λ ω t := by
    intro hx
    have ht' := htT hx
    have htrace : V ω = Λ ω t := by
      ext z
      change X ω (t, z) ↔ z ∈ Λ ω t
      rw [hXω t z, heq ht']
      exact and_iff_right ht'
    have hreg := hΛω.2.1.isRegularOpen t ht
    change openSetOfTrace (V ω) = Λ ω t
    rw [htrace]
    apply openSetOfTrace_eq
    · rw [← hreg]; exact isOpen_interior
    · exact hreg
  apply propext
  change ((∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3) ∧ _) ↔ _
  rw [← hcl]
  constructor <;> rintro ⟨hx, hy⟩ <;> refine ⟨hx, ?_⟩
  · simpa [hU hx, hηω.1] using hy
  · simpa [hU hx, hηω.1] using hy

/-- The sectionwise form of Proposition 6.1. -/
def IDLAUpperBoundSectionwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    Tendsto (fun ε => S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
      ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)})
      (𝓝[>] 0) (𝓝 0)

/-- Proposition 6.1 transfers from sectionwise probabilities to the joint outer law. -/
theorem joint_iDLAUpperBound_of_sectionwise (𝒮 : SpaceFillingSLEModel)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hupper : IDLAUpperBoundSectionwiseStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  apply (hupper γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact hS.idlaProb_eq_joint_environmentCluster ε
    (fun ω A => t < clusterExitTime (Λ ω) ρ ∧ ¬ fillCells ε (S.η ω) A ⊆ outerNbhd δ (Λ ω t))
    (fun A _ => hS.nullMeasurableSet_upper_cluster_event hγ hγ2 hfam h24 hρ hρ1 hΛ ht ε δ hε.le A) _

end MatedCRT
