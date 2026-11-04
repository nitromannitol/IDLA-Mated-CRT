import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RandomSetRegularization
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem

/-! # Measurability of bounded obstacle clusters -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter TopologicalSpace

/-- Lemma 2.7 makes point membership in the continuum obstacle cluster
null measurable for each ball strictly inside the unit disk. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_mem_localCluster
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {r t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ht : 0 < t) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ cluster (S.μ ω) r 0 t} S.P := by
  change NullMeasurableSet {ω | x ∈ ball (0 : ℂ) r ∧
    (x = 0 ∨ -t * greenFunction (ball 0 r) 0 x < leastSupersolution (S.μ ω) r 0 t x)} S.P
  by_cases hx : x ∈ ball (0 : ℂ) r
  · by_cases hx0 : x = 0
    · subst x
      simp [hr]
    · have hv := hS.aemeasurable_leastSupersolution_inside_unit hγ hγ2 h27
        hr hr1 ht (mem_ball_self hr) (ball_subset_closedBall hx)
      have hm := nullMeasurableSet_lt
        (aemeasurable_const : AEMeasurable (fun _ : Ω =>
          -t * greenFunction (ball 0 r) 0 x) S.P) hv
      simpa only [hx, hx0, true_and, false_or] using hm
  · simp only [hx, false_and, ofPred_false, nullMeasurableSet_empty]

/-- The regularized bounded obstacle cluster has null-measurable point
membership, including possible contact points in its interior. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_mem_regularizedLocalCluster
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {r t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ht : 0 < t) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ interior (closure (cluster (S.μ ω) r 0 t))} S.P := by
  obtain ⟨C₀, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let C : Set ℂ := C₀ ∪ {0}
  have hC : C.Countable := hcount.union (countable_singleton 0)
  have hd : Dense C := hdense.mono subset_union_left
  have hzero : (0 : ℂ) ∈ C := Or.inr rfl
  apply nullMeasurableSet_mem_interior_closure_of_countable S.P
    (fun ω => cluster (S.μ ω) r 0 t) hC hd
  · intro z _
    exact hS.nullMeasurableSet_mem_localCluster hγ hγ2 h27 hr hr1 ht z
  · filter_upwards [hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hr1, hS.isLQGMeasure] with
      ω ⟨βm, βp, hV⟩ hμ
    have hc := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ.isLocallyFiniteMeasure hr hV
      (mem_ball_self hr) ht).2.1
    exact cluster_subset_closure_inter_of_continuous (S.μ ω) hr t hd hzero
      (hc.mono ball_subset_closedBall)

/-- Containment of the regularized local cluster in a fixed ball is null
measurable, by testing a countable dense set of points. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_regularizedLocalCluster_subset_ball
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {r t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ht : 0 < t) (s : ℝ) :
    NullMeasurableSet {ω | interior (closure (cluster (S.μ ω) r 0 t)) ⊆ ball 0 s} S.P := by
  classical
  obtain ⟨C, hC, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable C := hC.to_subtype
  have hmem : ∀ z : C, NullMeasurableSet
      {ω | (z : ℂ) ∈ interior (closure (cluster (S.μ ω) r 0 t)) →
        (z : ℂ) ∈ closedBall 0 s} S.P := by
    intro z
    by_cases hz : (z : ℂ) ∈ closedBall 0 s
    · simp [hz]
    · convert (hS.nullMeasurableSet_mem_regularizedLocalCluster hγ hγ2 h27 hr hr1 ht z).compl using 1
      ext ω
      simp [hz]
  have h := NullMeasurableSet.iInter hmem
  apply h.congr
  filter_upwards [] with ω
  apply propext
  simpa using (isOpen_subset_ball_iff_dense (D := interior (closure (cluster (S.μ ω) r 0 t)))
    isOpen_interior hdense s).symm

end MatedCRT
