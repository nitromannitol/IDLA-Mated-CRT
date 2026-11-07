import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.CorrectedClusterRegular
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.SmallMesh

/-! The corrected cluster identity under stopped/global odometer agreement. -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- The stopped odometer support is the obstacle cluster on a regular map;
the source component suffices even if the full stopping domain is disconnected. -/
theorem matedDiscreteCluster_eq_stopped_support_of_regular
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hd : IsRegularMatedMap m ε η) (ht : 0 < t)
    (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) :
    matedDiscreteCluster m ε η ρ t = Function.support (stoppedOdometer m ε η ρ t) := by
  classical
  let V := vComponent m (ballInterior ε η ρ) 0
  let φ := matedObstacle m ε η ρ t
  let w := discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ
  have hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [V, φ, matedDeg, mul_comm] using hd.isObstacleSetting ht h0
  have hA : matedDiscreteCluster m ε η ρ t = discreteCluster (vClosure m V) w φ := by
    simpa [V, w, φ, matedDeg] using hd.cluster_eq ht h0
  have hW : vClosure m V ⊆ cellVertices ε η (closedBall 0 ρ) :=
    (vClosure_vComponent_subset h0).trans (vClosure_ballInterior_subset hd.continuous hd.cells_meet)
  rw [hA]
  ext a
  by_cases ha : a ∈ vClosure m V
  · have haW := hW ha
    have hw := hd.w_eq_gluedW ht h0 haW
    rw [gluedW_of_mem ha] at hw
    have hle := hS.obstacle_le_w a ha
    simp only [discreteCluster, mem_ofPred_eq, Function.mem_support, stoppedOdometer,
      haW, ↓reduceIte, ha, true_and]
    change φ a < w a ↔ matedLeastSupersolution m ε η ρ t a - φ a ≠ 0
    rw [hw]
    change φ a < w a ↔ w a - φ a ≠ 0
    change φ a ≤ w a at hle
    constructor
    · intro h; exact sub_ne_zero.mpr (ne_of_gt h)
    · intro h; exact lt_of_le_of_ne hle (Ne.symm (sub_ne_zero.mp h))
  · have hz : stoppedOdometer m ε η ρ t a = 0 := by
      by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
      · have hw := hd.w_eq_gluedW ht h0 haW
        rw [gluedW_of_not_mem ha] at hw
        have hφ := hd.obstacle_eq_zero_off ht h0 ha
        simp [stoppedOdometer, haW, hw, hφ]
      · simp [stoppedOdometer, haW]
    simp [discreteCluster, ha, Function.mem_support, hz]

/-- Corrected equation `eq:cluster-and-lambdat`, paper lines 1961–1968,
from agreement of the stopped and global odometers. -/
theorem sandpileCluster_eq_matedDiscreteCluster_of_odometer_consistency
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hd : IsRegularMatedMap m ε η) (hεt : ε < t)
    (h0 : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hcons : stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε)) :
    sandpileCluster m (t / ε) = vClosure m (matedDiscreteCluster m ε η ρ t) := by
  have ht : 0 < t := hd.pos.trans hεt
  have hdeg : ∀ a, 0 < mdeg m a := fun a => mdeg_pos_of_ne_zero hd.locallyFinite (hd.succ a)
  have hconn := Sandpile.connected_of_consecutive_edges hd.symm hd.succ
  obtain ⟨v, hv, _⟩ := Sandpile.exists_finite_stabilizer hd.locallyFinite hd.symm hd.loopless hdeg hconn (t / ε)
  apply sandpileCluster_eq_matedDiscreteCluster_closure_of_consistency hd.locallyFinite hd.symm
    hd.loopless hdeg ⟨v, hv⟩ hd.pos hεt
  rw [matedDiscreteCluster_eq_stopped_support_of_regular hd ht h0, hcons]

/-- Almost surely, the corrected identity holds at all sufficiently small
meshes and all times above the mesh, whenever the two odometers agree. -/
theorem ae_small_mesh_cluster_identity_of_odometer_consistency
    (𝒮 : SpaceFillingSLEModel)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < δ → ε < t →
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t =
        sandpileNormOdometer (S.mult ε ω) (t / ε) →
      sandpileCluster (S.mult ε ω) (t / ε) = vClosure (S.mult ε ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) := by
  filter_upwards [hS.isAreaParametrized,
    ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ hγ2 hS] with ω hη hreg
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_mesh_zero_mem_ballInterior hη.1.continuousAt hη.2.1 hρ
  exact ⟨δ, hδ, fun ε t hε hεδ hεt hcons =>
    sandpileCluster_eq_matedDiscreteCluster_of_odometer_consistency
      (hreg ε hε) hεt (hsmall ε hε hεδ) hcons⟩

end MatedCRT

#print axioms MatedCRT.sandpileCluster_eq_matedDiscreteCluster_of_odometer_consistency
#print axioms MatedCRT.ae_small_mesh_cluster_identity_of_odometer_consistency
