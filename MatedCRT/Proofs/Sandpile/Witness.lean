import MatedCRT.Proofs.Sandpile.Comparison

/-! Finite-support stabilizing witnesses from the discrete obstacle problem. -/

namespace MatedCRT.Sandpile

open Set Finset Classical

variable {m : ℤ → ℤ → ℕ} {M : ℝ} {V : Set ℤ} {φ : ℤ → ℝ}

/-- If the obstacle cluster is contained in the graph interior of its domain,
the stopped obstacle odometer is a finite-support global stabilizer. -/
theorem obstacle_odometer_admissible_of_interior
    (hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ ((mdeg m 0 : ℝ)⁻¹ * M))
    (hint : discreteCluster (vClosure m V)
      (discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ) φ ⊆
        vInterior m V) :
    (fun a => if a ∈ vClosure m V then
      discreteLeastSupersolution m V (vClosure m V) (fun b => (mdeg m b : ℝ)⁻¹) φ a - φ a
      else 0) ∈ admissible m M ∧
    (Function.support (fun a => if a ∈ vClosure m V then
      discreteLeastSupersolution m V (vClosure m V) (fun b => (mdeg m b : ℝ)⁻¹) φ a - φ a
      else 0)).Finite := by
  classical
  let r : ℤ → ℝ := fun a => (mdeg m a : ℝ)⁻¹
  let w := discreteLeastSupersolution m V (vClosure m V) r φ
  let v : ℤ → ℝ := fun a => if a ∈ vClosure m V then w a - φ a else 0
  have hvnonneg : ∀ a, 0 ≤ v a := by
    intro a
    dsimp [v]
    split_ifs with ha
    · exact sub_nonneg.2 (hS.obstacle_le_w a ha)
    · exact le_rfl
  have hsupport : Function.support v ⊆ vInterior m V := by
    intro a ha
    by_cases haW : a ∈ vClosure m V
    · apply hint
      refine ⟨haW, ?_⟩
      have hpos : 0 < v a := lt_of_le_of_ne (hvnonneg a) (Ne.symm ha)
      simp only [v, ite_eq_left haW] at hpos
      linarith
    · simp [Function.mem_support, v, haW] at ha
  have hvlocal : ∀ a ∈ V, mLaplacian m v a + (mdeg m 0 : ℝ)⁻¹ * M * diracZero a ≤ r a := by
    intro a ha
    have haW : a ∈ vClosure m V := Or.inl ha
    have hsum : lapSum hS.hlf v a = lapSum hS.hlf (fun b => w b - φ b) a := by
      unfold lapSum
      apply Finset.sum_congr rfl
      intro b hb
      have hbW := mem_vClosure_of_mem_nbrs hS.hlf ha hb
      simp [v, haW, hbW]
    have hΔ : mLaplacian m v a = mLaplacian m w a - mLaplacian m φ a := by
      simp only [mLaplacian_eq_div hS.hlf]
      rw [hsum, lapSum_sub, sub_div]
    rw [hΔ, hS.obstacle_laplacian a ha]
    have hbound := hS.lap_w_le a ha
    dsimp [w, r] at *
    by_cases ha0 : a = 0 <;> simp [diracZero, ha0] at * <;> linarith
  have hvadm : v ∈ admissible m M := by
    refine ⟨hvnonneg, fun a => ?_⟩
    by_cases ha : a ∈ V
    · exact hvlocal a ha
    · have ha0 : a ≠ 0 := fun e => ha (e ▸ hS.origin_mem)
      have hva : v a = 0 := by
        by_contra hn
        exact ha (hsupport hn).1
      have hsum : lapSum hS.hlf v a = 0 := by
        unfold lapSum
        apply Finset.sum_eq_zero
        intro b hb
        have hvb : v b = 0 := by
          by_contra hn
          have hba : m b a ≠ 0 := by rw [hS.symm]; exact (mem_nbrs hS.hlf).1 hb
          exact ha ((hsupport hn).2 a hba)
        simp [hva, hvb]
      have hlap : mLaplacian m v a = 0 := by
        rw [mLaplacian_eq_div hS.hlf, hsum, zero_div]
      simp only [hlap, diracZero, ite_eq_right ha0, mul_zero, add_zero]
      exact inv_nonneg.2 (Nat.cast_nonneg _)
  exact ⟨hvadm, hS.finite.subset fun a ha => (hsupport ha).1⟩

/-- A compactly supported obstacle odometer supplies a finite stabilizing witness. -/
theorem finite_witness_of_obstacle_interior
    (hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ ((mdeg m 0 : ℝ)⁻¹ * M))
    (hint : discreteCluster (vClosure m V)
      (discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ) φ ⊆
        vInterior m V) :
    ∃ v : ℤ → ℝ, v ∈ admissible m M ∧ (Function.support v).Finite := by
  exact ⟨_, obstacle_odometer_admissible_of_interior hS hint⟩

/-- If the stopped cluster stays in the graph interior, the stopped odometer equals the
global odometer. The hypothesis concerns the stopped cluster and therefore avoids assuming
the global containment that this comparison is meant to prove. -/
theorem obstacle_odometer_eq_of_interior
    (hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ ((mdeg m 0 : ℝ)⁻¹ * M))
    (hint : discreteCluster (vClosure m V)
      (discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ) φ ⊆
        vInterior m V) :
    (fun a => if a ∈ vClosure m V then
      discreteLeastSupersolution m V (vClosure m V) (fun b => (mdeg m b : ℝ)⁻¹) φ a - φ a
      else 0) = sandpileNormOdometer m M := by
  classical
  let r : ℤ → ℝ := fun a => (mdeg m a : ℝ)⁻¹
  let w := discreteLeastSupersolution m V (vClosure m V) r φ
  let v : ℤ → ℝ := fun a => if a ∈ vClosure m V then w a - φ a else 0
  have hv : v ∈ admissible m M := (obstacle_odometer_admissible_of_interior hS hint).1
  have hne : (admissible m M).Nonempty := ⟨v, hv⟩
  have hu := normOdometer_mem_admissible hS.hlf hne
  have hψ : (fun a => sandpileNormOdometer m M a + φ a) ∈
      obstacleAdmissible m V (vClosure m V) r φ := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [mLaplacian_add_of_locallyFinite hS.hlf, hS.obstacle_laplacian a ha]
      have hu' := hu.2 a
      by_cases ha0 : a = 0 <;> simpa [r, diracZero, ha0] using hu'
    · have := normOdometer_nonneg hne a
      linarith
  funext a
  apply le_antisymm
  · by_cases ha : a ∈ vClosure m V
    · have hcmp := IsObstacleSetting.w_le (m := m) (V := V) (𝔯 := r) (φ := φ)
        (fun a => sandpileNormOdometer m M a + φ a) hψ a ha
      simp only [ite_eq_left ha]
      linarith
    · simpa [v, ha] using normOdometer_nonneg hne a
  · exact normOdometer_le v hv a

/-- The stopped mated-CRT odometer equals the global normalized odometer when its
obstacle cluster is contained in the graph interior of the stopping domain. -/
theorem stoppedOdometer_eq_of_obstacle_interior {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (Metric.closedBall 0 ρ))
    (hint : discreteCluster (vClosure m (ballInterior ε η ρ))
      (discreteLeastSupersolution m (ballInterior ε η ρ) (vClosure m (ballInterior ε η ρ))
        (fun a => (mdeg m a : ℝ)⁻¹) (matedObstacle m ε η ρ t)) (matedObstacle m ε η ρ t) ⊆
        vInterior m (ballInterior ε η ρ)) :
    stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε) := by
  classical
  have hS' : IsObstacleSetting m (ballInterior ε η ρ) 0
      (fun a => (mdeg m a : ℝ)⁻¹) (matedObstacle m ε η ρ t)
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [IsMatedObstacleSetting, matedDeg, mul_comm] using hS
  have heq := obstacle_odometer_eq_of_interior hS' hint
  have hφ := matedObstacle_eq_zero_off_vClosure (m := m) (ε := ε) (η := η) (ρ := ρ) (t := t)
  funext a
  have heqa := congrFun heq a
  by_cases ha : a ∈ vClosure m (ballInterior ε η ρ)
  · have haW := hW ha
    have hw := dls_eq_of_mem_vClosure hS' hW hφ ha
    simp only [stoppedOdometer, haW, ↓reduceIte, matedLeastSupersolution_eq, matedDeg, hw]
    simpa only [ha, ↓reduceIte] using heqa
  · have hu0 : sandpileNormOdometer m (t / ε) a = 0 := by
      simpa only [ha, ↓reduceIte] using heqa.symm
    by_cases haW : a ∈ cellVertices ε η (Metric.closedBall 0 ρ)
    · have hw := dls_eq_zero_of_not_mem_vClosure hS' hφ haW ha
      simp only [stoppedOdometer, haW, ↓reduceIte, matedLeastSupersolution_eq, matedDeg, hw,
        hφ a haW ha, sub_self, hu0]
    · simp [stoppedOdometer, haW, hu0]

/-- The same comparison with the stopped cluster as stated in Section 7. -/
theorem stoppedOdometer_eq_of_stopped_cluster_interior {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (Metric.closedBall 0 ρ))
    (hint : matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ)) :
    stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε) := by
  have hS' : IsObstacleSetting m (ballInterior ε η ρ) 0
      (fun a => (mdeg m a : ℝ)⁻¹) (matedObstacle m ε η ρ t)
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [IsMatedObstacleSetting, matedDeg, mul_comm] using hS
  apply stoppedOdometer_eq_of_obstacle_interior hS hW
  intro a ha
  have haV : a ∈ ballInterior ε η ρ := hS'.cluster_subset ha
  have hφ := matedObstacle_eq_zero_off_vClosure (m := m) (ε := ε) (η := η) (ρ := ρ) (t := t)
  have hw := dls_eq_of_mem_vClosure hS' hW hφ ha.1
  apply hint
  refine ⟨ballInterior_subset_cellVertices_ball haV, ?_⟩
  simpa [matedLeastSupersolution_eq, matedDeg, hw] using ha.2

end MatedCRT.Sandpile
