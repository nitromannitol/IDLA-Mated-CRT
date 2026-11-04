import MatedCRT.Proofs.Sandpile.Geometry

/-! Global consequences of finite stabilization for the divisible sandpile. -/

namespace MatedCRT.Sandpile

open Set Classical

variable {m : ℤ → ℤ → ℕ} {M : ℝ}

/-- The normalized Laplacian plus the point source is final mass divided
by the degree, as in equation `laplacian-of-uteps`. -/
theorem normalized_final_identity (hdeg0 : 0 < mdeg m 0) (a : ℤ) :
    mLaplacian m (sandpileNormOdometer m M) a +
      (mdeg m 0 : ℝ)⁻¹ * M * diracZero a =
    (mdeg m a : ℝ)⁻¹ * sandpileFinal m M a := by
  by_cases ha : a = 0
  · subst a
    have hd : (mdeg m 0 : ℝ) ≠ 0 := by exact_mod_cast hdeg0.ne'
    simp only [sandpileFinal, diracZero, ite_true, mul_one]
    field_simp
    ring
  · by_cases hd : mdeg m a = 0
    · simp [sandpileFinal, diracZero, ha, mLaplacian, hd]
    · have hd' : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hd
      simp [sandpileFinal, diracZero, ha, hd']

theorem normalized_final_nonneg (hlf : IsLocallyFiniteMult m)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) (hM : 0 ≤ M) (a : ℤ) :
    0 ≤ mLaplacian m (sandpileNormOdometer m M) a +
      (mdeg m 0 : ℝ)⁻¹ * M * diracZero a := by
  rw [normalized_final_identity (hdeg 0)]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (final_nonneg hlf hloop hdeg hne hM a)

theorem normalized_laplacian_eq_of_odometer_pos (hlf : IsLocallyFiniteMult m)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) {a : ℤ}
    (ha : 0 < sandpileNormOdometer m M a) :
    mLaplacian m (sandpileNormOdometer m M) a +
      (mdeg m 0 : ℝ)⁻¹ * M * diracZero a = (mdeg m a : ℝ)⁻¹ := by
  rw [normalized_final_identity (hdeg 0), final_eq_one_of_normOdometer_pos hlf hloop hdeg hne ha]
  simp

/-- Least action and the finite-support properties hold on an infinite
connected locally finite graph. -/
theorem global_stabilization (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ) :
    sandpileNormOdometer m M ∈ admissible m M ∧
    (Function.support (sandpileNormOdometer m M)).Finite ∧
    (Function.support (sandpileOdometer m M)).Finite ∧
    (Function.support (sandpileFinal m M)).Finite ∧
    (∑ᶠ a, sandpileFinal m M a) = M := by
  obtain ⟨w, hw, hfin⟩ := exists_finite_stabilizer hlf hsymm hloop hdeg hconn M
  have hne : (admissible m M).Nonempty := ⟨w, hw⟩
  have hufin := normOdometer_finiteSupport hne w hw hfin
  refine ⟨normOdometer_mem_admissible hlf hne, hufin, ?_,
    final_finiteSupport hlf hsymm w hw hfin, finsum_final_eq_mass hlf hsymm w hw hfin⟩
  apply hufin.subset
  intro a ha
  simp only [Function.mem_support, sandpileOdometer] at ha ⊢
  exact fun hz => ha (by simp [hz])

theorem global_odometer_support_card (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ) (hM : 0 ≤ M) :
    ((Function.support (sandpileNormOdometer m M)).ncard : ℝ) ≤ M := by
  obtain ⟨w, hw, hfin⟩ := exists_finite_stabilizer hlf hsymm hloop hdeg hconn M
  exact odometer_support_ncard_le_mass hlf hsymm hloop hdeg hM w hw hfin

theorem global_cluster_connected (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ) (hM : 1 < M) :
    IsVConnected m (sandpileCluster m M) := by
  obtain ⟨w, hw, _⟩ := exists_finite_stabilizer hlf hsymm hloop hdeg hconn M
  exact cluster_connected hlf hsymm hloop hdeg ⟨w, hw⟩ hM

theorem global_cluster_mono (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ)
    {M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) : sandpileCluster m M₁ ⊆ sandpileCluster m M₂ := by
  obtain ⟨w, hw, _⟩ := exists_finite_stabilizer hlf hsymm hloop hdeg hconn M₂
  exact cluster_mono hlf hloop hdeg hM ⟨w, hw⟩

theorem global_normalized_laplacian_bounds (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ) (hM : 0 ≤ M) (a : ℤ) :
    0 ≤ mLaplacian m (sandpileNormOdometer m M) a +
      (mdeg m 0 : ℝ)⁻¹ * M * diracZero a ∧
    mLaplacian m (sandpileNormOdometer m M) a +
      (mdeg m 0 : ℝ)⁻¹ * M * diracZero a ≤ (mdeg m a : ℝ)⁻¹ := by
  obtain ⟨w, hw, _⟩ := exists_finite_stabilizer hlf hsymm hloop hdeg hconn M
  exact ⟨normalized_final_nonneg hlf hloop hdeg ⟨w, hw⟩ hM a,
    (normOdometer_mem_admissible hlf ⟨w, hw⟩).2 a⟩

theorem global_stoppedOdometer_eq {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ)
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (Metric.closedBall 0 ρ))
    (hcluster : sandpileCluster m (t / ε) ⊆ ballInterior ε η ρ) :
    stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε) := by
  have hS' : IsObstacleSetting m (ballInterior ε η ρ) 0
      (fun a => (mdeg m a : ℝ)⁻¹) (matedObstacle m ε η ρ t)
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [IsMatedObstacleSetting, matedDeg, mul_comm] using hS
  obtain ⟨w, hw, _⟩ := exists_finite_stabilizer hS'.hlf hS'.symm hS'.loopless hdeg hconn (t / ε)
  exact stoppedOdometer_eq_normOdometer hdeg ⟨w, hw⟩ hS hW hcluster

/-- A partially filled origin disproves the proposed cardinality bound for
the full cluster, even though the positive odometer support obeys it. -/
theorem cluster_card_bound_fails (m : ℤ → ℤ → ℕ) :
    ¬ ((sandpileCluster m (1 / 2)).ncard : ℝ) ≤ (1 / 2 : ℝ) := by
  rw [cluster_of_mass_le_one (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)]
  norm_num

end MatedCRT.Sandpile
