import MatedCRT.Proofs.Sandpile.Connectivity
import MatedCRT.Proofs.SecA.DiscreteObstacle
import MatedCRT.Proofs.Sec4.GreenLaplacian

/-! Least-action comparison for a sandpile stopped in a vertex set. -/

namespace MatedCRT.Sandpile

open Set

variable {m : ℤ → ℤ → ℕ} {M : ℝ}

/-- A nonnegative local stabilizer below the global odometer is the global
odometer if the global cluster is contained in the local domain. This is the
least-action step in the stopped-odometer comparison. -/
theorem eq_of_local_stabilizer (hlf : IsLocallyFiniteMult m)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) {V : Set ℤ}
    (hcluster : sandpileCluster m M ⊆ V) (v : ℤ → ℝ)
    (hvnonneg : ∀ a, 0 ≤ v a) (hvle : ∀ a, v a ≤ sandpileNormOdometer m M a)
    (hvlocal : ∀ a ∈ V, mLaplacian m v a + (mdeg m 0 : ℝ)⁻¹ * M * diracZero a ≤
      (mdeg m a : ℝ)⁻¹) :
    v = sandpileNormOdometer m M := by
  have hu := normOdometer_mem_admissible hlf hne
  have hv : v ∈ admissible m M := by
    refine ⟨hvnonneg, fun a => ?_⟩
    by_cases haV : a ∈ V
    · exact hvlocal a haV
    · have hu0 : sandpileNormOdometer m M a = 0 := by
        apply le_antisymm _ (normOdometer_nonneg hne a)
        by_contra hn
        have hpos : 0 < sandpileNormOdometer m M a := lt_of_not_ge hn
        have haD : a ∈ sandpileCluster m M := by
          change 0 < sandpileFinal m M a
          rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg hne hpos]
          norm_num
        exact haV (hcluster haD)
      have hv0 : v a = 0 := le_antisymm (by simpa [hu0] using hvle a) (hvnonneg a)
      have hsum : lapSum hlf v a ≤ lapSum hlf (sandpileNormOdometer m M) a := by
        apply lapSum_le_lapSum hlf (fun b _ => hvle b)
        simp [hu0, hv0]
      have hlap : mLaplacian m v a ≤ mLaplacian m (sandpileNormOdometer m M) a := by
        simp only [mLaplacian_eq_div hlf]
        exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
      have := hu.2 a
      linarith
  funext a
  exact le_antisymm (hvle a) (normOdometer_le v hv a)

open Classical in
/-- Obstacle formulation of the stopped odometer on a finite connected
domain.  If the global cluster is contained in the domain, it agrees with the
global normalized odometer. -/
theorem obstacle_odometer_eq (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) {V : Set ℤ} {φ : ℤ → ℝ}
    (hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ ((mdeg m 0 : ℝ)⁻¹ * M))
    (hcluster : sandpileCluster m M ⊆ V) :
    (fun a => if a ∈ vClosure m V then
      discreteLeastSupersolution m V (vClosure m V) (fun b => (mdeg m b : ℝ)⁻¹) φ a - φ a
      else 0) = sandpileNormOdometer m M := by
  classical
  let u := sandpileNormOdometer m M
  let r : ℤ → ℝ := fun a => (mdeg m a : ℝ)⁻¹
  let w := discreteLeastSupersolution m V (vClosure m V) r φ
  let v : ℤ → ℝ := fun a => if a ∈ vClosure m V then w a - φ a else 0
  have hu := normOdometer_mem_admissible hS.hlf hne
  have hψ : (fun a => u a + φ a) ∈ obstacleAdmissible m V (vClosure m V) r φ := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [mLaplacian_add_of_locallyFinite hS.hlf, hS.obstacle_laplacian a ha]
      have hu' := hu.2 a
      by_cases ha0 : a = 0 <;> simpa [u, r, diracZero, ha0] using hu'
    · have := normOdometer_nonneg hne a
      linarith
  have hvnonneg : ∀ a, 0 ≤ v a := by
    intro a
    dsimp [v]
    split_ifs with ha
    · exact sub_nonneg.2 (hS.obstacle_le_w a ha)
    · exact le_rfl
  have hvle : ∀ a, v a ≤ u a := by
    intro a
    by_cases ha : a ∈ vClosure m V
    · have hcmp := IsObstacleSetting.w_le (m := m) (V := V) (𝔯 := r) (φ := φ)
        (fun a => u a + φ a) hψ a ha
      simp only [v, ite_eq_left ha]
      linarith
    · simpa [v, ha] using normOdometer_nonneg hne a
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
  exact eq_of_local_stabilizer hS.hlf hS.loopless hdeg hne hcluster v hvnonneg hvle hvlocal

/-- The Section 7 stopped odometer agrees with the global normalized
odometer when the global cluster stays inside the stopping domain. -/
theorem stoppedOdometer_eq_normOdometer {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m (t / ε)).Nonempty)
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (Metric.closedBall 0 ρ))
    (hcluster : sandpileCluster m (t / ε) ⊆ ballInterior ε η ρ) :
    stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε) := by
  classical
  have hS' : IsObstacleSetting m (ballInterior ε η ρ) 0
      (fun a => (mdeg m a : ℝ)⁻¹) (matedObstacle m ε η ρ t)
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [IsMatedObstacleSetting, matedDeg, mul_comm] using hS
  have heq := obstacle_odometer_eq hdeg hne hS' hcluster
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

end MatedCRT.Sandpile
