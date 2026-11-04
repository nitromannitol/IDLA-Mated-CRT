import MatedCRT.Defs.Sandpile

/-!
# Elementary properties of the stopped odometer (Section 7, line 2941; eq:laplacian-of-uteps, lines 2967, 2970)

For every map (no hypothesis on `η`), `ε > 0` and `t > 0`:
* the obstacle `-(t ε⁻¹) g^ε_{B_ρ}(0, ·)` is nonpositive, so `0` is admissible for the obstacle problem and
  `w̃^ε_t ≥ -(t ε⁻¹) g^ε_{B_ρ}(0, ·)` on `V^ε(cl(B_ρ))`;
* the stopped odometer `u^ε_t` is nonnegative (`stoppedOdometer_nonneg`) and vanishes on `V^ε(B_ρ) \ Λ^ε_t`
  (`stoppedOdometer_eq_zero_of_not_mem_cluster`).
-/

namespace MatedCRT.Sec7

open Set Metric

theorem cellVertices_mono {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' := by
  rintro k ⟨z, hz, hzD⟩
  exact ⟨z, hz, h hzD⟩

theorem greenKernel_nonneg (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b :=
  div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

theorem mLaplacian_const_zero {α : Type*} (m : α → α → ℕ) (a : α) : mLaplacian m (fun _ => 0) a = 0 := by
  simp [mLaplacian]

/-- If the obstacle problem has an admissible function, its least supersolution lies above the obstacle on `W`. -/
theorem le_discreteLeastSupersolution {α : Type*} {m : α → α → ℕ} {V W : Set α} {𝔯 φ : α → ℝ}
    (hne : ∃ u : α → ℝ, (∀ b ∈ V, mLaplacian m u b ≤ 𝔯 b) ∧ ∀ b ∈ W, φ b ≤ u b) {a : α} (ha : a ∈ W) :
    φ a ≤ discreteLeastSupersolution m V W 𝔯 φ a := by
  obtain ⟨u, hu⟩ := hne
  refine le_csInf ⟨u a, u, hu, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hv.2 a ha

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

theorem matedObstacle_nonpos (hε : 0 < ε) (ht : 0 < t) (a : ℤ) : matedObstacle m ε η ρ t a ≤ 0 := by
  unfold matedObstacle
  rw [neg_mul]
  exact neg_nonpos.2 (mul_nonneg (div_nonneg ht.le hε.le) (greenKernel_nonneg _ _ _ _))

theorem matedObstacle_le_matedLeastSupersolution (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (ha : a ∈ cellVertices ε η (closedBall 0 ρ)) :
    matedObstacle m ε η ρ t a ≤ matedLeastSupersolution m ε η ρ t a := by
  refine le_discreteLeastSupersolution ⟨fun _ => 0, fun b _ => ?_, fun b _ => matedObstacle_nonpos hε ht b⟩ ha
  rw [mLaplacian_const_zero]
  exact inv_nonneg.2 (Nat.cast_nonneg _)

/-- `u^ε_t ≥ 0` (eq:laplacian-of-uteps, line 2967). -/
theorem stoppedOdometer_nonneg (hε : 0 < ε) (ht : 0 < t) (a : ℤ) : 0 ≤ stoppedOdometer m ε η ρ t a := by
  unfold stoppedOdometer
  split_ifs with h
  · linarith [matedObstacle_le_matedLeastSupersolution (m := m) (η := η) (ρ := ρ) hε ht h]
  · exact le_rfl

/-- `u^ε_t = 0` on `V^ε(B_ρ) \ Λ^ε_t` (eq:laplacian-of-uteps, line 2970). -/
theorem stoppedOdometer_eq_zero_of_not_mem_cluster (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (ha : a ∈ cellVertices ε η (ball 0 ρ)) (haΛ : a ∉ matedDiscreteCluster m ε η ρ t) :
    stoppedOdometer m ε η ρ t a = 0 := by
  have haW : a ∈ cellVertices ε η (closedBall 0 ρ) := cellVertices_mono ball_subset_closedBall ha
  have hle : ¬ matedObstacle m ε η ρ t a < matedLeastSupersolution m ε η ρ t a := fun h => haΛ ⟨ha, h⟩
  have hge := matedObstacle_le_matedLeastSupersolution (m := m) (η := η) (ρ := ρ) hε ht haW
  unfold stoppedOdometer
  split_ifs
  linarith [not_lt.1 hle]

/-- Off `V = V^ε(B_ρ) \ V^ε(∂B_ρ)` the obstacle constrains nothing: lowering an admissible function to the obstacle at
`a ∉ V` keeps it admissible, so `w̃^ε_t(a) ≤ -(t ε⁻¹) g^ε_{B_ρ}(0, a)` there. -/
theorem matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (haW : a ∈ cellVertices ε η (closedBall 0 ρ)) (haV : a ∉ ballInterior ε η ρ) :
    matedLeastSupersolution m ε η ρ t a ≤ matedObstacle m ε η ρ t a := by
  unfold matedLeastSupersolution discreteLeastSupersolution
  refine csInf_le ⟨matedObstacle m ε η ρ t a, ?_⟩
    ⟨Function.update (fun _ => 0) a (matedObstacle m ε η ρ t a), ⟨?_, ?_⟩, by simp⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hv.2 a haW
  · intro b hb
    have hba : b ≠ a := fun h => haV (h ▸ hb)
    have hlap : mLaplacian m (Function.update (fun _ => 0) a (matedObstacle m ε η ρ t a)) b =
        ((mdeg m b : ℕ) : ℝ)⁻¹ * ((m b a : ℝ) * matedObstacle m ε η ρ t a) := by
      unfold mLaplacian
      congr 1
      rw [finsum_eq_single _ a]
      · simp [hba]
      · intro c hc
        simp [hc, hba]
    rw [hlap]
    have h1 := matedObstacle_nonpos (m := m) (η := η) (ρ := ρ) hε ht a
    have h2 : 0 ≤ ((mdeg m b : ℕ) : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    have h3 : (m b a : ℝ) * matedObstacle m ε η ρ t a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h1
    exact (mul_nonpos_of_nonneg_of_nonpos h2 h3).trans (inv_nonneg.2 (Nat.cast_nonneg _))
  · intro b _
    by_cases hba : b = a
    · subst hba
      simp
    · rw [Function.update_of_ne hba]
      exact matedObstacle_nonpos hε ht b

/-- The support of `u^ε_t` is contained in `Λ^ε_t`. -/
theorem mem_matedDiscreteCluster_of_stoppedOdometer_pos (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (h : 0 < stoppedOdometer m ε η ρ t a) : a ∈ matedDiscreteCluster m ε η ρ t := by
  by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
  swap
  · simp [stoppedOdometer, haW] at h
  simp only [stoppedOdometer, haW, ↓reduceIte] at h
  by_cases haV : a ∈ ballInterior ε η ρ
  · exact ⟨(show a ∈ cellVertices ε η (ball 0 ρ) \ cellVertices ε η (frontier (ball 0 ρ)) from haV).1,
      by linarith⟩
  · have := matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior (m := m) hε ht haW haV
    linarith

end MatedCRT.Sec7
