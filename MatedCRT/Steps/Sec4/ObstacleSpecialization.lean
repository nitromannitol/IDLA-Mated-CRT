import MatedCRT.Draft.Section4
import MatedCRT.Proofs.SecA.Statements
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Steps.Infra.MatingOfTrees

/-!
# Section 4: Lemmas 4.3-4.5 as special cases of Appendix A (lines 1672-1712, 3398-3411)

The discrete obstacle problem of Section 4 (eq:discrete-least-supersolution, line 1573) is the one of Appendix A
(eq:discrete-least-supersolution-general, line 3381) under the map of lines 3400-3411:
`G → 𝒢^ε`, `V → V^ε(B_ρ) \ V^ε(∂B_ρ)` (`ballInterior`), `𝔯 → (deg^ε)⁻¹`, `φ → -(t ε⁻¹) g^ε_{B_ρ}(0, ·)`
(`matedObstacle`), `𝔱 → ε⁻¹ t deg^ε(0)⁻¹`, `𝔮 → -q^ε_{B_ρ}`.

Two differences with the printed reduction are handled here.
* The domain of `w̃^ε_t` is `V^ε(cl B_ρ)`, which contains `cl(V)` (cells of `V` lie in `B_ρ`, adjacent cells meet) but may
  be larger; on `V^ε(cl B_ρ) \ cl(V)` the obstacle vanishes and `w̃^ε_t = 0`, and `w̃^ε_t` agrees with the Appendix A
  solution on `cl(V)` (`dls_eq_of_mem_vClosure`); the clusters agree (`discreteCluster_eq`).
* The origin need not lie in `V` (ESCALATIONS E-c1-1): then the obstacle is `0`, `w̃^ε_t = 0` on `V^ε(cl B_ρ)` and
  `Λ^ε_t = ∅`. The claim `0 ∈ Λ^ε_t` of Lemma 4.4 and the mass identity of Lemma 4.5 fail in that case; their corrected
  forms (hypothesis `0 ∈ V`) are `DiscreteLaplacianBoundCorrectedStmt` and `DiscreteConservationOfMassCorrectedStmt`.

## Steps
* `MatedObstacleSettingStep`: almost surely, for all `t, ε > 0` with `0 ∈ V`, the Section 4 data satisfy the
  hypotheses `IsObstacleSetting` of Appendix A.
* `NormExitTimeLaplacianStep` (eq:discrete-normalized-exit-laplacian, line 790; Lawler-Limic, Prop. 6.2.3):
  `Δ q_A = -deg⁻¹` on a finite `A`.
* `ConsecutiveCellsAdjacentStep`: almost surely the cells `η([a-ε,a])` and `η([a,a+ε])` share a non-trivial boundary arc.
* `GreenKernelLaplacianStep` (eq:discrete-normalized-green-laplacian, line 804; Lawler-Limic, Prop. 6.2.3) and
  `EtaProperStep` (`η(t) → ∞` as `|t| → ∞`; Miller-Sheffield, Imaginary geometry IV, Section 1.2.3): used to prove
  `MatedObstacleSettingStep` (MatedCRT/Proofs/Sec4/ObstacleSpecialization.lean).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology Classical

/-! ## Locality and linearity of the Laplacian -/

section Multigraph

variable {α : Type*} {m : α → α → ℕ}

/-- `Δu(a)` only depends on `u(a)` and the values of `u` at the neighbours of `a`. -/
theorem mLaplacian_congr_nbhd {u v : α → ℝ} {a : α} (ha : u a = v a)
    (hnb : ∀ b, m a b ≠ 0 → u b = v b) : mLaplacian m u a = mLaplacian m v a := by
  unfold mLaplacian
  congr 1
  refine finsum_congr fun b => ?_
  by_cases hb : m a b = 0
  · simp [hb]
  · rw [hnb b hb, ha]

/-- `Δ(c u) = c Δu` on a locally finite multigraph. -/
theorem mLaplacian_const_mul (c : ℝ) (u : α → ℝ) (a : α) :
    mLaplacian m (fun b => c * u b) a = c * mLaplacian m u a := by
  have hrw : ∀ b, (m a b : ℝ) * (c * u b - c * u a) = c * ((m a b : ℝ) * (u b - u a)) := fun b => by ring
  simp only [mLaplacian, hrw]
  rw [← mul_finsum]
  ring

/-- A vertex with an edge has positive degree (locally finite multigraph). -/
theorem mdeg_pos_of_ne_zero (hlf : ∀ a, {b | m a b ≠ 0}.Finite) {a b : α} (hab : m a b ≠ 0) :
    0 < mdeg m a := by
  unfold mdeg
  have hs : (Function.support fun c => m a c).Finite := hlf a
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hab) (single_le_finsum b hs fun _ => Nat.zero_le _)

theorem nbr_mem_vClosure {V : Set α} {a b : α} (ha : a ∈ V) (hab : m a b ≠ 0) : b ∈ vClosure m V := by
  by_cases hb : b ∈ V
  · exact Or.inl hb
  · exact Or.inr ⟨hb, a, ha, hab⟩

theorem mLaplacian_eq_zero_of_vClosure {V : Set α} {u : α → ℝ} (hu : ∀ b ∈ vClosure m V, u b = 0) {a : α}
    (ha : a ∈ V) : mLaplacian m u a = 0 := by
  rw [mLaplacian_congr_nbhd (v := fun _ => 0) (hu a (Or.inl ha)) fun b hb => hu b (nbr_mem_vClosure ha hb)]
  simp [mLaplacian]

end Multigraph

/-! ## The obstacle problem on a domain larger than `cl(V)` -/

section Enlarged

variable {α : Type*} {m : α → α → ℕ} {V W : Set α} {o : α} {𝔯 φ : α → ℝ} {𝔱 : ℝ}

/-- The Appendix A solution `w` on `cl(V)`, extended by `0`. -/
noncomputable def gluedW (m : α → α → ℕ) (V : Set α) (𝔯 φ : α → ℝ) : α → ℝ :=
  fun b => if b ∈ vClosure m V then discreteLeastSupersolution m V (vClosure m V) 𝔯 φ b else 0

theorem gluedW_mem (hS : IsObstacleSetting m V o 𝔯 φ 𝔱)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V → φ b = 0) : gluedW m V 𝔯 φ ∈ obstacleAdmissible m V W 𝔯 φ := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hb' : b ∈ vClosure m V := Or.inl hb
    have : mLaplacian m (gluedW m V 𝔯 φ) b =
        mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) b := by
      refine mLaplacian_congr_nbhd ?_ fun c hc => ?_
      · simp [gluedW, hb']
      · simp [gluedW, nbr_mem_vClosure hb hc]
    rw [this]
    exact hS.lap_w_le b hb
  · unfold gluedW
    split_ifs with hc
    · exact hS.obstacle_le_w b hc
    · exact (hφ b hb hc).le

/-- On `cl(V)`, the obstacle problem on `W ⊇ cl(V)` has the Appendix A solution. -/
theorem dls_eq_of_mem_vClosure (hS : IsObstacleSetting m V o 𝔯 φ 𝔱) (hW : vClosure m V ⊆ W)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V → φ b = 0) {a : α} (ha : a ∈ vClosure m V) :
    discreteLeastSupersolution m V W 𝔯 φ a = discreteLeastSupersolution m V (vClosure m V) 𝔯 φ a := by
  apply le_antisymm
  · rw [discreteLeastSupersolution_eq m V W]
    refine csInf_le ⟨φ a, ?_⟩ ⟨gluedW m V 𝔯 φ, gluedW_mem hS hφ, by simp [gluedW, ha]⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a (hW ha)
  · rw [discreteLeastSupersolution_eq m V W]
    refine le_csInf ⟨_, ⟨_, gluedW_mem hS hφ, rfl⟩⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact IsObstacleSetting.w_le u ⟨hu.1, fun b hb => hu.2 b (hW hb)⟩ a ha

/-- On `W \ cl(V)`, the solution vanishes. -/
theorem dls_eq_zero_of_not_mem_vClosure (hS : IsObstacleSetting m V o 𝔯 φ 𝔱)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V → φ b = 0) {a : α} (haW : a ∈ W) (ha : a ∉ vClosure m V) :
    discreteLeastSupersolution m V W 𝔯 φ a = 0 := by
  rw [discreteLeastSupersolution_eq m V W]
  apply le_antisymm
  · refine csInf_le ⟨φ a, ?_⟩ ⟨gluedW m V 𝔯 φ, gluedW_mem hS hφ, by simp [gluedW, ha]⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a haW
  · refine (hφ a haW ha).symm.le.trans (le_csInf ⟨_, ⟨_, gluedW_mem hS hφ, rfl⟩⟩ ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a haW

theorem mLaplacian_dls_eq (hS : IsObstacleSetting m V o 𝔯 φ 𝔱) (hW : vClosure m V ⊆ W)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V → φ b = 0) {a : α} (ha : a ∈ V) :
    mLaplacian m (discreteLeastSupersolution m V W 𝔯 φ) a =
      mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a :=
  mLaplacian_congr_nbhd (dls_eq_of_mem_vClosure hS hW hφ (Or.inl ha)) fun _ hb =>
    dls_eq_of_mem_vClosure hS hW hφ (nbr_mem_vClosure ha hb)

/-- The cluster `{a ∈ U : w(a) > φ(a)}` for `V ⊆ U ⊆ W` is the Appendix A cluster. -/
theorem discreteCluster_eq (hS : IsObstacleSetting m V o 𝔯 φ 𝔱) (hW : vClosure m V ⊆ W)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V → φ b = 0) {U : Set α} (hVU : V ⊆ U) (hUW : U ⊆ W) :
    discreteCluster U (discreteLeastSupersolution m V W 𝔯 φ) φ =
      discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ := by
  ext a
  constructor
  · rintro ⟨haU, hlt⟩
    by_cases ha : a ∈ vClosure m V
    · exact ⟨ha, by rwa [dls_eq_of_mem_vClosure hS hW hφ ha] at hlt⟩
    · rw [dls_eq_zero_of_not_mem_vClosure hS hφ (hUW haU) ha, hφ a (hUW haU) ha] at hlt
      exact absurd hlt (lt_irrefl 0)
  · rintro ⟨ha, hlt⟩
    have haV : a ∈ V := hS.cluster_subset ⟨ha, hlt⟩
    exact ⟨hVU haV, by rwa [dls_eq_of_mem_vClosure hS hW hφ ha]⟩

/-- With a vanishing obstacle and a nonnegative threshold, the solution vanishes on `W`. -/
theorem dls_eq_zero_of_obstacle_zero (h𝔯 : ∀ b ∈ V, 0 ≤ 𝔯 b) (hφ : ∀ b ∈ W, φ b = 0) {a : α} (ha : a ∈ W) :
    discreteLeastSupersolution m V W 𝔯 φ a = 0 := by
  have h0 : (fun _ => (0 : ℝ)) ∈ obstacleAdmissible m V W 𝔯 φ := by
    refine ⟨fun b hb => ?_, fun b hb => (hφ b hb).le⟩
    have : mLaplacian m (fun _ => (0 : ℝ)) b = 0 := by simp [mLaplacian]
    rw [this]
    exact h𝔯 b hb
  rw [discreteLeastSupersolution_eq]
  apply le_antisymm
  · refine csInf_le ⟨φ a, ?_⟩ ⟨_, h0, rfl⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a ha
  · refine (hφ a ha).symm.le.trans (le_csInf ⟨_, ⟨_, h0, rfl⟩⟩ ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a ha

end Enlarged

/-! ## The mated-CRT map: cells, adjacency, Green's kernel -/

section Mated

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

theorem cellMult_symm (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) : cellMult ε η j k = cellMult ε η k j := by
  unfold cellMult
  by_cases h : j = k
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Set.inter_comm]

theorem cellMult_self (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) : cellMult ε η k k = 0 := by
  simp [cellMult]

/-- Adjacent cells meet (Definition 1.2). -/
theorem cell_inter_nonempty_of_cellMult_ne_zero {j k : ℤ} (h : cellMult ε η j k ≠ 0) :
    (cell ε η j ∩ cell ε η k).Nonempty := by
  unfold cellMult at h
  split_ifs at h with hjk
  · exact absurd rfl h
  · obtain ⟨C, hC, hns⟩ := Set.nonempty_of_ncard_ne_zero h
    obtain ⟨z, hz⟩ := (Set.not_subsingleton_iff.1 hns).nonempty
    obtain ⟨x, hx, rfl⟩ := hC
    exact ⟨z, connectedComponentIn_subset _ _ hz⟩

/-- A cell of a vertex of `V^ε(B_ρ) \ V^ε(∂B_ρ)` lies in `B_ρ` (`η` continuous; intermediate value theorem). -/
theorem mem_ball_of_mem_cell (hη : Continuous η) {k : ℤ} (hk : k ∈ ballInterior ε η ρ) {z : ℂ}
    (hz : z ∈ cell ε η k) : z ∈ ball (0 : ℂ) ρ := by
  obtain ⟨⟨y, hyc, hyb⟩, hkf⟩ : (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty ∧
      ¬ (cell ε η k ∩ frontier (ball (0 : ℂ) ρ)).Nonempty := hk
  have hρ : ρ ≠ 0 := by
    rintro rfl
    simp at hyb
  rw [frontier_ball (0 : ℂ) hρ] at hkf
  by_contra hzb
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = z := hz
  obtain ⟨s', hs', rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = y := hyc
  have hcont : ContinuousOn (fun r => ‖η r‖) (uIcc s' s) := (continuous_norm.comp hη).continuousOn
  have hmem : ρ ∈ uIcc ‖η s'‖ ‖η s‖ := by
    rw [mem_ball_zero_iff] at hyb
    rw [mem_ball_zero_iff, not_lt] at hzb
    exact Set.mem_uIcc.2 (Or.inl ⟨hyb.le, hzb⟩)
  obtain ⟨r, hr, hrρ⟩ := intermediate_value_uIcc hcont hmem
  exact hkf ⟨η r, ⟨r, Set.uIcc_subset_Icc hs' hs hr, rfl⟩, mem_sphere_zero_iff_norm.2 hrρ⟩

theorem ballInterior_subset_cellVertices_ball : ballInterior ε η ρ ⊆ cellVertices ε η (ball 0 ρ) :=
  fun _ hk => hk.1

theorem cellVertices_ball_subset_closedBall : cellVertices ε η (ball 0 ρ) ⊆ cellVertices ε η (closedBall 0 ρ) :=
  fun _ ⟨z, hz, hzb⟩ => ⟨z, hz, ball_subset_closedBall hzb⟩

/-- `cl(V^ε(B_ρ) \ V^ε(∂B_ρ)) ⊆ V^ε(cl B_ρ)`, for a map `m` whose adjacent vertices have intersecting cells (for the
map of Definition 1.1: `AdjacentCellsMeetStep`, MatedCRT/Steps/Infra/MatingOfTrees.lean). -/
theorem vClosure_ballInterior_subset (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (closedBall 0 ρ) := by
  rintro b (hb | ⟨-, a, ha, hab⟩)
  · exact cellVertices_ball_subset_closedBall (ballInterior_subset_cellVertices_ball hb)
  · obtain ⟨z, hza, hzb⟩ := hcell a b hab
    exact ⟨z, hzb, ball_subset_closedBall (mem_ball_of_mem_cell hη ha hza)⟩

theorem visitsBeforeExit_eq_zero_of_not_mem {A : Set ℤ} {b : ℤ} (hb : b ∉ A) (x : ℕ → ℤ) :
    visitsBeforeExit A b x = 0 := by
  unfold visitsBeforeExit
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  apply ite_eq_right
  rintro ⟨hlt, hxn⟩
  have hn : x n ∉ A := hxn ▸ hb
  have hex : ∃ n, x n ∉ A := ⟨n, hn⟩
  have : vExitTime A x ≤ n := by
    unfold vExitTime
    rw [dite_eq_left hex]
    exact_mod_cast Nat.find_min' hex hn
  exact absurd hlt (not_lt.2 this)

/-- `g_A(a, b) = 0` for `b ∉ A` (line 760). -/
theorem greenKernel_eq_zero_of_not_mem_right (m : ℤ → ℤ → ℕ) {A : Set ℤ} (a : ℤ) {b : ℤ} (hb : b ∉ A) :
    greenKernel m A a b = 0 := by
  simp [greenKernel, greenFn, visitsBeforeExit_eq_zero_of_not_mem hb]

theorem greenKernel_nonneg (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b :=
  div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

theorem normExitTime_nonneg (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) : 0 ≤ normExitTime m A a :=
  tsum_nonneg fun _ => greenKernel_nonneg _ _ _ _

theorem matedObstacle_nonpos (ht : 0 ≤ t) (hε : 0 ≤ ε) (a : ℤ) : matedObstacle m ε η ρ t a ≤ 0 := by
  unfold matedObstacle
  rw [neg_mul]
  exact neg_nonpos.2 (mul_nonneg (div_nonneg ht hε) (greenKernel_nonneg _ _ _ _))

theorem matedObstacle_eq_zero_of_not_mem {a : ℤ} (ha : a ∉ ballInterior ε η ρ) : matedObstacle m ε η ρ t a = 0 := by
  simp [matedObstacle, greenKernel_eq_zero_of_not_mem_right _ _ ha]

theorem matedObstacle_eq_zero_of_origin_not_mem (h0 : (0 : ℤ) ∉ ballInterior ε η ρ) (a : ℤ) :
    matedObstacle m ε η ρ t a = 0 := by
  simp [matedObstacle, greenKernel_eq_zero_of_not_mem _ h0]

/-- `Δ^ε φ = 𝔱 δ_0` on `V`, from eq:discrete-normalized-green-laplacian. -/
theorem matedObstacle_laplacian
    (hG : ∀ b ∈ ballInterior ε η ρ, mLaplacian m (greenKernel m (ballInterior ε η ρ) 0) b =
      -((mdeg m 0 : ℝ)⁻¹ * if b = 0 then 1 else 0))
    {a : ℤ} (ha : a ∈ ballInterior ε η ρ) :
    mLaplacian m (matedObstacle m ε η ρ t) a =
      t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹ * (if a = 0 then 1 else 0) := by
  have : matedObstacle m ε η ρ t = fun b => -(t / ε) * greenKernel m (ballInterior ε η ρ) 0 b := rfl
  rw [this, mLaplacian_const_mul, hG a ha]
  unfold matedDeg
  ring

/-- The Section 4 data satisfy the hypotheses of Appendix A when `0 ∈ V` and `V` is connected (ESCALATIONS E-c1-2). -/
theorem matedObstacle_isObstacleSetting (ht : 0 < t) (hε : 0 < ε) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hfin : (ballInterior ε η ρ).Finite) (hcons : ∀ k, m k (k + 1) ≠ 0)
    (hconn : IsVConnected m (ballInterior ε η ρ)) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hG : ∀ b ∈ ballInterior ε η ρ, mLaplacian m (greenKernel m (ballInterior ε η ρ) 0) b =
      -((mdeg m 0 : ℝ)⁻¹ * if b = 0 then 1 else 0)) :
    IsObstacleSetting m (ballInterior ε η ρ) 0 (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
      (matedObstacle m ε η ρ t) (t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹) where
  symm := hsymm
  loopless := hloop
  locallyFinite := hlf
  infinite := inferInstance
  finite := hfin
  connected := hconn
  origin_mem := h0
  threshold_pos := fun a _ => inv_pos.2 (Nat.cast_pos.2 (mdeg_pos_of_ne_zero hlf (hcons a)))
  obstacle_nonpos := fun a _ => matedObstacle_nonpos ht.le hε.le a
  obstacle_laplacian := fun a ha => by
    rw [matedObstacle_laplacian hG ha]
    by_cases h : a = 0 <;> simp [h]
  obstacle_boundary := fun _ ha => matedObstacle_eq_zero_of_not_mem ha.1
  mass_pos := mul_pos (div_pos ht hε) (inv_pos.2 (Nat.cast_pos.2 (mdeg_pos_of_ne_zero hlf (hcons 0))))

end Mated

/-! ## Lemmas 4.3-4.5 for fixed `t, ε` -/

/-- The Section 4 data satisfy the hypotheses of Appendix A under the map of lines 3400-3411:
`V = V^ε(B_ρ) \ V^ε(∂B_ρ)`, origin `0`, `𝔯 = (deg^ε)⁻¹`, `φ = -(t ε⁻¹) g^ε_{B_ρ}(0, ·)`, `𝔱 = ε⁻¹ t deg^ε(0)⁻¹`. -/
abbrev IsMatedObstacleSetting (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) : Prop :=
  IsObstacleSetting m (ballInterior ε η ρ) 0 (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
    (matedObstacle m ε η ρ t) (t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹)

section Fixed

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

theorem matedLeastSupersolution_eq : matedLeastSupersolution m ε η ρ t =
    discreteLeastSupersolution m (ballInterior ε η ρ) (cellVertices ε η (closedBall 0 ρ))
      (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹) (matedObstacle m ε η ρ t) :=
  rfl

theorem matedDiscreteCluster_eq : matedDiscreteCluster m ε η ρ t =
    discreteCluster (cellVertices ε η (ball 0 ρ)) (matedLeastSupersolution m ε η ρ t) (matedObstacle m ε η ρ t) :=
  rfl

theorem matedObstacle_eq_zero_off_vClosure :
    ∀ b ∈ cellVertices ε η (closedBall 0 ρ), b ∉ vClosure m (ballInterior ε η ρ) →
      matedObstacle m ε η ρ t b = 0 :=
  fun _ _ hb => matedObstacle_eq_zero_of_not_mem fun h => hb (Or.inl h)

/-- If `0 ∉ V`, the obstacle vanishes and so does `w̃^ε_t` on `V^ε(cl B_ρ)`. -/
theorem matedLeastSupersolution_eq_zero_of_origin_not_mem (h0 : (0 : ℤ) ∉ ballInterior ε η ρ) {a : ℤ}
    (ha : a ∈ cellVertices ε η (closedBall 0 ρ)) : matedLeastSupersolution m ε η ρ t a = 0 :=
  dls_eq_zero_of_obstacle_zero (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
    (fun b _ => matedObstacle_eq_zero_of_origin_not_mem h0 b) ha

/-- If `0 ∉ V`, the discrete cluster is empty. -/
theorem matedDiscreteCluster_eq_empty (h0 : (0 : ℤ) ∉ ballInterior ε η ρ) : matedDiscreteCluster m ε η ρ t = ∅ := by
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha, hlt⟩
  rw [matedLeastSupersolution_eq_zero_of_origin_not_mem h0 (cellVertices_ball_subset_closedBall ha),
    matedObstacle_eq_zero_of_origin_not_mem h0 a] at hlt
  exact lt_irrefl _ hlt

theorem matedLaplacian_eq_zero_of_origin_not_mem (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (h0 : (0 : ℤ) ∉ ballInterior ε η ρ) {a : ℤ}
    (ha : a ∈ ballInterior ε η ρ) : matedLaplacian m (matedLeastSupersolution m ε η ρ t) a = 0 :=
  mLaplacian_eq_zero_of_vClosure
    (fun _ hb => matedLeastSupersolution_eq_zero_of_origin_not_mem h0 (vClosure_ballInterior_subset hη hcell hb)) ha

/-- Lemma 4.3 for fixed `t, ε`. -/
theorem matedBasicProperties_fixed (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hS : (0 : ℤ) ∈ ballInterior ε η ρ → IsMatedObstacleSetting m ε η ρ t)
    (hq : (0 : ℤ) ∈ ballInterior ε η ρ → ∀ a ∈ ballInterior ε η ρ,
      mLaplacian m (normExitTime m (ballInterior ε η ρ)) a = -((matedDeg m a : ℕ) : ℝ)⁻¹) :
    (∀ a ∈ cellVertices ε η (closedBall 0 ρ),
      max (-normExitTime m (ballInterior ε η ρ) a) (matedObstacle m ε η ρ t a) ≤
        matedLeastSupersolution m ε η ρ t a ∧ matedLeastSupersolution m ε η ρ t a ≤ 0) ∧
    ∀ a ∈ ballInterior ε η ρ,
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ≤ ((matedDeg m a : ℕ) : ℝ)⁻¹ := by
  have hW := vClosure_ballInterior_subset (ε := ε) (ρ := ρ) hη hcell
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hS h0
    have hφ := matedObstacle_eq_zero_off_vClosure (m := m) (ε := ε) (η := η) (ρ := ρ) (t := t)
    have hq' : ∀ a ∈ ballInterior ε η ρ, mLaplacian m
        (fun b => -normExitTime m (ballInterior ε η ρ) b) a = ((matedDeg m a : ℕ) : ℝ)⁻¹ := by
      intro a ha
      have : (fun b => -normExitTime m (ballInterior ε η ρ) b) =
          fun b => (-1) * normExitTime m (ballInterior ε η ρ) b := funext fun _ => by ring
      rw [this, mLaplacian_const_mul, hq h0 a ha]
      ring
    have hqb : ∀ a ∈ vBoundary m (ballInterior ε η ρ),
        -normExitTime m (ballInterior ε η ρ) a = 0 := fun a ha => by
      rw [normExitTime_eq_zero_of_not_mem _ ha.1, neg_zero]
    have hA := discreteBasicPropertiesGeneral ℤ _ _ _ _ _ _ hS _ hq' hqb
    rw [matedLeastSupersolution_eq]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · by_cases hac : a ∈ vClosure m (ballInterior ε η ρ)
      · rw [dls_eq_of_mem_vClosure hS hW hφ hac]
        exact hA.1 a hac
      · rw [dls_eq_zero_of_not_mem_vClosure hS hφ ha hac, hφ a ha hac,
          normExitTime_eq_zero_of_not_mem _ fun h => hac (Or.inl h)]
        simp
    · rw [matedLaplacian, mLaplacian_dls_eq hS hW hφ ha]
      exact hA.2 a ha
  · refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [matedLeastSupersolution_eq_zero_of_origin_not_mem h0 ha, matedObstacle_eq_zero_of_origin_not_mem h0 a]
      exact ⟨max_le (neg_nonpos.2 (normExitTime_nonneg _ _ _)) le_rfl, le_rfl⟩
    · rw [matedLaplacian_eq_zero_of_origin_not_mem hη hcell h0 ha]
      exact inv_nonneg.2 (Nat.cast_nonneg _)

/-- Lemma 4.4 for fixed `t, ε`, with the origin claim under `0 ∈ V` (ESCALATIONS E-c1-1). -/
theorem matedLaplacianBound_fixed (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hS : (0 : ℤ) ∈ ballInterior ε η ρ → IsMatedObstacleSetting m ε η ρ t) :
    (∀ a ∈ matedDiscreteCluster m ε η ρ t,
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹) ∧
    (∀ a ∈ ballInterior ε η ρ,
      0 ≤ matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ∧
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ≤ ((matedDeg m a : ℕ) : ℝ)⁻¹) ∧
    IsVPreconnected m (matedDiscreteCluster m ε η ρ t) ∧
    (1 < t / ε → (0 : ℤ) ∈ ballInterior ε η ρ → (0 : ℤ) ∈ matedDiscreteCluster m ε η ρ t) := by
  have hW := vClosure_ballInterior_subset (ε := ε) (ρ := ρ) hη hcell
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hS h0
    have hφ := matedObstacle_eq_zero_off_vClosure (m := m) (ε := ε) (η := η) (ρ := ρ) (t := t)
    have hA := discreteLaplacianBoundGeneral ℤ _ _ _ _ _ _ hS
    rw [matedDiscreteCluster_eq, matedLeastSupersolution_eq,
      discreteCluster_eq hS hW hφ ballInterior_subset_cellVertices_ball cellVertices_ball_subset_closedBall]
    refine ⟨fun a ha => ?_, fun a ha => ?_, hA.2.2.1, fun h1 _ => hA.2.2.2 ?_⟩
    · rw [matedLaplacian, mLaplacian_dls_eq hS hW hφ (IsObstacleSetting.cluster_subset hS ha)]
      exact hA.1 a ha
    · rw [matedLaplacian, mLaplacian_dls_eq hS hW hφ ha]
      exact hA.2.1 a ha
    · show ((matedDeg m 0 : ℕ) : ℝ)⁻¹ < t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹
      exact lt_mul_of_one_lt_left (inv_pos.2 (Nat.cast_pos.2 (IsObstacleSetting.mdeg_origin_pos hS))) h1
  · rw [matedDiscreteCluster_eq_empty h0]
    refine ⟨fun a ha => absurd ha (by simp), fun a ha => ?_, ?_, fun _ h => absurd h h0⟩
    · rw [matedLaplacian_eq_zero_of_origin_not_mem hη hcell h0 ha]
      exact ⟨le_rfl, inv_nonneg.2 (Nat.cast_nonneg _)⟩
    · intro u
      exact ((Set.mem_empty_iff_false _).mp u.2).elim

/-- Lemma 4.5 for fixed `t, ε`, with the mass identity under `0 ∈ V` (ESCALATIONS E-c1-1). -/
theorem matedConservationOfMass_fixed (hη : Continuous η)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (ht : 0 < t) (hε : 0 < ε)
    (hS : (0 : ℤ) ∈ ballInterior ε η ρ → IsMatedObstacleSetting m ε η ρ t) :
    (matedDiscreteCluster m ε η ρ t).Finite ∧
    ((matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤ t / ε ∧
    ((0 : ℤ) ∈ ballInterior ε η ρ →
      matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ) →
      ∑' a : ballInterior ε η ρ,
        matedLaplacian m (matedLeastSupersolution m ε η ρ t) a * (matedDeg m a : ℝ) = t / ε) := by
  have hW := vClosure_ballInterior_subset (ε := ε) (ρ := ρ) hη hcell
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hS h0
    have hφ := matedObstacle_eq_zero_off_vClosure (m := m) (ε := ε) (η := η) (ρ := ρ) (t := t)
    have hA := discreteConservationOfMassGeneral ℤ _ _ _ _ _ _ hS fun _ _ => rfl
    have hd : ((mdeg m 0 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (IsObstacleSetting.mdeg_origin_pos hS).ne'
    have h𝔱 : t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹ * (mdeg m 0 : ℝ) = t / ε :=
      inv_mul_cancel_right₀ hd _
    rw [matedDiscreteCluster_eq, matedLeastSupersolution_eq,
      discreteCluster_eq hS hW hφ ballInterior_subset_cellVertices_ball cellVertices_ball_subset_closedBall]
    refine ⟨IsObstacleSetting.cluster_finite hS, hA.1.trans_eq h𝔱, fun _ hint => ?_⟩
    have hfs : (Function.support ((ballInterior ε η ρ).indicator fun a =>
        matedLaplacian m (discreteLeastSupersolution m (ballInterior ε η ρ)
          (cellVertices ε η (closedBall 0 ρ)) (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹) (matedObstacle m ε η ρ t)) a *
            (matedDeg m a : ℝ))).Finite :=
      (IsObstacleSetting.finite hS).subset (Set.support_indicator_subset)
    rw [tsum_subtype (ballInterior ε η ρ) (fun a => matedLaplacian m (discreteLeastSupersolution m
        (ballInterior ε η ρ) (cellVertices ε η (closedBall 0 ρ)) (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
          (matedObstacle m ε η ρ t)) a * (matedDeg m a : ℝ)), tsum_eq_finsum hfs, ← finsum_mem_def, ← h𝔱,
      ← hA.2 hint]
    exact finsum_mem_congr rfl fun a ha =>
      congrArg (· * (mdeg m a : ℝ)) (mLaplacian_dls_eq hS hW hφ ha)
  · rw [matedDiscreteCluster_eq_empty h0, Set.ncard_empty, Nat.cast_zero]
    exact ⟨Set.finite_empty, div_nonneg ht.le hε.le, fun h => absurd h h0⟩

end Fixed

/-! ## Steps -/

/-- *Properness of the space-filling curve*: almost surely `η(s) → ∞` as `|s| → ∞`. Whole-plane space-filling SLE from
`∞` to `∞` (Miller-Sheffield, Imaginary geometry IV, Section 1.2.3; paper lines 606-621) has this property; it is not
derivable from the area parametrization alone. Gives finiteness of `V^ε(B_ρ)` and local finiteness of `𝒢^ε`. -/
def EtaProperStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)

/-- *Consecutive cells are adjacent*: almost surely, for every `ε > 0` and every vertex `a = εk`, the cells
`η([a-ε, a])` and `η([a, a+ε])` intersect along a non-trivial boundary arc, so `εk ∼ ε(k+1)` in `𝒢^ε`. In the Brownian
description (Definition 1.1, line 175) consecutive vertices are always adjacent; Definitions 1.1 and 1.2 agree
almost surely (Duplantier-Miller-Sheffield, Mating of trees, Theorem 1.9 and Lemma 8.8; line 202). -/
def ConsecutiveCellsAdjacentStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0

/-- *Laplacian of the Green's kernel* (eq:discrete-normalized-green-laplacian, line 804; Lawler-Limic, Random walk: a
modern introduction, Proposition 6.2.3): for a finite `A` in a symmetric, locally finite multigraph on `ℤ` in which
`a ∼ a + 1` for all `a`, `Δ g_A(o, ·) = -deg(o)⁻¹ δ_o` on `A`. Deterministic; derivable from the definitions
(Markov property of `srwLaw`). -/
def GreenKernelLaplacianStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (A : Set ℤ), (∀ a b, m a b = m b a) → (∀ a, {b | m a b ≠ 0}.Finite) →
    (∀ a, m a (a + 1) ≠ 0) → A.Finite → ∀ o ∈ A, ∀ b ∈ A,
      mLaplacian m (greenKernel m A o) b = -((mdeg m o : ℝ)⁻¹ * if b = o then 1 else 0)

/-- *Laplacian of the normalized expected exit time* (eq:discrete-normalized-exit-laplacian, line 790; Lawler-Limic,
Proposition 6.2.3): in the setting of `GreenKernelLaplacianStep`, `Δ q_A = -deg⁻¹` on `A`. Deterministic; derivable
from the definitions (Markov property of `srwLaw`). -/
def NormExitTimeLaplacianStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (A : Set ℤ), (∀ a b, m a b = m b a) → (∀ a, {b | m a b ≠ 0}.Finite) →
    (∀ a, m a (a + 1) ≠ 0) → A.Finite → ∀ a ∈ A, mLaplacian m (normExitTime m A) a = -(mdeg m a : ℝ)⁻¹

/-- *The Section 4 obstacle problem is an Appendix A obstacle problem* (lines 3400-3411): almost surely, for all
`t, ε > 0` with `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`, the data satisfy `IsObstacleSetting`. Proved (Proofs/Sec4) from
`EtaProperStep`, `ConsecutiveCellsAdjacentStep` and `GreenKernelLaplacianStep`, except for the field `connected`
(ESCALATIONS E-c1-2). -/
def MatedObstacleSettingStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
    IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t

/-- *Connectivity of `V^ε(B_ρ) \ V^ε(∂B_ρ)`*, required only by the field `IsObstacleSetting.connected` (paper line 3339,
"a finite, connected set of vertices V", applied at line 3406). Not a literature fact and suspected false: a cell inside
`B_ρ` can be enclosed by cells meeting `∂B_ρ` (ESCALATIONS E-c1-2). Lemmas 4.3-4.5 do not need it; this step disappears
once the field is weakened (owner A). -/
def BallInteriorConnectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
    IsVConnected (S.mult ε ω) (ballInterior ε (S.η ω) ρ)

/-! ## Corrected statements of Lemmas 4.4 and 4.5 (ESCALATIONS E-c1-1) -/

/-- **Lemma 4.4**, corrected: the claim `0 ∈ Λ^ε_t` needs `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)` (the origin of Appendix A). -/
def DiscreteLaplacianBoundCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a = ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    (∀ a ∈ ballInterior ε (S.η ω) ρ,
      0 ≤ matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ∧
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤ ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    IsVPreconnected (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) ∧
    (1 < t / ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ → (0 : ℤ) ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)

/-- **Lemma 4.5**, corrected: the mass identity needs `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
def DiscreteConservationOfMassCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite ∧
    ((matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤ t / ε ∧
    ((0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆ vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) →
      ∑' a : ballInterior ε (S.η ω) ρ,
        matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a * (matedDeg (S.mult ε ω) a : ℝ) = t / ε)

/-! ## Lemmas 4.3-4.5 from the steps -/

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1679) from the steps. -/
theorem discreteBasicProperties_of_steps {𝒮 : SpaceFillingSLEModel} (hset : MatedObstacleSettingStep 𝒮)
    (hcons : ConsecutiveCellsAdjacentStep 𝒮) (hq : NormExitTimeLaplacianStep) (hcell : AdjacentCellsMeetStep 𝒮) :
    DiscreteBasicPropertiesStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hset γ hγ hγ2 ρ hρ hρ1 Ω S hS, hcons γ hγ hγ2 Ω S hS, hS.isAreaParametrized,
    hcell γ hγ hγ2 Ω S hS] with ω hω hc hη hcω
  intro t ε ht hε
  exact matedBasicProperties_fixed hη.1 (hcω ε hε) (hω t ε ht hε) fun h0 a ha =>
    hq _ _ (S.mult_symm ε ω) (hω t ε ht hε h0).locallyFinite (hc ε hε) (hω t ε ht hε h0).finite a ha

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, line 1697), corrected (E-c1-1), from the steps. -/
theorem discreteLaplacianBoundCorrected_of_steps {𝒮 : SpaceFillingSLEModel} (hset : MatedObstacleSettingStep 𝒮)
    (hcell : AdjacentCellsMeetStep 𝒮) : DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hset γ hγ hγ2 ρ hρ hρ1 Ω S hS, hS.isAreaParametrized, hcell γ hγ hγ2 Ω S hS] with ω hω hη hcω
  intro t ε ht hε
  exact matedLaplacianBound_fixed hη.1 (hcω ε hε) (hω t ε ht hε)

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, line 1705), corrected (E-c1-1), from the steps. -/
theorem discreteConservationOfMassCorrected_of_steps {𝒮 : SpaceFillingSLEModel}
    (hset : MatedObstacleSettingStep 𝒮) (hcell : AdjacentCellsMeetStep 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hset γ hγ hγ2 ρ hρ hρ1 Ω S hS, hS.isAreaParametrized, hcell γ hγ hγ2 Ω S hS] with ω hω hη hcω
  intro t ε ht hε
  exact matedConservationOfMass_fixed hη.1 (hcω ε hε) ht hε (hω t ε ht hε)

end MatedCRT
