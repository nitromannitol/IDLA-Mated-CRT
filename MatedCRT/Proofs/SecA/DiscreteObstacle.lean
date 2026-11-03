import MatedCRT.Draft.SectionA
import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# Appendix A: the discrete obstacle problem (Lemmas A.2-A.4)

Proofs of the properties of the discrete least supersolution `w = discreteLeastSupersolution m V (cl V) 𝔯 φ` in the
setting of Appendix A (`IsObstacleSetting`), following lines 3420-3556 of the corrected draft:

* `IsObstacleSetting.boundary_nonempty`, `IsObstacleSetting.mdeg_pos`: `∂V ≠ ∅` and every vertex of `V` has an edge
  (from `Δφ = 𝔱 δ_o` with `𝔱 > 0`, the Gauss-Green identity and connectedness of `V`);
* `lap_w_le` (the infimum of supersolutions is a supersolution, so it is the minimum), `q_le_w` (comparison with `𝔮`
  by the minimum principle): Lemma A.2;
* `lap_w_eq_on_cluster` (perturbation `w - η δ_a`), `lap_w_nonneg`, `origin_mem_cluster`, `cluster_preconnected`
  (replacing `w` by `φ` on a component of `Λ` not containing the origin): Lemma A.3;
* `card_cluster_le`, `sum_lap_w_eq` (Gauss-Green identity for `w - φ`): Lemma A.4.
-/

namespace MatedCRT

open Set Finset Classical

variable {α : Type*} {m : α → α → ℕ} {V : Set α} {o : α} {𝔯 φ : α → ℝ} {𝔱 : ℝ}

/-- The admissible functions of the discrete obstacle problem: `Δu ≤ 𝔯` on `V` and `u ≥ φ` on `W`. -/
def obstacleAdmissible (m : α → α → ℕ) (V W : Set α) (𝔯 φ : α → ℝ) : Set (α → ℝ) :=
  {u | (∀ b ∈ V, mLaplacian m u b ≤ 𝔯 b) ∧ ∀ b ∈ W, φ b ≤ u b}

theorem discreteLeastSupersolution_eq (m : α → α → ℕ) (V W : Set α) (𝔯 φ : α → ℝ) (a : α) :
    discreteLeastSupersolution m V W 𝔯 φ a = sInf ((fun u : α → ℝ => u a) '' obstacleAdmissible m V W 𝔯 φ) :=
  rfl

namespace IsObstacleSetting

variable (h : IsObstacleSetting m V o 𝔯 φ 𝔱)
include h

local notation "𝔴" => discreteLeastSupersolution m V (vClosure m V) 𝔯 φ
local notation "𝒜" => obstacleAdmissible m V (vClosure m V) 𝔯 φ

theorem hlf : IsLocallyFiniteMult m := h.locallyFinite

theorem lapSum_obstacle (a : α) (ha : a ∈ V) :
    lapSum h.hlf φ a = 𝔱 * (if a = o then 1 else 0) * (mdeg m a : ℝ) := by
  rw [← mLaplacian_mul_mdeg h.hlf, h.obstacle_laplacian a ha]

theorem mdeg_origin_pos : 0 < mdeg m o := by
  rcases Nat.eq_zero_or_pos (mdeg m o) with h0 | h0
  · have := h.obstacle_laplacian o h.origin_mem
    simp [mLaplacian, h0] at this
    exact absurd this.symm h.mass_pos.ne'
  · exact h0

theorem lapSum_obstacle_nonneg (a : α) (ha : a ∈ V) : 0 ≤ lapSum h.hlf φ a := by
  rw [h.lapSum_obstacle a ha]
  have := h.mass_pos
  positivity

/-- `∂V ≠ ∅`: otherwise the Gauss-Green identity gives `0 = ∑_{a ∈ V} Δφ(a) deg(a) = 𝔱 deg(o) > 0`. -/
theorem boundary_nonempty : (vBoundary m V).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hflux := sum_lapSum_eq_flux h.hlf h.symm h.finite.toFinset φ
  have hzero : ∑ a ∈ h.finite.toFinset,
      ∑ b ∈ (nbrs h.hlf a).filter (· ∉ h.finite.toFinset), (m a b : ℝ) * (φ b - φ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hb
    rw [Set.Finite.mem_toFinset] at ha
    have : b ∈ vBoundary m V := ⟨hb.2, a, ha, (mem_nbrs h.hlf).1 hb.1⟩
    rw [hne] at this
    exact absurd this (Set.notMem_empty b)
  rw [hzero] at hflux
  have hsum : ∑ a ∈ h.finite.toFinset, lapSum h.hlf φ a = 𝔱 * (mdeg m o : ℝ) := by
    rw [Finset.sum_congr rfl fun a ha => h.lapSum_obstacle a (h.finite.mem_toFinset.1 ha)]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' h.finite.toFinset o, ite_eq_left (h.finite.mem_toFinset.2 h.origin_mem)]
  have hpos : 0 < 𝔱 * (mdeg m o : ℝ) := mul_pos h.mass_pos (by exact_mod_cast h.mdeg_origin_pos)
  linarith

/-- Every vertex of `V` has an edge: `V` is connected and `deg(o) > 0`. -/
theorem mdeg_pos (a : α) (ha : a ∈ V) : 0 < mdeg m a := by
  rcases Nat.eq_zero_or_pos (mdeg m a) with h0 | h0
  · exfalso
    have hnb := nbrs_eq_empty_of_mdeg_eq_zero h.hlf h0
    have hiso : ∀ y, m a y = 0 := by
      intro y
      by_contra hy
      have : y ∈ nbrs h.hlf a := (mem_nbrs h.hlf).2 hy
      rw [hnb] at this
      exact Finset.notMem_empty y this
    have hr := h.connected.preconnected ⟨a, ha⟩ ⟨o, h.origin_mem⟩
    have hoa : o = a := propagate_reachable h.symm (A := V) (fun z => z = a)
      (fun x _ y _ hxy hx => absurd (hx ▸ hiso y) hxy) hr rfl
    have := h.mdeg_origin_pos
    rw [hoa, h0] at this
    exact lt_irrefl 0 this
  · exact h0

theorem zero_mem_admissible : (fun _ => (0 : ℝ)) ∈ 𝒜 := by
  refine ⟨fun b hb => ?_, fun b hb => h.obstacle_nonpos b hb⟩
  have : mLaplacian m (fun _ => (0 : ℝ)) b = 0 := by simp [mLaplacian]
  rw [this]
  exact (h.threshold_pos b hb).le

omit h in
theorem bddBelow_values (a : α) (ha : a ∈ vClosure m V) : BddBelow ((fun u : α → ℝ => u a) '' 𝒜) := by
  refine ⟨φ a, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hu.2 a ha

theorem values_nonempty (a : α) : ((fun u : α → ℝ => u a) '' 𝒜).Nonempty :=
  ⟨_, ⟨_, h.zero_mem_admissible, rfl⟩⟩

theorem obstacle_le_w (a : α) (ha : a ∈ vClosure m V) : φ a ≤ 𝔴 a := by
  rw [discreteLeastSupersolution_eq]
  refine le_csInf (h.values_nonempty a) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hu.2 a ha

omit h in
theorem w_le (u : α → ℝ) (hu : u ∈ 𝒜) (a : α) (ha : a ∈ vClosure m V) : 𝔴 a ≤ u a := by
  rw [discreteLeastSupersolution_eq]
  exact csInf_le (bddBelow_values a ha) ⟨u, hu, rfl⟩

theorem w_nonpos (a : α) (ha : a ∈ vClosure m V) : 𝔴 a ≤ 0 :=
  w_le _ h.zero_mem_admissible a ha

theorem w_boundary (b : α) (hb : b ∈ vBoundary m V) : 𝔴 b = 0 ∧ φ b = 0 := by
  have hφ := h.obstacle_boundary b hb
  have hcl : b ∈ vClosure m V := Or.inr hb
  exact ⟨le_antisymm (w_le _ h.zero_mem_admissible b hcl) (hφ ▸ h.obstacle_le_w b hcl), hφ⟩

/-- The infimum of the supersolutions is a supersolution: `Δw ≤ 𝔯` on `V`. -/
theorem lap_w_le (a : α) (ha : a ∈ V) : mLaplacian m 𝔴 a ≤ 𝔯 a := by
  have hD : (0 : ℝ) < mdeg m a := by exact_mod_cast h.mdeg_pos a ha
  refine mLaplacian_le_of_lapSum_le h.hlf (h.threshold_pos a ha).le ?_
  by_contra hlt
  push Not at hlt
  set η := (lapSum h.hlf 𝔴 a - 𝔯 a * mdeg m a) / mdeg m a with hη
  have hηpos : 0 < η := div_pos (by linarith) hD
  have hlt' : sInf ((fun u : α → ℝ => u a) '' 𝒜) < 𝔴 a + η := by
    rw [← discreteLeastSupersolution_eq]; linarith
  obtain ⟨_, ⟨u, hu, rfl⟩, hua⟩ := exists_lt_of_csInf_lt (h.values_nonempty a) hlt'
  have key : lapSum h.hlf 𝔴 a ≤ lapSum h.hlf u a + (mdeg m a : ℝ) * (u a - 𝔴 a) := by
    unfold lapSum
    rw [mdeg_cast_eq h.hlf a, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    have hwb := w_le u hu b (mem_vClosure_of_mem_nbrs h.hlf ha hb)
    have := mul_le_mul_of_nonneg_left hwb (Nat.cast_nonneg (m a b))
    linarith
  have hu' := lapSum_le_of_mLaplacian_le h.hlf (hu.1 a ha)
  have h3 : (mdeg m a : ℝ) * (u a - 𝔴 a) < (mdeg m a : ℝ) * η :=
    mul_lt_mul_of_pos_left (by linarith) hD
  have h4 : (mdeg m a : ℝ) * η = lapSum h.hlf 𝔴 a - 𝔯 a * mdeg m a := by
    rw [hη]; field_simp
  linarith

theorem w_mem_admissible : 𝔴 ∈ 𝒜 :=
  ⟨fun b hb => h.lap_w_le b hb, fun b hb => h.obstacle_le_w b hb⟩

/-- Comparison with `𝔮` (minimum principle for `u - 𝔮`). -/
theorem q_le (𝔮 : α → ℝ) (hq : ∀ a ∈ V, mLaplacian m 𝔮 a = 𝔯 a) (hqb : ∀ a ∈ vBoundary m V, 𝔮 a = 0)
    (u : α → ℝ) (hu : u ∈ 𝒜) (a : α) (ha : a ∈ vClosure m V) : 𝔮 a ≤ u a := by
  have hsup : ∀ b ∈ V, lapSum h.hlf (fun c => u c - 𝔮 c) b ≤ 0 := by
    intro b hb
    rw [lapSum_sub, ← mLaplacian_mul_mdeg h.hlf 𝔮, hq b hb]
    linarith [lapSum_le_of_mLaplacian_le h.hlf (hu.1 b hb)]
  have hbd : ∀ b ∈ vBoundary m V, 0 ≤ u b - 𝔮 b := by
    intro b hb
    rw [hqb b hb, sub_zero, ← h.obstacle_boundary b hb]
    exact hu.2 b (Or.inr hb)
  rcases ha with haV | haB
  · linarith [nonneg_of_lapSum_nonpos h.hlf h.symm h.finite h.connected h.boundary_nonempty hsup hbd a haV]
  · linarith [hbd a haB]

/-! ### Lemma A.3 -/

local notation "𝔏" => discreteCluster (vClosure m V) 𝔴 φ

theorem w_eq_obstacle_of_not_mem (a : α) (ha : a ∈ vClosure m V) (hna : a ∉ 𝔏) : 𝔴 a = φ a := by
  have h1 := h.obstacle_le_w a ha
  by_contra hne
  exact hna ⟨ha, lt_of_le_of_ne h1 (Ne.symm hne)⟩

theorem cluster_subset : 𝔏 ⊆ V := by
  rintro a ⟨ha, hlt⟩
  rcases ha with haV | haB
  · exact haV
  · have := h.w_boundary a haB
    rw [this.1, this.2] at hlt
    exact absurd hlt (lt_irrefl 0)

/-- `Δw = 𝔯` on `Λ`: otherwise `w - η δ_a` is admissible for small `η > 0`. -/
theorem lap_w_eq_on_cluster (a : α) (ha : a ∈ 𝔏) : mLaplacian m 𝔴 a = 𝔯 a := by
  have haV := h.cluster_subset ha
  have hD : (0 : ℝ) < mdeg m a := by exact_mod_cast h.mdeg_pos a haV
  refine le_antisymm (h.lap_w_le a haV) ?_
  by_contra hlt
  push Not at hlt
  set η := min (𝔯 a - mLaplacian m 𝔴 a) (𝔴 a - φ a) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by linarith [ha.2])
  set w' : α → ℝ := fun b => if b = a then 𝔴 b - η else 𝔴 b with hw'
  have hw'adm : w' ∈ 𝒜 := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · refine mLaplacian_le_of_lapSum_le h.hlf (h.threshold_pos b hb).le ?_
      by_cases hba : b = a
      · subst hba
        have hsum : lapSum h.hlf w' b = lapSum h.hlf 𝔴 b + η * (mdeg m b : ℝ) := by
          unfold lapSum
          rw [mdeg_cast_eq h.hlf b, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c hc => ?_
          have hcb : c ≠ b := by
            rintro rfl
            exact (mem_nbrs h.hlf).1 hc (h.loopless c)
          simp only [hw', ite_eq_right hcb, ite_eq_left rfl]
          ring
        rw [hsum, ← mLaplacian_mul_mdeg h.hlf]
        have : η ≤ 𝔯 b - mLaplacian m 𝔴 b := min_le_left _ _
        nlinarith
      · have hle : lapSum h.hlf w' b ≤ lapSum h.hlf 𝔴 b := by
          refine lapSum_le_lapSum h.hlf (fun c _ => ?_) (by simp [hw', hba])
          simp only [hw']
          split_ifs <;> linarith
        linarith [lapSum_le_of_mLaplacian_le h.hlf (h.lap_w_le b hb)]
    · simp only [hw']
      split_ifs with hba
      · subst hba
        have : η ≤ 𝔴 b - φ b := min_le_right _ _
        linarith
      · exact h.obstacle_le_w b hb
  have := w_le w' hw'adm a (Or.inl haV)
  simp only [hw', ite_eq_left rfl] at this
  linarith

/-- `Δw ≥ 0` on `V`. -/
theorem lap_w_nonneg (a : α) (ha : a ∈ V) : 0 ≤ mLaplacian m 𝔴 a := by
  by_cases hc : a ∈ 𝔏
  · rw [h.lap_w_eq_on_cluster a hc]
    exact (h.threshold_pos a ha).le
  · have heq := h.w_eq_obstacle_of_not_mem a (Or.inl ha) hc
    have hle : lapSum h.hlf φ a ≤ lapSum h.hlf 𝔴 a :=
      lapSum_le_lapSum h.hlf (fun c hc' => h.obstacle_le_w c (mem_vClosure_of_mem_nbrs h.hlf ha hc'))
        heq.le
    rw [mLaplacian_eq_div h.hlf]
    exact div_nonneg (le_trans (h.lapSum_obstacle_nonneg a ha) hle) (Nat.cast_nonneg _)

/-- If `𝔱 > 𝔯(o)` the origin lies in `Λ`. -/
theorem origin_mem_cluster (ht : 𝔯 o < 𝔱) : o ∈ 𝔏 := by
  by_contra hno
  have hoV := h.origin_mem
  have heq := h.w_eq_obstacle_of_not_mem o (Or.inl hoV) hno
  have hle : lapSum h.hlf φ o ≤ lapSum h.hlf 𝔴 o :=
    lapSum_le_lapSum h.hlf (fun c hc' => h.obstacle_le_w c (mem_vClosure_of_mem_nbrs h.hlf hoV hc')) heq.le
  have hup := lapSum_le_of_mLaplacian_le h.hlf (h.lap_w_le o hoV)
  rw [h.lapSum_obstacle o hoV, ite_eq_left rfl, mul_one] at hle
  have hD : (0 : ℝ) < mdeg m o := by exact_mod_cast h.mdeg_origin_pos
  have : 𝔱 * (mdeg m o : ℝ) ≤ 𝔯 o * mdeg m o := le_trans hle hup
  have := le_of_mul_le_mul_right this hD
  linarith

/-- `Λ` is connected (possibly empty): replacing `w` by `φ` on a component of `Λ` which does not contain the origin
gives an admissible function below `w`. -/
theorem cluster_preconnected : IsVPreconnected m 𝔏 := by
  intro x y
  by_contra hxy
  -- a vertex of `Λ` not reachable from the origin
  obtain ⟨a₀, hno⟩ : ∃ a₀ : ↥𝔏, ∀ ho : o ∈ 𝔏, ¬ ((adjGraph m).induce 𝔏).Reachable ⟨o, ho⟩ a₀ := by
    by_cases hx : ∀ ho : o ∈ 𝔏, ¬ ((adjGraph m).induce 𝔏).Reachable ⟨o, ho⟩ x
    · exact ⟨x, hx⟩
    · push Not at hx
      obtain ⟨ho, hox⟩ := hx
      refine ⟨y, fun ho' hoy => hxy ?_⟩
      exact hox.symm.trans hoy
  set Λ₁ : Set α := {c | ∃ hc : c ∈ 𝔏, ((adjGraph m).induce 𝔏).Reachable a₀ ⟨c, hc⟩} with hΛ₁
  have hoΛ₁ : o ∉ Λ₁ := fun ⟨ho, hr⟩ => hno ho hr.symm
  have hclosed : ∀ b ∈ Λ₁, ∀ c ∈ 𝔏, m b c ≠ 0 → c ∈ Λ₁ := by
    rintro b ⟨hb, hrb⟩ c hc hbc
    have hne : b ≠ c := fun e => hbc (by rw [← e]; exact h.loopless b)
    refine ⟨hc, hrb.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.induce_adj, adjGraph_adj_iff h.symm]
    exact ⟨hne, hbc⟩
  set w' : α → ℝ := fun b => if b ∈ Λ₁ then φ b else 𝔴 b with hw'
  have hw'le : ∀ c ∈ vClosure m V, w' c ≤ 𝔴 c := by
    intro c hc
    simp only [hw']
    split_ifs
    · exact h.obstacle_le_w c hc
    · exact le_rfl
  have hw'adm : w' ∈ 𝒜 := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · refine mLaplacian_le_of_lapSum_le h.hlf (h.threshold_pos b hb).le ?_
      by_cases hbΛ : b ∈ Λ₁
      · have heq : lapSum h.hlf w' b = lapSum h.hlf φ b := by
          unfold lapSum
          refine Finset.sum_congr rfl fun c hc => ?_
          have hccl := mem_vClosure_of_mem_nbrs h.hlf hb hc
          have hwc : w' c = φ c := by
            by_cases hcΛ : c ∈ 𝔏
            · simp only [hw', ite_eq_left (hclosed b hbΛ c hcΛ ((mem_nbrs h.hlf).1 hc))]
            · have hcΛ₁ : c ∉ Λ₁ := fun h' => hcΛ h'.1
              simp only [hw', ite_eq_right hcΛ₁]
              exact h.w_eq_obstacle_of_not_mem c hccl hcΛ
          have hwb : w' b = φ b := by simp only [hw', ite_eq_left hbΛ]
          rw [hwc, hwb]
        have hbo : b ≠ o := fun hbo => hoΛ₁ (hbo ▸ hbΛ)
        rw [heq, h.lapSum_obstacle b hb, ite_eq_right hbo]
        have := (h.threshold_pos b hb).le
        simp only [mul_zero, zero_mul]
        positivity
      · have hle : lapSum h.hlf w' b ≤ lapSum h.hlf 𝔴 b :=
          lapSum_le_lapSum h.hlf (fun c hc => hw'le c (mem_vClosure_of_mem_nbrs h.hlf hb hc))
            (by simp [hw', hbΛ])
        linarith [lapSum_le_of_mLaplacian_le h.hlf (h.lap_w_le b hb)]
    · simp only [hw']
      split_ifs
      · exact le_rfl
      · exact h.obstacle_le_w b hb
  have ha₀Λ₁ : (a₀ : α) ∈ Λ₁ := ⟨a₀.2, SimpleGraph.Reachable.refl _⟩
  have h1 := w_le w' hw'adm a₀ a₀.2.1
  simp only [hw', ite_eq_left ha₀Λ₁] at h1
  exact absurd a₀.2.2 (not_lt.2 h1)

/-! ### Lemma A.4 -/

theorem cluster_finite : Set.Finite 𝔏 := h.finite.subset h.cluster_subset

/-- `∑_{a ∈ V} lapSum w a = 𝔱 deg(o) + (flux of `w - φ`)`, and the flux is `≤ 0`, `= 0` if `Λ ⊆ int V`. -/
theorem sum_lapSum_w_eq :
    ∑ a ∈ h.finite.toFinset, lapSum h.hlf 𝔴 a = 𝔱 * (mdeg m o : ℝ) +
      ∑ a ∈ h.finite.toFinset, ∑ b ∈ (nbrs h.hlf a).filter (· ∉ h.finite.toFinset),
        (m a b : ℝ) * ((𝔴 b - φ b) - (𝔴 a - φ a)) := by
  have hsplit : ∀ a, lapSum h.hlf 𝔴 a = lapSum h.hlf (fun c => 𝔴 c - φ c) a + lapSum h.hlf φ a := by
    intro a; rw [lapSum_sub]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [sum_lapSum_eq_flux h.hlf h.symm h.finite.toFinset (fun c => 𝔴 c - φ c)]
  have hsum : ∑ a ∈ h.finite.toFinset, lapSum h.hlf φ a = 𝔱 * (mdeg m o : ℝ) := by
    rw [Finset.sum_congr rfl fun a ha => h.lapSum_obstacle a (h.finite.mem_toFinset.1 ha)]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' h.finite.toFinset o, ite_eq_left (h.finite.mem_toFinset.2 h.origin_mem)]
  rw [hsum]
  ring

theorem flux_term_nonpos {a b : α} (ha : a ∈ V) (hb : b ∈ nbrs h.hlf a) (hbV : b ∉ V) :
    (m a b : ℝ) * ((𝔴 b - φ b) - (𝔴 a - φ a)) ≤ 0 := by
  have hbB : b ∈ vBoundary m V := ⟨hbV, a, ha, (mem_nbrs h.hlf).1 hb⟩
  obtain ⟨hw0, hφ0⟩ := h.w_boundary b hbB
  rw [hw0, hφ0]
  have := h.obstacle_le_w a (Or.inl ha)
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)

theorem sum_lapSum_w_le : ∑ a ∈ h.finite.toFinset, lapSum h.hlf 𝔴 a ≤ 𝔱 * (mdeg m o : ℝ) := by
  rw [h.sum_lapSum_w_eq]
  have : ∑ a ∈ h.finite.toFinset, ∑ b ∈ (nbrs h.hlf a).filter (· ∉ h.finite.toFinset),
      (m a b : ℝ) * ((𝔴 b - φ b) - (𝔴 a - φ a)) ≤ 0 := by
    refine Finset.sum_nonpos fun a ha => Finset.sum_nonpos fun b hb => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hb
    exact h.flux_term_nonpos (h.finite.mem_toFinset.1 ha) hb.1 hb.2
  linarith

theorem sum_lapSum_w_eq_of_subset (hint : 𝔏 ⊆ vInterior m V) :
    ∑ a ∈ h.finite.toFinset, lapSum h.hlf 𝔴 a = 𝔱 * (mdeg m o : ℝ) := by
  rw [h.sum_lapSum_w_eq]
  have : ∑ a ∈ h.finite.toFinset, ∑ b ∈ (nbrs h.hlf a).filter (· ∉ h.finite.toFinset),
      (m a b : ℝ) * ((𝔴 b - φ b) - (𝔴 a - φ a)) = 0 := by
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hb
    have haV := h.finite.mem_toFinset.1 ha
    have hbB : b ∈ vBoundary m V := ⟨hb.2, a, haV, (mem_nbrs h.hlf).1 hb.1⟩
    obtain ⟨hw0, hφ0⟩ := h.w_boundary b hbB
    have haΛ : a ∉ 𝔏 := fun haΛ => hb.2 ((hint haΛ).2 b ((mem_nbrs h.hlf).1 hb.1))
    have := h.w_eq_obstacle_of_not_mem a (Or.inl haV) haΛ
    rw [hw0, hφ0, this]
    ring
  rw [this, add_zero]

end IsObstacleSetting

end MatedCRT
