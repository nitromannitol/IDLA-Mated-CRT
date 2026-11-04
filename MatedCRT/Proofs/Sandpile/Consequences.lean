import MatedCRT.Proofs.Sandpile.LeastAction

/-! Consequences of the least action principle for the divisible sandpile. -/

namespace MatedCRT.Sandpile

open Set Finset Classical

variable {m : ℤ → ℤ → ℕ} {M : ℝ}

/-- If the initial mass is at most one, no vertex needs to topple. -/
theorem zero_admissible (hM : M ≤ 1) : (fun _ => (0 : ℝ)) ∈ admissible m M := by
  refine ⟨fun _ => le_rfl, fun b => ?_⟩
  by_cases hb : b = 0
  · subst b
    simp only [mLaplacian, sub_self, mul_zero, finsum_zero, zero_add,
      diracZero, ite_true, mul_one]
    exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hM
  · simp only [mLaplacian, sub_self, mul_zero, finsum_zero, zero_add, diracZero, ite_eq_right hb]
    exact inv_nonneg.2 (Nat.cast_nonneg _)

theorem normOdometer_eq_zero_of_mass_le_one (hM : M ≤ 1) :
    sandpileNormOdometer m M = 0 := by
  funext a
  apply le_antisymm
  · exact normOdometer_le (fun _ => 0) (zero_admissible hM) a
  · exact normOdometer_nonneg ⟨_, zero_admissible hM⟩ a

theorem final_of_mass_le_one (hM : M ≤ 1) (a : ℤ) :
    sandpileFinal m M a = M * diracZero a := by
  simp [sandpileFinal, normOdometer_eq_zero_of_mass_le_one hM, mLaplacian]

/-- For positive mass at most one the final cluster is the singleton origin,
although the set of vertices that topple is empty. -/
theorem cluster_of_mass_le_one (hMpos : 0 < M) (hM : M ≤ 1) :
    sandpileCluster m M = {0} := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp [sandpileCluster, final_of_mass_le_one hM, diracZero, hMpos]
  · simp [sandpileCluster, final_of_mass_le_one hM, diracZero, ha]

/-- The support of the final configuration is monotone in the initial mass. -/
theorem cluster_mono (hlf : IsLocallyFiniteMult m) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) {M₁ M₂ : ℝ} (hM : M₁ ≤ M₂)
    (hne₂ : (admissible m M₂).Nonempty) :
    sandpileCluster m M₁ ⊆ sandpileCluster m M₂ := by
  have hne₁ : (admissible m M₁).Nonempty := by
    obtain ⟨w, hw⟩ := hne₂
    refine ⟨w, hw.1, fun b => ?_⟩
    have hc : 0 ≤ (mdeg m 0 : ℝ)⁻¹ * diracZero b := by
      apply mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      simp [diracZero]; split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_left hM hc
    nlinarith [hw.2 b]
  intro a ha
  change 0 < sandpileFinal m M₁ a at ha
  change 0 < sandpileFinal m M₂ a
  by_cases hpos : 0 < sandpileNormOdometer m M₂ a
  · rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg hne₂ hpos]
    norm_num
  · have hz₂ : sandpileNormOdometer m M₂ a = 0 :=
      le_antisymm (not_lt.mp hpos) (normOdometer_nonneg hne₂ a)
    have hz₁ : sandpileNormOdometer m M₁ a = 0 := by
      apply le_antisymm _ (normOdometer_nonneg hne₁ a)
      simpa [hz₂] using normOdometer_mono hM hne₂ a
    have hlap : lapSum hlf (sandpileNormOdometer m M₁) a ≤
        lapSum hlf (sandpileNormOdometer m M₂) a := by
      apply lapSum_le_lapSum hlf
      · intro b hb
        exact normOdometer_mono hM hne₂ b
      · simp [hz₁, hz₂]
    have hlap' : mLaplacian m (sandpileNormOdometer m M₁) a ≤
        mLaplacian m (sandpileNormOdometer m M₂) a := by
      simp only [mLaplacian_eq_div hlf]
      exact div_le_div_of_nonneg_right hlap (Nat.cast_nonneg _)
    have hdir : 0 ≤ diracZero a := by
      simp [diracZero]; split_ifs <;> norm_num
    have hmass := mul_le_mul_of_nonneg_right hM hdir
    have hflux := mul_le_mul_of_nonneg_left hlap' (Nat.cast_nonneg (mdeg m a))
    unfold sandpileFinal at ha ⊢
    linarith

/-- Off the origin and the closure of the odometer support, the final mass vanishes. -/
theorem final_support_subset (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a) :
    Function.support (sandpileFinal m M) ⊆ insert 0 (vClosure m (Function.support (sandpileNormOdometer m M))) := by
  intro a ha
  by_contra hn
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    exact hn (mem_insert 0 _)
  have haK : a ∉ Function.support (sandpileNormOdometer m M) := fun h => hn (mem_insert_of_mem _ (Or.inl h))
  have hau : sandpileNormOdometer m M a = 0 := by simpa [Function.mem_support] using haK
  have hnb : ∀ b ∈ nbrs hlf a, sandpileNormOdometer m M b = 0 := by
    intro b hb
    by_contra hbu
    have hbK : b ∈ Function.support (sandpileNormOdometer m M) := hbu
    have hba : m b a ≠ 0 := by rw [hsymm]; exact (mem_nbrs hlf).1 hb
    exact hn (mem_insert_of_mem _ (Or.inr ⟨haK, b, hbK, hba⟩))
  apply ha
  unfold sandpileFinal
  rw [mul_comm (mdeg m a : ℝ), mLaplacian_mul_mdeg hlf]
  have hsum : lapSum hlf (sandpileNormOdometer m M) a = 0 := by
    unfold lapSum
    apply Finset.sum_eq_zero
    intro b hb
    simp [hau, hnb b hb]
  simp [diracZero, ha0, hsum]

theorem final_finiteSupport (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (w : ℤ → ℝ) (hw : w ∈ admissible m M) (hfin : (Function.support w).Finite) :
    (Function.support (sandpileFinal m M)).Finite := by
  have hK := normOdometer_finiteSupport ⟨w, hw⟩ w hw hfin
  have hB : (vBoundary m (Function.support (sandpileNormOdometer m M))).Finite := by
    refine (hK.biUnion fun a _ => hlf a).subset ?_
    rintro c ⟨-, a, ha, hac⟩
    exact mem_biUnion ha hac
  exact ((hK.union hB).insert 0).subset (final_support_subset hlf hsymm)

/-- Conservation of total mass, once a finite-support admissible witness is given. -/
theorem finsum_final_eq_mass (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (w : ℤ → ℝ) (hw : w ∈ admissible m M) (hfin : (Function.support w).Finite) :
    ∑ᶠ a, sandpileFinal m M a = M := by
  classical
  let K := Function.support (sandpileNormOdometer m M)
  have hK : K.Finite := normOdometer_finiteSupport ⟨w, hw⟩ w hw hfin
  have hB : (vBoundary m K).Finite := by
    refine (hK.biUnion fun a _ => hlf a).subset ?_
    rintro c ⟨-, a, ha, hac⟩
    exact mem_biUnion ha hac
  have hT : (insert 0 (vClosure m K)).Finite := (hK.union hB).insert 0
  let s := hT.toFinset
  have hs : ∀ a, a ∈ s ↔ a ∈ insert 0 (vClosure m K) := fun a => hT.mem_toFinset
  have h0 : (0 : ℤ) ∈ s := (hs 0).2 (mem_insert 0 _)
  have hout : ∀ a ∉ s, sandpileNormOdometer m M a = 0 := by
    intro a ha
    have haK : a ∉ K := fun h => ha ((hs a).2 (mem_insert_of_mem _ (Or.inl h)))
    simpa [K, Function.mem_support] using haK
  have hclosed : ∀ a ∈ s, ∀ b ∉ s, m a b ≠ 0 → sandpileNormOdometer m M a = 0 := by
    intro a ha b hb hab
    by_contra hau
    have haK : a ∈ K := hau
    have hbK : b ∉ K := fun h => hb ((hs b).2 (mem_insert_of_mem _ (Or.inl h)))
    exact hb ((hs b).2 (mem_insert_of_mem _ (Or.inr ⟨hbK, a, haK, hab⟩)))
  rw [finsum_eq_sum_of_support_subset _ ?_]
  · exact sum_final_eq_mass hlf hsymm s h0 hout hclosed
  · intro a ha
    rw [Finset.mem_coe, hs]
    exact final_support_subset hlf hsymm ha

/-- The number of sites that emit mass is at most the initial mass.  The
larger cluster also contains partially filled boundary sites. -/
theorem odometer_support_ncard_le_mass (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hM : 0 ≤ M)
    (w : ℤ → ℝ) (hw : w ∈ admissible m M) (hfin : (Function.support w).Finite) :
    ((Function.support (sandpileNormOdometer m M)).ncard : ℝ) ≤ M := by
  let K := Function.support (sandpileNormOdometer m M)
  let F := Function.support (sandpileFinal m M)
  have hK : K.Finite := normOdometer_finiteSupport ⟨w, hw⟩ w hw hfin
  have hF : F.Finite := final_finiteSupport hlf hsymm w hw hfin
  have hsub : K ⊆ F := by
    intro a ha
    have hpos : 0 < sandpileNormOdometer m M a :=
      lt_of_le_of_ne (normOdometer_nonneg ⟨w, hw⟩ a) (Ne.symm ha)
    change sandpileFinal m M a ≠ 0
    rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg ⟨w, hw⟩ hpos]
    norm_num
  have hsub' : hK.toFinset ⊆ hF.toFinset := Set.Finite.toFinset_subset_toFinset.2 hsub
  have hone : ∀ a ∈ hK.toFinset, sandpileFinal m M a = 1 := by
    intro a ha
    have haK := hK.mem_toFinset.1 ha
    apply final_eq_one_of_normOdometer_pos hlf hloop hdeg ⟨w, hw⟩
    exact lt_of_le_of_ne (normOdometer_nonneg ⟨w, hw⟩ a) (Ne.symm haK)
  have hsum : ∑ a ∈ hF.toFinset, sandpileFinal m M a = M := by
    rw [← finsum_eq_sum_of_support_subset (sandpileFinal m M) (by
      intro a ha
      exact hF.mem_toFinset.2 ha)]
    exact finsum_final_eq_mass hlf hsymm w hw hfin
  calc
    (K.ncard : ℝ) = ∑ a ∈ hK.toFinset, sandpileFinal m M a := by
      rw [Set.ncard_eq_toFinset_card _ hK, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
        Finset.sum_congr rfl hone]
    _ ≤ ∑ a ∈ hF.toFinset, sandpileFinal m M a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub'
        (fun a _ _ => final_nonneg hlf hloop hdeg ⟨w, hw⟩ hM a)
    _ = M := hsum

end MatedCRT.Sandpile
