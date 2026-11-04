import MatedCRT.Defs.Sandpile
import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# Least action for the divisible sandpile

Order and attainment properties of the pointwise infimum in Section 4.  The
existence of an admissible function is kept explicit; it is a separate question
from the local finiteness needed for attainment.
-/

namespace MatedCRT.Sandpile

open Set Finset Classical

/-- The stabilizing functions appearing in the least action principle. -/
def admissible (m : ℤ → ℤ → ℕ) (M : ℝ) : Set (ℤ → ℝ) :=
  {w | (∀ b, 0 ≤ w b) ∧ ∀ b, mLaplacian m w b +
    (mdeg m 0 : ℝ)⁻¹ * M * diracZero b ≤ (mdeg m b : ℝ)⁻¹}

variable {m : ℤ → ℤ → ℕ} {M : ℝ}

theorem bddBelow_values (a : ℤ) : BddBelow ((fun w : ℤ → ℝ => w a) '' admissible m M) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hw.1 a

theorem normOdometer_nonneg (hne : (admissible m M).Nonempty) (a : ℤ) :
    0 ≤ sandpileNormOdometer m M a := by
  obtain ⟨w, hw⟩ := hne
  unfold sandpileNormOdometer
  refine le_csInf ⟨w a, w, hw, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hv.1 a

theorem normOdometer_le (w : ℤ → ℝ) (hw : w ∈ admissible m M) (a : ℤ) :
    sandpileNormOdometer m M a ≤ w a := by
  exact csInf_le (bddBelow_values a) ⟨w, hw, rfl⟩

/-- Local finiteness makes the pointwise infimum a stabilizing function. The
argument follows the proof for obstacle supersolutions in Leo's
`MatedCRT/Proofs/SecA/DiscreteObstacle.lean`. -/
theorem normOdometer_mem_admissible (hlf : IsLocallyFiniteMult m)
    (hne : (admissible m M).Nonempty) : sandpileNormOdometer m M ∈ admissible m M := by
  refine ⟨normOdometer_nonneg hne, fun a => ?_⟩
  set u := sandpileNormOdometer m M
  set c := (mdeg m 0 : ℝ)⁻¹ * M * diracZero a
  set r := (mdeg m a : ℝ)⁻¹ - c
  have hgoal : mLaplacian m u a ≤ r := by
    by_cases hd : mdeg m a = 0
    · have ⟨w, hw⟩ := hne
      have hw' := hw.2 a
      simp only [mLaplacian, hd, Nat.cast_zero, inv_zero, zero_mul] at hw' ⊢
      dsimp [r, c]
      simp only [hd, Nat.cast_zero, inv_zero]
      linarith
    · have hD : (0 : ℝ) < mdeg m a := by exact_mod_cast Nat.pos_of_ne_zero hd
      by_contra hlt
      have hlt : r * (mdeg m a : ℝ) < lapSum hlf u a := by
        rw [← mLaplacian_mul_mdeg hlf]
        exact mul_lt_mul_of_pos_right (lt_of_not_ge hlt) hD
      set η := (lapSum hlf u a - r * mdeg m a) / mdeg m a with hη
      have hηpos : 0 < η := div_pos (by linarith) hD
      obtain ⟨w, hw⟩ := hne
      have hval : ((fun v : ℤ → ℝ => v a) '' admissible m M).Nonempty := ⟨w a, w, hw, rfl⟩
      have hinf : sInf ((fun v : ℤ → ℝ => v a) '' admissible m M) < u a + η := by
        change u a < u a + η
        linarith
      obtain ⟨_, ⟨v, hv, rfl⟩, hva⟩ := exists_lt_of_csInf_lt hval hinf
      have key : lapSum hlf u a ≤ lapSum hlf v a + (mdeg m a : ℝ) * (v a - u a) := by
        unfold lapSum
        rw [mdeg_cast_eq hlf a, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun b hb => ?_
        have := mul_le_mul_of_nonneg_left (normOdometer_le v hv b) (Nat.cast_nonneg (m a b))
        change (m a b : ℝ) * u b ≤ (m a b : ℝ) * v b at this
        linarith
      have hv' : lapSum hlf v a ≤ r * (mdeg m a : ℝ) := by
        apply lapSum_le_of_mLaplacian_le hlf
        dsimp [r, c]
        linarith [hv.2 a]
      have h3 : (mdeg m a : ℝ) * (v a - u a) < (mdeg m a : ℝ) * η :=
        mul_lt_mul_of_pos_left (by linarith) hD
      have h4 : (mdeg m a : ℝ) * η = lapSum hlf u a - r * mdeg m a := by
        rw [hη]; field_simp
      linarith
  dsimp [r, c, u] at hgoal
  linarith

theorem normOdometer_mono {M₁ M₂ : ℝ} (hM : M₁ ≤ M₂)
    (hne : (admissible m M₂).Nonempty) (a : ℤ) :
    sandpileNormOdometer m M₁ a ≤ sandpileNormOdometer m M₂ a := by
  have hsub : admissible m M₂ ⊆ admissible m M₁ := by
    intro w hw
    refine ⟨hw.1, fun b => ?_⟩
    have hc : 0 ≤ (mdeg m 0 : ℝ)⁻¹ * diracZero b := by
      apply mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      simp [diracZero]; split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_left hM hc
    nlinarith [hw.2 b]
  obtain ⟨w, hw⟩ := hne
  unfold sandpileNormOdometer
  refine le_csInf ⟨w a, w, hw, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact csInf_le (bddBelow_values a) ⟨v, hsub hv, rfl⟩

theorem normOdometer_finiteSupport (hne : (admissible m M).Nonempty)
    (w : ℤ → ℝ) (hw : w ∈ admissible m M) (hfin : (Function.support w).Finite) :
    (Function.support (sandpileNormOdometer m M)).Finite := by
  apply hfin.subset
  intro a ha
  simp only [Function.mem_support] at ha ⊢
  intro hwa
  apply ha
  exact le_antisymm (by simpa [hwa] using normOdometer_le w hw a) (normOdometer_nonneg hne a)

/-- Stability of the final configuration when the origin has positive degree. -/
theorem final_le_one (hlf : IsLocallyFiniteMult m) (hne : (admissible m M).Nonempty)
    (hdeg0 : 0 < mdeg m 0) (a : ℤ) : sandpileFinal m M a ≤ 1 := by
  have hadm := (normOdometer_mem_admissible hlf hne).2 a
  have hd0 : (mdeg m 0 : ℝ) ≠ 0 := by exact_mod_cast hdeg0.ne'
  have hd : 0 ≤ (mdeg m a : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hadm hd
  unfold sandpileFinal
  by_cases ha : a = 0
  · subst a
    simp only [diracZero, ite_true, mul_one] at hmul ⊢
    have hid : (mdeg m 0 : ℝ)⁻¹ * (mdeg m 0 : ℝ) = 1 := inv_mul_cancel₀ hd0
    have hcancel : (mdeg m 0 : ℝ)⁻¹ * M * (mdeg m 0 : ℝ) = M := by
      calc
        _ = ((mdeg m 0 : ℝ)⁻¹ * (mdeg m 0 : ℝ)) * M := by ring
        _ = M := by rw [hid, one_mul]
    rw [add_mul, hcancel, hid] at hmul
    nlinarith
  · simp only [diracZero, ite_eq_right ha, mul_zero, zero_add] at hmul ⊢
    have hinv : (mdeg m a : ℝ)⁻¹ * (mdeg m a : ℝ) ≤ 1 := by
      by_cases hz : mdeg m a = 0
      · simp [hz]
      · have hz' : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hz
        rw [inv_mul_cancel₀ hz']
    nlinarith

/-- Complementarity: a site that emits positive mass finishes with mass one. -/
theorem final_eq_one_of_normOdometer_pos (hlf : IsLocallyFiniteMult m)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) {a : ℤ} (ha : 0 < sandpileNormOdometer m M a) :
    sandpileFinal m M a = 1 := by
  let u := sandpileNormOdometer m M
  let c : ℤ → ℝ := fun b => (mdeg m 0 : ℝ)⁻¹ * M * diracZero b
  let r : ℤ → ℝ := fun b => (mdeg m b : ℝ)⁻¹ - c b
  have hu := normOdometer_mem_admissible hlf hne
  have hulap : ∀ b, mLaplacian m u b ≤ r b := by
    intro b
    dsimp [r, c, u]
    linarith [hu.2 b]
  have heq : mLaplacian m u a = r a := by
    refine le_antisymm (hulap a) ?_
    by_contra hn
    have hgap : mLaplacian m u a < r a := lt_of_not_ge hn
    let η := min (r a - mLaplacian m u a) (u a)
    have hη : 0 < η := lt_min (by linarith) ha
    let v : ℤ → ℝ := fun b => if b = a then u b - η else u b
    have hv : v ∈ admissible m M := by
      refine ⟨fun b => ?_, fun b => ?_⟩
      · dsimp [v]
        split_ifs with hba
        · subst b
          have := min_le_right (r a - mLaplacian m u a) (u a)
          linarith
        · exact hu.1 b
      · have hD : (0 : ℝ) < mdeg m b := by exact_mod_cast hdeg b
        have hlap : lapSum hlf v b ≤ r b * (mdeg m b : ℝ) := by
          by_cases hba : b = a
          · subst b
            have hsum : lapSum hlf v a = lapSum hlf u a + η * (mdeg m a : ℝ) := by
              unfold lapSum
              rw [mdeg_cast_eq hlf a, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun d hd => ?_
              have hda : d ≠ a := by
                rintro rfl
                exact (mem_nbrs hlf).1 hd (hloop d)
              simp only [v, ite_eq_right hda, ite_eq_left rfl]
              ring
            rw [hsum, ← mLaplacian_mul_mdeg hlf]
            have := min_le_left (r a - mLaplacian m u a) (u a)
            nlinarith
          · have hle : lapSum hlf v b ≤ lapSum hlf u b := by
              refine lapSum_le_lapSum hlf (fun d _ => ?_) (by simp [v, hba])
              dsimp [v]
              split_ifs <;> linarith
            exact le_trans hle (lapSum_le_of_mLaplacian_le hlf (hulap b))
        have hvb : mLaplacian m v b ≤ r b := by
          rw [mLaplacian_eq_div hlf, div_le_iff₀ hD]
          exact hlap
        dsimp [r, c] at hvb
        linarith
    have hmin := normOdometer_le v hv a
    simp only [v, ite_eq_left rfl] at hmin
    linarith
  have hd0 : (mdeg m 0 : ℝ) ≠ 0 := by exact_mod_cast (hdeg 0).ne'
  have hda : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast (hdeg a).ne'
  unfold sandpileFinal
  change M * diracZero a + (mdeg m a : ℝ) * mLaplacian m u a = 1
  rw [heq]
  dsimp [r, c]
  by_cases ha0 : a = 0
  · subst a
    simp only [diracZero, ite_true, mul_one]
    field_simp
    ring
  · simp [diracZero, ha0, hda]

theorem final_nonneg (hlf : IsLocallyFiniteMult m) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m M).Nonempty) (hM : 0 ≤ M) (a : ℤ) :
    0 ≤ sandpileFinal m M a := by
  by_cases ha : 0 < sandpileNormOdometer m M a
  · rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg hne ha]
    norm_num
  · have hz : sandpileNormOdometer m M a = 0 :=
      le_antisymm (not_lt.mp ha) (normOdometer_nonneg hne a)
    have hsum : 0 ≤ lapSum hlf (sandpileNormOdometer m M) a := by
      unfold lapSum
      apply Finset.sum_nonneg
      intro b hb
      rw [hz, sub_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (normOdometer_nonneg hne b)
    have hlap : 0 ≤ mLaplacian m (sandpileNormOdometer m M) a := by
      rw [mLaplacian_eq_div hlf]
      exact div_nonneg hsum (Nat.cast_nonneg _)
    have hdir : 0 ≤ diracZero a := by
      simp [diracZero]; split_ifs <;> norm_num
    unfold sandpileFinal
    exact add_nonneg (mul_nonneg hM hdir) (mul_nonneg (Nat.cast_nonneg _) hlap)

theorem origin_mem_cluster (hlf : IsLocallyFiniteMult m) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m M).Nonempty)
    (hM : 1 < M) : 0 ∈ sandpileCluster m M := by
  have ha : 0 < sandpileNormOdometer m M 0 := by
    by_contra hn
    have hz : sandpileNormOdometer m M 0 = 0 :=
      le_antisymm (not_lt.mp hn) (normOdometer_nonneg hne 0)
    have hsum : 0 ≤ lapSum hlf (sandpileNormOdometer m M) 0 := by
      unfold lapSum
      apply Finset.sum_nonneg
      intro b hb
      rw [hz, sub_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (normOdometer_nonneg hne b)
    have hlap : 0 ≤ mLaplacian m (sandpileNormOdometer m M) 0 := by
      rw [mLaplacian_eq_div hlf]
      exact div_nonneg hsum (Nat.cast_nonneg _)
    have hf := final_le_one hlf hne (hdeg 0) 0
    simp only [sandpileFinal, diracZero, ite_true, mul_one] at hf
    have hmul := mul_nonneg (Nat.cast_nonneg (mdeg m 0)) hlap
    linarith
  change 0 < sandpileFinal m M 0
  rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg hne ha]
  norm_num

/-- Conservation on any finite set containing the origin, the support of the
odometer, and all its neighbors. -/
theorem sum_final_eq_mass (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (s : Finset ℤ) (h0 : (0 : ℤ) ∈ s)
    (hout : ∀ a ∉ s, sandpileNormOdometer m M a = 0)
    (hclosed : ∀ a ∈ s, ∀ b ∉ s, m a b ≠ 0 → sandpileNormOdometer m M a = 0) :
    ∑ a ∈ s, sandpileFinal m M a = M := by
  classical
  let : DecidableEq ℤ := Classical.decEq ℤ
  have hsum : ∑ a ∈ s, lapSum hlf (sandpileNormOdometer m M) a = 0 := by
    rw [sum_lapSum_eq_flux hlf hsymm]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    have hb' := Finset.mem_filter.mp hb
    rw [hout b hb'.2, hclosed a ha b hb'.2 ((mem_nbrs hlf).1 hb'.1)]
    simp
  simp only [sandpileFinal, Finset.sum_add_distrib]
  have hmass : ∑ a ∈ s, M * diracZero a = M := by
    simp [diracZero, Finset.sum_ite_eq', h0]
  rw [hmass]
  have hlap : ∑ a ∈ s, (mdeg m a : ℝ) * mLaplacian m (sandpileNormOdometer m M) a = 0 := by
    calc
      _ = ∑ a ∈ s, lapSum hlf (sandpileNormOdometer m M) a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [mul_comm, mLaplacian_mul_mdeg hlf]
      _ = 0 := hsum
  rw [hlap, add_zero]

end MatedCRT.Sandpile
