import MatedCRT.Proofs.WalkPotential.ExitBeforeHit

/-!
# The expected exit time solves `Δ Q = -1` (eq:discrete-exit-laplacian)

For a locally finite multigraph `m` on `ℤ`, a set `A` and `a ∈ A` of positive degree, the Markov property at the first
step (`srwLaw_eq_srwFirstStepLaw`) gives `Q_A(a) = 1 + deg(a)⁻¹ ∑_{b ∼ a} m(a,b) Q_A(b)`
(`expectedExitTime_eq_one_add`). Hence, if `Q_A` is finite on `A`, its real values satisfy
`∑_{b ∼ a} m(a,b) (Q_A(b) - Q_A(a)) = -deg(a)` (`lapSum_expectedExitTime`). The proof of Lemma 3.1 uses this at
line 1049.
-/

namespace MatedCRT.Tightness

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The exit time is measurable. -/
theorem measurable_vExitTime_coe (A : Set ℤ) :
    Measurable fun x : ℕ → ℤ => ((vExitTime A x : ℕ∞) : ℝ≥0∞) := by
  have hfin : ∀ n : ℕ, MeasurableSet {x : ℕ → ℤ | vExitTime A x = n} := by
    intro n
    have h : {x : ℕ → ℤ | vExitTime A x = n} =
        (fun x : ℕ → ℤ => x n) ⁻¹' Aᶜ ∩ ⋂ k ∈ Finset.range n, (fun x : ℕ → ℤ => x k) ⁻¹' A := by
      ext x
      simp only [mem_ofPred_eq, vExitTime_eq_coe_iff, mem_inter_iff, mem_preimage, mem_compl_iff, mem_iInter,
        Finset.mem_range]
    rw [h]
    exact (measurable_pi_apply n (Set.to_countable _).measurableSet).inter
      (Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k (Set.to_countable _).measurableSet)
  have htop : MeasurableSet {x : ℕ → ℤ | vExitTime A x = ⊤} := by
    have h : {x : ℕ → ℤ | vExitTime A x = ⊤} = ⋂ n : ℕ, {x : ℕ → ℤ | vExitTime A x = n}ᶜ := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
      constructor
      · intro hx n hn
        rw [hx] at hn
        exact ENat.top_ne_natCast n hn
      · intro hx
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
        exact hx n hn.symm
    rw [h]
    exact MeasurableSet.iInter fun n => (hfin n).compl
  intro s _
  have h : (fun x : ℕ → ℤ => ((vExitTime A x : ℕ∞) : ℝ≥0∞)) ⁻¹' s =
      (⋃ n : ℕ, ⋃ (_ : (((n : ℕ∞) : ℝ≥0∞)) ∈ s), {x : ℕ → ℤ | vExitTime A x = n}) ∪
        ⋃ (_ : (((⊤ : ℕ∞) : ℝ≥0∞)) ∈ s), {x : ℕ → ℤ | vExitTime A x = ⊤} := by
    ext x
    simp only [mem_preimage, mem_union, mem_iUnion, mem_ofPred_eq, exists_prop]
    obtain h | h := eq_or_ne (vExitTime A x) ⊤
    · rw [h]
      constructor
      · intro hs
        exact Or.inr ⟨hs, rfl⟩
      · rintro (⟨i, -, hi⟩ | ⟨hs, -⟩)
        · exact absurd hi (ENat.top_ne_natCast i)
        · exact hs
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
      rw [← hn]
      constructor
      · intro hs
        exact Or.inl ⟨n, hs, rfl⟩
      · rintro (⟨i, hi, hni⟩ | ⟨-, hn'⟩)
        · rw [Nat.cast_inj.1 hni]
          exact hi
        · exact absurd hn'.symm (ENat.top_ne_natCast n)
  rw [h]
  exact (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hfin n).union
    (MeasurableSet.iUnion fun _ => htop)

/-- Prepending a site of `A` adds one step to the exit time from `A`. -/
theorem vExitTime_pathCons {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (y : ℕ → ℤ) :
    vExitTime A (pathCons a y) = vExitTime A y + 1 := by
  by_cases hy : ∃ n, y n ∉ A
  · have hne : vExitTime A y ≠ ⊤ := by
      unfold vExitTime
      split_ifs
      exact (ENat.top_ne_natCast _).symm
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
    obtain ⟨hyn, hlt⟩ := vExitTime_eq_coe_iff.1 hn.symm
    rw [← hn]
    have h1 : vExitTime A (pathCons a y) = ((n + 1 : ℕ) : ℕ∞) := by
      refine vExitTime_eq_coe_iff.2 ⟨hyn, fun k hk => ?_⟩
      cases k with
      | zero => exact ha
      | succ k => exact hlt k (by omega)
    rw [h1, Nat.cast_succ]
  · have h1 : vExitTime A y = ⊤ := by
      unfold vExitTime
      split_ifs
      rfl
    have h2 : vExitTime A (pathCons a y) = ⊤ := by
      unfold vExitTime
      split_ifs with h
      · exfalso
        obtain ⟨k, hk⟩ := h
        cases k with
        | zero => exact hk ha
        | succ k => exact hy ⟨k, hk⟩
      · rfl
    rw [h1, h2, top_add]

/-- **First-step analysis** of the expected exit time. -/
theorem expectedExitTime_eq_one_add {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {A : Set ℤ} {a : ℤ}
    (ha : a ∈ A) (hdeg : mdeg m a ≠ 0) :
    expectedExitTime m A a =
      1 + ((mdeg m a : ℝ≥0∞))⁻¹ * ∑ b ∈ nbrs hlf a, (m a b : ℝ≥0∞) * expectedExitTime m A b := by
  have hF := measurable_vExitTime_coe A
  have hstep : ∀ b, ∫⁻ x, ((vExitTime A x : ℕ∞) : ℝ≥0∞) ∂(srwLaw m b).map (pathCons a) =
      ∫⁻ y, ((vExitTime A y : ℕ∞) : ℝ≥0∞) ∂srwLaw m b + 1 := by
    intro b
    rw [lintegral_map hF (measurable_pathCons a)]
    have h : ∀ y, ((vExitTime A (pathCons a y) : ℕ∞) : ℝ≥0∞) = ((vExitTime A y : ℕ∞) : ℝ≥0∞) + 1 := by
      intro y
      rw [vExitTime_pathCons ha]
      simp
    rw [lintegral_congr fun y => h y, lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
      mul_one]
  have hint : expectedExitTime m A a = ∫⁻ b, (expectedExitTime m A b + 1) ∂srwStep m a := by
    unfold expectedExitTime
    rw [srwLaw_eq_srwFirstStepLaw, srwFirstStepLaw,
      Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
    exact lintegral_congr fun b => hstep b
  rw [hint, lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_srwStep hlf hdeg, add_comm]

/-- **eq:discrete-exit-laplacian**: if `Q_A` is finite on `A`, then `∑_{b ∼ a} m(a,b) (Q_A(b) - Q_A(a)) = -deg(a)` at
every `a ∈ A` of positive degree. -/
theorem lapSum_expectedExitTime {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {A : Set ℤ}
    (hfin : ∀ b ∈ A, expectedExitTime m A b ≠ ⊤) {a : ℤ} (ha : a ∈ A) (hdeg : mdeg m a ≠ 0) :
    lapSum hlf (fun b => (expectedExitTime m A b).toReal) a = -(mdeg m a : ℝ) := by
  have hnt : ∀ b, expectedExitTime m A b ≠ ⊤ := fun b => by
    by_cases hb : b ∈ A
    · exact hfin b hb
    · rw [expectedExitTime_eq_zero_of_not_mem m hb]
      exact ENNReal.zero_ne_top
  have hd : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hdeg
  have hd' : (mdeg m a : ℝ≥0∞) ≠ 0 := by exact_mod_cast hdeg
  have hterm : ∀ b ∈ nbrs hlf a, (m a b : ℝ≥0∞) * expectedExitTime m A b ≠ ⊤ :=
    fun b _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hnt b)
  have hsum_ne : ∑ b ∈ nbrs hlf a, (m a b : ℝ≥0∞) * expectedExitTime m A b ≠ ⊤ :=
    ENNReal.sum_ne_top.2 hterm
  have key := congrArg ENNReal.toReal (expectedExitTime_eq_one_add hlf ha hdeg)
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hd') hsum_ne),
    ENNReal.toReal_mul, ENNReal.toReal_sum hterm] at key
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_mul] at key
  have hS : ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (expectedExitTime m A b).toReal =
      (mdeg m a : ℝ) * ((expectedExitTime m A a).toReal - 1) := by
    rw [key, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  simp only [lapSum, mul_sub, Finset.sum_sub_distrib]
  rw [hS, ← Finset.sum_mul, ← mdeg_cast_eq hlf a]
  ring

end MatedCRT.Tightness
