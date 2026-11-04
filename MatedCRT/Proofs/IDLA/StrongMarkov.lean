import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.WalkPotential.Markov

/-!
# The strong Markov property of simple random walk at a hitting time

For simple random walk on any multigraph `m` on `ℤ` (law `srwLaw m z`), a set `D`, a weight `h : ℤ → [0, ∞]` and a
measurable functional `F ≥ 0` of paths, on the event `{τ_D = k}`:
`E^z[h(X_k) F(θ_k X); τ_D = k] = E^z[h(X_k) E^{X_k}[F]; τ_D = k]` (`lintegral_hitTime_eq`), where `θ_k` is the shift
of the path by `k` (`pathShift`). The proof is by induction on `k`, through the Markov property at the first step
(`srwLaw_eq_srwFirstStepLaw`, MatedCRT/Proofs/WalkPotential/Markov.lean).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The path shifted by `k`: `(θ_k x)(n) = x(n + k)`. -/
def pathShift (k : ℕ) (x : ℕ → ℤ) : ℕ → ℤ := fun n => x (n + k)

theorem measurable_pathShift (k : ℕ) : Measurable (pathShift k) :=
  Measurable.of_eval fun n => measurable_pi_apply (n + k)

@[simp] theorem pathShift_zero (x : ℕ → ℤ) : pathShift 0 x = x := rfl

theorem pathShift_succ_pathCons (k : ℕ) (z : ℤ) (y : ℕ → ℤ) :
    pathShift (k + 1) (pathCons z y) = pathShift k y := by
  funext n
  rfl

/-- `m + k < T_O(x)` iff `m < T_O(θ_k x)`, when the path stays in `O` up to time `k`. -/
theorem lt_vExitTime_add_iff {O : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (hk : ∀ j ≤ k, x j ∈ O) (m : ℕ) :
    ((m + k : ℕ) : ℕ∞) < vExitTime O x ↔ (m : ℕ∞) < vExitTime O (pathShift k x) := by
  rw [natCast_lt_vExitTime_iff, natCast_lt_vExitTime_iff]
  constructor
  · intro h i hi
    exact h (i + k) (by omega)
  · intro h j hj
    by_cases hjk : j ≤ k
    · exact hk j hjk
    · have h' := h (j - k) (by omega)
      have hjk' : j - k + k = j := Nat.sub_add_cancel (by omega)
      simp only [pathShift, hjk'] at h'
      exact h'

/-- Exit time of a path started inside `A`, through its tail. -/
theorem vExitTime_pathCons {A : Set ℤ} {z : ℤ} (hz : z ∈ A) (y : ℕ → ℤ) :
    vExitTime A (pathCons z y) = vExitTime A y + 1 := by
  induction hy : vExitTime A y using ENat.recTopCoe with
  | top =>
    rw [top_add, vExitTime_eq_top_iff]
    have h := vExitTime_eq_top_iff.1 hy
    intro n
    cases n with
    | zero => exact hz
    | succ n => exact h n
  | coe j =>
    rw [← Nat.cast_succ, vExitTime_eq_natCast_iff, natCast_lt_vExitTime_iff]
    refine ⟨fun h => apply_vExitTime_not_mem hy (h (j + 1) le_rfl), fun i hi => ?_⟩
    cases i with
    | zero => exact hz
    | succ i =>
      exact mem_of_lt_vExitTime (x := y) (k := i)
        (by rw [hy]; exact_mod_cast Nat.lt_of_succ_lt_succ hi)

/-- A path started outside `A` exits at time `0`. -/
theorem vExitTime_eq_zero_of_not_mem {A : Set ℤ} {x : ℕ → ℤ} (hx : x 0 ∉ A) : vExitTime A x = 0 := by
  rw [← Nat.cast_zero, vExitTime_eq_natCast_iff, natCast_lt_vExitTime_iff]
  exact ⟨fun h => hx (h 0 le_rfl), fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- `τ_D(z, y) = k + 1` iff `z ∉ D` and `τ_D(y) = k`. -/
theorem vHitTime_pathCons_eq_succ_iff {D : Set ℤ} {z : ℤ} {y : ℕ → ℤ} {k : ℕ} :
    vHitTime D (pathCons z y) = ((k + 1 : ℕ) : ℕ∞) ↔ z ∉ D ∧ vHitTime D y = k := by
  unfold vHitTime
  by_cases hz : z ∈ D
  · have h0 : vExitTime Dᶜ (pathCons z y) = 0 := vExitTime_eq_zero_of_not_mem (by simpa using hz)
    have hne : (0 : ℕ∞) ≠ ((k + 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_zero, Ne, Nat.cast_inj]
      omega
    rw [h0]
    simp only [hz, not_true_eq_false, false_and, iff_false]
    exact hne
  · rw [vExitTime_pathCons (show z ∈ Dᶜ from hz)]
    simp only [hz, not_false_eq_true, true_and]
    induction vExitTime Dᶜ y using ENat.recTopCoe with
    | top =>
      rw [top_add]
      exact ⟨fun h => absurd h.symm (ENat.natCast_ne_top _), fun h => absurd h.symm (ENat.natCast_ne_top _)⟩
    | coe j =>
      rw [← Nat.cast_succ]
      simp only [Nat.cast_inj]
      omega

/-- `τ_D = 0` iff the path starts in `D`. -/
theorem vHitTime_eq_zero_iff {D : Set ℤ} {x : ℕ → ℤ} : vHitTime D x = ((0 : ℕ) : ℕ∞) ↔ x 0 ∈ D := by
  unfold vHitTime
  rw [vExitTime_eq_natCast_iff, natCast_lt_vExitTime_iff]
  constructor
  · rintro ⟨h, -⟩
    by_contra hx
    exact h fun j hj => by
      rw [Nat.le_zero.1 hj]
      exact hx
  · intro hx
    exact ⟨fun h => h 0 le_rfl hx, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **Markov property at the first step**, for integrals: `E^z[f(X)] = ∫ E^b[f(z, Y)] p(z, db)`. -/
theorem lintegral_srwLaw_eq_firstStep (m : ℤ → ℤ → ℕ) (z : ℤ) {f : (ℕ → ℤ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂srwLaw m z = ∫⁻ b, ∫⁻ y, f (pathCons z y) ∂srwLaw m b ∂srwStep m z := by
  rw [srwLaw_eq_srwFirstStepLaw m z]
  unfold srwFirstStepLaw
  rw [Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [lintegral_map hf (measurable_pathCons z)]

theorem measurableSet_vHitTime_eq (D : Set ℤ) (k : ℕ) : MeasurableSet {x : ℕ → ℤ | vHitTime D x = k} :=
  measurable_vHitTime D (measurableSet_singleton _)

/-- **Strong Markov property at the hitting time of `D`**: for `h : ℤ → [0, ∞]` and measurable `F ≥ 0`,
`E^z[h(X_k) F(θ_k X); τ_D = k] = E^z[h(X_k) E^{X_k}[F]; τ_D = k]`. -/
theorem lintegral_hitTime_eq (m : ℤ → ℤ → ℕ) (D : Set ℤ) (h : ℤ → ℝ≥0∞) {F : (ℕ → ℤ) → ℝ≥0∞}
    (hF : Measurable F) (k : ℕ) (z : ℤ) :
    ∫⁻ x, {x | vHitTime D x = k}.indicator (fun x => h (x k) * F (pathShift k x)) x ∂srwLaw m z =
      ∫⁻ x, {x | vHitTime D x = k}.indicator (fun x => h (x k) * ∫⁻ y, F y ∂srwLaw m (x k)) x
        ∂srwLaw m z := by
  induction k generalizing z with
  | zero =>
    have hae := srwLaw_ae_start m z
    by_cases hz : z ∈ D
    · have hL : ∀ᵐ x ∂srwLaw m z, {x | vHitTime D x = ((0 : ℕ) : ℕ∞)}.indicator
          (fun x => h (x 0) * F (pathShift 0 x)) x = h z * F x := by
        filter_upwards [hae] with x hx
        have hmem : x ∈ {x | vHitTime D x = ((0 : ℕ) : ℕ∞)} := vHitTime_eq_zero_iff.2 (hx ▸ hz)
        rw [indicator_of_mem hmem, hx, pathShift_zero]
      have hR : ∀ᵐ x ∂srwLaw m z, {x | vHitTime D x = ((0 : ℕ) : ℕ∞)}.indicator
          (fun x => h (x 0) * ∫⁻ y, F y ∂srwLaw m (x 0)) x = h z * ∫⁻ y, F y ∂srwLaw m z := by
        filter_upwards [hae] with x hx
        have hmem : x ∈ {x | vHitTime D x = ((0 : ℕ) : ℕ∞)} := vHitTime_eq_zero_iff.2 (hx ▸ hz)
        rw [indicator_of_mem hmem, hx]
      rw [lintegral_congr_ae hL, lintegral_congr_ae hR, lintegral_const_mul _ hF, lintegral_const,
        measure_univ, mul_one]
    · have h0 : ∀ G : (ℕ → ℤ) → ℝ≥0∞, ∀ᵐ x ∂srwLaw m z,
          {x | vHitTime D x = ((0 : ℕ) : ℕ∞)}.indicator G x = 0 := by
        intro G
        filter_upwards [hae] with x hx
        have hmem : x ∉ {x | vHitTime D x = ((0 : ℕ) : ℕ∞)} := fun hm =>
          hz (hx ▸ vHitTime_eq_zero_iff.1 hm)
        exact indicator_of_notMem hmem _
      rw [lintegral_congr_ae (h0 _), lintegral_congr_ae (h0 _)]
  | succ k ih =>
    have hmeasL : Measurable ({x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)}.indicator
        (fun x => h (x (k + 1)) * F (pathShift (k + 1) x))) :=
      (((measurable_of_countable h).comp (measurable_pi_apply (k + 1))).mul
        (hF.comp (measurable_pathShift (k + 1)))).indicator (measurableSet_vHitTime_eq D (k + 1))
    have hmeasR : Measurable ({x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)}.indicator
        (fun x => h (x (k + 1)) * ∫⁻ y, F y ∂srwLaw m (x (k + 1)))) :=
      (((measurable_of_countable h).comp (measurable_pi_apply (k + 1))).mul
        ((measurable_of_countable fun b => ∫⁻ y, F y ∂srwLaw m b).comp (measurable_pi_apply (k + 1)))).indicator
        (measurableSet_vHitTime_eq D (k + 1))
    rw [lintegral_srwLaw_eq_firstStep m z hmeasL, lintegral_srwLaw_eq_firstStep m z hmeasR]
    refine lintegral_congr fun b => ?_
    by_cases hz : z ∈ D
    · have hnot : ∀ y : ℕ → ℤ, pathCons z y ∉ {x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)} :=
        fun y hy => (vHitTime_pathCons_eq_succ_iff.1 hy).1 hz
      simp only [indicator_of_notMem (hnot _)]
    · have hiff : ∀ y : ℕ → ℤ, pathCons z y ∈ {x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)} ↔
          y ∈ {x : ℕ → ℤ | vHitTime D x = k} := fun y => by
        show vHitTime D (pathCons z y) = ((k + 1 : ℕ) : ℕ∞) ↔ vHitTime D y = k
        rw [vHitTime_pathCons_eq_succ_iff]
        exact and_iff_right hz
      have hL : ∀ y : ℕ → ℤ,
          {x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)}.indicator
            (fun x => h (x (k + 1)) * F (pathShift (k + 1) x)) (pathCons z y) =
          {x : ℕ → ℤ | vHitTime D x = k}.indicator (fun x => h (x k) * F (pathShift k x)) y := by
        intro y
        by_cases hy : y ∈ {x : ℕ → ℤ | vHitTime D x = k}
        · simp only [indicator_of_mem ((hiff y).2 hy), indicator_of_mem hy, pathShift_succ_pathCons,
            pathCons_succ]
        · rw [indicator_of_notMem (fun h' => hy ((hiff y).1 h')), indicator_of_notMem hy]
      have hR : ∀ y : ℕ → ℤ,
          {x : ℕ → ℤ | vHitTime D x = ((k + 1 : ℕ) : ℕ∞)}.indicator
            (fun x => h (x (k + 1)) * ∫⁻ y, F y ∂srwLaw m (x (k + 1))) (pathCons z y) =
          {x : ℕ → ℤ | vHitTime D x = k}.indicator (fun x => h (x k) * ∫⁻ y, F y ∂srwLaw m (x k)) y := by
        intro y
        by_cases hy : y ∈ {x : ℕ → ℤ | vHitTime D x = k}
        · simp only [indicator_of_mem ((hiff y).2 hy), indicator_of_mem hy, pathCons_succ]
        · rw [indicator_of_notMem (fun h' => hy ((hiff y).1 h')), indicator_of_notMem hy]
      simp only [hL, hR]
      exact ih b

end MatedCRT
