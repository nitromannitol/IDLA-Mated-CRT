import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# Simple random walk on a multigraph: the Markov property at the first step

For an edge multiplicity `m : ℤ → ℤ → ℕ` (any multigraph on `ℤ`, no hypothesis), the law `srwLaw m a` of simple random
walk started at `a` (Ionescu-Tulcea, `Kernel.traj`) satisfies:

* `srwLaw_cylinder`: the cylinder probabilities
  `P^a[X_0 = x_0, …, X_n = x_n] = 1{x_0 = a} ∏_{i < n} p(x_i, x_{i+1})`, `p(c, d) = srwStep m c {d}`;
* `srwLaw_eq_srwFirstStepLaw`: the Markov property at time `1`: `P^a` is the law of `(a, Y)` where `Y` is simple random
  walk started from a step `X_1 ∼ p(a, ·)`, i.e. `P^a[E] = ∫ P^b[(a, ·) ∈ E] p(a, db)` (`srwLaw_apply_eq_lintegral`);
* `lintegral_srwStep`: at a vertex of finite positive degree, `∫ f dp(a, ·) = deg(a)⁻¹ ∑_{b ∼ a} m(a,b) f(b)`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The path `(a, x₀, x₁, …)`: the path `x` preceded by the site `a`. -/
def pathCons (a : ℤ) (x : ℕ → ℤ) : ℕ → ℤ
  | 0 => a
  | n + 1 => x n

@[simp] theorem pathCons_zero (a : ℤ) (x : ℕ → ℤ) : pathCons a x 0 = a := rfl

@[simp] theorem pathCons_succ (a : ℤ) (x : ℕ → ℤ) (n : ℕ) : pathCons a x (n + 1) = x n := rfl

theorem measurable_pathCons (a : ℤ) : Measurable (pathCons a) := by
  refine measurable_pi_iff.2 fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

theorem srwHistoryKernel_apply (m : ℤ → ℤ → ℕ) (n : ℕ) (y : (i : Finset.Iic n) → ℤ) :
    srwHistoryKernel m n y = srwStep m (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) := rfl

theorem frestrictLe_eq_iff {n : ℕ} {x y : ℕ → ℤ} :
    Preorder.frestrictLe n y = Preorder.frestrictLe n x ↔ ∀ i ≤ n, y i = x i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.2 hi⟩
  · intro h
    funext i
    obtain ⟨i, hi⟩ := i
    exact h i (Finset.mem_Iic.1 hi)

theorem cylinder_eq_preimage (n : ℕ) (x : ℕ → ℤ) :
    {y : ℕ → ℤ | ∀ i ≤ n, y i = x i} =
      (Preorder.frestrictLe n : (ℕ → ℤ) → (Finset.Iic n → ℤ)) ⁻¹' {Preorder.frestrictLe n x} := by
  ext y
  show (∀ i ≤ n, y i = x i) ↔
    Preorder.frestrictLe n y ∈ ({Preorder.frestrictLe n x} : Set (Finset.Iic n → ℤ))
  rw [mem_singleton_iff, frestrictLe_eq_iff]

theorem measurableSet_cylinder (n : ℕ) (x : ℕ → ℤ) : MeasurableSet {y : ℕ → ℤ | ∀ i ≤ n, y i = x i} := by
  rw [cylinder_eq_preimage]
  exact Preorder.measurable_frestrictLe n (measurableSet_singleton _)

/-- The finite dimensional distributions of simple random walk (Ionescu-Tulcea partial trajectories): the probability
of the history `(x_0, …, x_n)` is `1{x_0 = a} ∏_{i < n} p(x_i, x_{i+1})`. -/
theorem partialTraj_srw_singleton (m : ℤ → ℤ → ℕ) (n : ℕ) (x₀ : (i : Finset.Iic 0) → ℤ) (x : ℕ → ℤ) :
    Kernel.partialTraj (X := fun _ => ℤ) (srwHistoryKernel m) 0 n x₀ {Preorder.frestrictLe n x} =
      (if x 0 = x₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩ then 1 else 0) *
        ∏ i ∈ Finset.range n, srwStep m (x i) {x (i + 1)} := by
  induction n with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
      Finset.range_zero, Finset.prod_empty, mul_one]
    have key : x₀ = Preorder.frestrictLe 0 x ↔ x 0 = x₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
      constructor
      · rintro rfl
        rfl
      · intro h
        funext i
        obtain ⟨i, hi⟩ := i
        obtain rfl : i = 0 := Nat.le_zero.1 (Finset.mem_Iic.1 hi)
        exact h.symm
    split_ifs with h
    · rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 (key.2 h))]
      rfl
    · exact Set.indicator_apply_eq_zero.2 fun hx => absurd (key.1 (Set.mem_singleton_iff.1 hx)) h
  | succ n ih =>
    have hIP : Measurable (IicProdIoc (X := fun _ : ℕ => ℤ) n (n + 1)) :=
      measurable_of_countable _
    rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n), Kernel.map_apply _ hIP,
      Measure.map_apply hIP (measurableSet_singleton _)]
    have hpre : IicProdIoc (X := fun _ : ℕ => ℤ) n (n + 1) ⁻¹' {Preorder.frestrictLe (n + 1) x} =
        {Preorder.frestrictLe n x} ×ˢ {fun i : Finset.Ioc n (n + 1) => x i} := by
      ext ⟨y₁, y₂⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
      constructor
      · intro h
        refine ⟨funext fun i => ?_, funext fun i => ?_⟩
        · have hi : (i : ℕ) ≤ n := Finset.mem_Iic.1 i.2
          have := congrFun h ⟨(i : ℕ), Finset.mem_Iic.2 (hi.trans n.le_succ)⟩
          rw [IicProdIoc_def] at this
          simpa [hi, Preorder.frestrictLe, Finset.restrict] using this
        · have hi := Finset.mem_Ioc.1 i.2
          have := congrFun h ⟨(i : ℕ), Finset.mem_Iic.2 hi.2⟩
          rw [IicProdIoc_def] at this
          simpa [not_le.2 hi.1, Preorder.frestrictLe, Finset.restrict] using this
      · rintro ⟨rfl, rfl⟩
        funext i
        rw [IicProdIoc_def]
        by_cases hi : (i : ℕ) ≤ n
        · simp [hi, Preorder.frestrictLe, Finset.restrict]
        · simp [hi, Preorder.frestrictLe, Finset.restrict]
    have hps : ∀ (c : ℤ) (i : Finset.Ioc n (n + 1)),
        MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℤ) n c i = c := by
      intro c i
      simp [MeasurableEquiv.piSingleton]
    have hpre2 : MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℤ) n ⁻¹'
        {fun i : Finset.Ioc n (n + 1) => x i} = {x (n + 1)} := by
      ext c
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have := congrFun h ⟨n + 1, Finset.mem_Ioc.2 ⟨n.lt_succ_self, le_rfl⟩⟩
        rw [hps] at this
        exact this
      · intro h
        funext i
        rw [hps, h]
        have hi := Finset.mem_Ioc.1 i.2
        have : (i : ℕ) = n + 1 := by omega
        show x (n + 1) = x (i : ℕ)
        rw [this]
    have hint : ∀ y : (i : Finset.Iic n) → ℤ,
        (Kernel.id ×ₖ (srwHistoryKernel m n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℤ) n)) y
          ({Preorder.frestrictLe n x} ×ˢ {fun i : Finset.Ioc n (n + 1) => x i}) =
        Set.indicator {Preorder.frestrictLe n x} (fun _ => srwStep m (x n) {x (n + 1)}) y := by
      intro y
      rw [Kernel.prod_apply_prod, Kernel.id_apply, Kernel.map_apply _ (MeasurableEquiv.measurable _),
        MeasurableEquiv.map_apply, hpre2, Measure.dirac_apply' _ (measurableSet_singleton _),
        srwHistoryKernel_apply]
      by_cases hy : y = Preorder.frestrictLe n x
      · subst hy
        simp only [Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
        rfl
      · simp [hy]
    rw [hpre, Kernel.comp_apply,
      Measure.bind_apply ((measurableSet_singleton _).prod (measurableSet_singleton _))
        (Kernel.measurable _).aemeasurable,
      lintegral_congr hint, lintegral_indicator_const (measurableSet_singleton _), ih,
      Finset.prod_range_succ]
    ring

/-- The cylinder probabilities of simple random walk:
`P^a[X_i = x_i, i ≤ n] = 1{x_0 = a} ∏_{i < n} p(x_i, x_{i+1})`. -/
theorem srwLaw_cylinder (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    srwLaw m a {y | ∀ i ≤ n, y i = x i} =
      (if x 0 = a then 1 else 0) * ∏ i ∈ Finset.range n, srwStep m (x i) {x (i + 1)} := by
  have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => ℤ) (κ := srwHistoryKernel m) 0 n (fun _ => a)
  have := congrArg (fun μ : Measure ((i : Finset.Iic n) → ℤ) => μ {Preorder.frestrictLe n x}) h
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _)] at this
  rw [cylinder_eq_preimage]
  unfold srwLaw
  rw [this, partialTraj_srw_singleton]

/-- The law of `(a, Y)`, where `Y` is simple random walk started from a step of the walk from `a`. -/
noncomputable def srwFirstStepLaw (m : ℤ → ℤ → ℕ) (a : ℤ) : Measure (ℕ → ℤ) :=
  (srwStep m a).bind fun b => (srwLaw m b).map (pathCons a)

theorem srwFirstStepLaw_apply (m : ℤ → ℤ → ℕ) (a : ℤ) {E : Set (ℕ → ℤ)} (hE : MeasurableSet E) :
    srwFirstStepLaw m a E = ∫⁻ b, srwLaw m b (pathCons a ⁻¹' E) ∂srwStep m a := by
  unfold srwFirstStepLaw
  rw [Measure.bind_apply hE (measurable_of_countable _).aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [Measure.map_apply (measurable_pathCons a) hE]

theorem pathCons_preimage_cylinder_zero (a : ℤ) (x : ℕ → ℤ) :
    pathCons a ⁻¹' {y | ∀ i ≤ 0, y i = x i} = if x 0 = a then univ else ∅ := by
  ext y
  split_ifs with h
  · simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true]
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    exact h.symm
  · simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hall
    exact h (hall 0 le_rfl).symm

theorem pathCons_preimage_cylinder_succ (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    pathCons a ⁻¹' {y | ∀ i ≤ n + 1, y i = x i} =
      if x 0 = a then {y | ∀ i ≤ n, y i = x (i + 1)} else ∅ := by
  ext y
  split_ifs with h
  · simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · intro hall i hi
      exact hall (i + 1) (by omega)
    · intro hall i hi
      cases i with
      | zero => exact h.symm
      | succ i => exact hall i (by omega)
  · simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hall
    exact h (hall 0 (Nat.zero_le _)).symm

theorem srwFirstStepLaw_cylinder (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    srwFirstStepLaw m a {y | ∀ i ≤ n, y i = x i} =
      (if x 0 = a then 1 else 0) * ∏ i ∈ Finset.range n, srwStep m (x i) {x (i + 1)} := by
  rw [srwFirstStepLaw_apply m a (measurableSet_cylinder n x)]
  cases n with
  | zero =>
    rw [pathCons_preimage_cylinder_zero]
    split_ifs with h
    · simp
    · simp
  | succ n =>
    rw [pathCons_preimage_cylinder_succ]
    split_ifs with h
    · have hb : ∀ b, srwLaw m b {y | ∀ i ≤ n, y i = x (i + 1)} =
          (if x 1 = b then 1 else 0) * ∏ i ∈ Finset.range n, srwStep m (x (i + 1)) {x (i + 1 + 1)} :=
        fun b => srwLaw_cylinder m b n (fun i => x (i + 1))
      have hind : ∀ b, (if x 1 = b then (1 : ℝ≥0∞) else 0) *
          ∏ i ∈ Finset.range n, srwStep m (x (i + 1)) {x (i + 1 + 1)} =
          Set.indicator {x 1} (fun _ => ∏ i ∈ Finset.range n, srwStep m (x (i + 1)) {x (i + 1 + 1)}) b := by
        intro b
        by_cases hx : x 1 = b
        · subst hx
          simp
        · simp [hx, Ne.symm hx]
      simp_rw [hb, hind]
      rw [lintegral_indicator_const (measurableSet_singleton _), Finset.prod_range_succ', one_mul,
        zero_add, h]
    · simp

/-- **Markov property at the first step**: `P^a` is the law of `(a, Y)` with `Y` simple random walk started from a
step `X_1 ∼ p(a, ·)`. Proved through the Ionescu-Tulcea uniqueness `Kernel.eq_traj` and the cylinder formula. -/
theorem srwLaw_eq_srwFirstStepLaw (m : ℤ → ℤ → ℕ) (a : ℤ) : srwLaw m a = srwFirstStepLaw m a := by
  let η : Kernel ((i : Finset.Iic 0) → ℤ) (ℕ → ℤ) :=
    (Kernel.ofFunOfCountable (srwFirstStepLaw m)).comap (fun x₀ => x₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _)
  have hη : η = Kernel.traj (X := fun _ => ℤ) (srwHistoryKernel m) 0 := by
    refine Kernel.eq_traj (X := fun _ => ℤ) (srwHistoryKernel m) η fun n => ?_
    refine Kernel.ext fun x₀ => Measure.ext_of_singleton fun z => ?_
    obtain ⟨x, rfl⟩ : ∃ x : ℕ → ℤ, Preorder.frestrictLe n x = z := by
      refine ⟨fun i => if h : i ≤ n then z ⟨i, Finset.mem_Iic.2 h⟩ else 0, ?_⟩
      funext i
      obtain ⟨i, hi⟩ := i
      show (if h : i ≤ n then z ⟨i, Finset.mem_Iic.2 h⟩ else 0) = z ⟨i, hi⟩
      rw [dite_eq_left_of_eq_true (eq_true (Finset.mem_Iic.1 hi))]
    rw [Kernel.map_apply _ (Preorder.measurable_frestrictLe n),
      Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _),
      ← cylinder_eq_preimage, partialTraj_srw_singleton]
    exact srwFirstStepLaw_cylinder m _ n x
  have := congrArg (fun κ : Kernel ((i : Finset.Iic 0) → ℤ) (ℕ → ℤ) => κ (fun _ => a)) hη
  exact this.symm

/-- **Markov property at the first step**: `P^a[E] = ∫ P^b[(a, ·) ∈ E] p(a, db)`. -/
theorem srwLaw_apply_eq_lintegral (m : ℤ → ℤ → ℕ) (a : ℤ) {E : Set (ℕ → ℤ)} (hE : MeasurableSet E) :
    srwLaw m a E = ∫⁻ b, srwLaw m b (pathCons a ⁻¹' E) ∂srwStep m a := by
  rw [srwLaw_eq_srwFirstStepLaw, srwFirstStepLaw_apply m a hE]

/-- The total mass of `∑_b m(a,b) δ_b` is the degree, for a locally finite multigraph. -/
theorem edgeMeasure_univ {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (a : ℤ) :
    edgeMeasure m a univ = mdeg m a := by
  unfold edgeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have hz : ∀ b ∉ nbrs hlf a, (m a b : ℝ≥0∞) = 0 := by
    intro b hb
    have : m a b = 0 := by
      by_contra h
      exact hb ((mem_nbrs hlf).2 h)
    simp [this]
  rw [tsum_eq_sum hz, mdeg_eq_sum_nbrs hlf a, Nat.cast_sum]

/-- At a vertex of finite positive degree, `∫ f dp(a, ·) = deg(a)⁻¹ ∑_{b ∼ a} m(a,b) f(b)`. -/
theorem lintegral_srwStep {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {a : ℤ} (hdeg : mdeg m a ≠ 0)
    (f : ℤ → ℝ≥0∞) :
    ∫⁻ b, f b ∂srwStep m a = ((mdeg m a : ℝ≥0∞))⁻¹ * ∑ b ∈ nbrs hlf a, (m a b : ℝ≥0∞) * f b := by
  have hu := edgeMeasure_univ hlf a
  have hcond : edgeMeasure m a univ ≠ 0 ∧ edgeMeasure m a univ ≠ ⊤ := by
    rw [hu]
    exact ⟨by exact_mod_cast hdeg, ENNReal.natCast_ne_top _⟩
  unfold srwStep
  split_ifs
  rw [ProbabilityTheory.cond, Measure.restrict_univ, lintegral_smul_measure, hu]
  congr 1
  unfold edgeMeasure
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  refine tsum_eq_sum fun b hb => ?_
  have : m a b = 0 := by
    by_contra h
    exact hb ((mem_nbrs hlf).2 h)
  simp [this]

end MatedCRT
