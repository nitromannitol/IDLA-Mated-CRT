import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable

/-! # Green kernels of measurable random multigraphs -/

namespace MatedCRT.GreenEnvironment

open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal

/-- The edge measure depends measurably on the environment. -/
theorem measurable_edgeMeasure
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (j : ℤ) : Measurable (fun ω => edgeMeasure (M ω) j) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [edgeMeasure, Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  apply Measurable.tsum
  intro k
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
    (hM j k)).mul measurable_const

/-- The simple random walk one-step law depends measurably on the environment. -/
theorem measurable_srwStep
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (j : ℤ) : Measurable (fun ω => srwStep (M ω) j) := by
  let μ : Ω → Measure ℤ := fun ω => edgeMeasure (M ω) j
  have hμ : Measurable μ := measurable_edgeMeasure M hM j
  have hm : Measurable (fun ω => μ ω univ) := (Measure.measurable_coe MeasurableSet.univ).comp hμ
  have hgood : MeasurableSet {ω | μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤} :=
    ((hm (measurableSet_singleton 0)).compl).inter ((hm (measurableSet_singleton ⊤)).compl)
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hvalue : Measurable (fun ω => μ ω A) := (Measure.measurable_coe hA).comp hμ
  change Measurable (fun ω => (if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω)[|univ]
    else Measure.dirac j) A)
  have heq : (fun ω => (if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω)[|univ]
      else Measure.dirac j) A) =
      (fun ω => if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω univ)⁻¹ * μ ω A
      else (Measure.dirac j) A) := by
    funext ω
    split_ifs <;> simp [cond_apply MeasurableSet.univ]
  rw [heq]
  exact Measurable.ite hgood (hm.inv.mul hvalue) measurable_const

/-- Every finite path cylinder probability is measurable in the environment. -/
theorem measurable_srwLaw_cylinder
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    Measurable (fun ω => srwLaw (M ω) a {y | ∀ i ≤ n, y i = x i}) := by
  simp_rw [srwLaw_cylinder]
  refine measurable_const.mul (Finset.measurable_prod _ ?_)
  intro i hi
  exact (Measure.measurable_coe (measurableSet_singleton _)).comp
    (measurable_srwStep M hM (x i))

/-- Every finite-dimensional marginal of the walk law is measurable in the
environment. -/
theorem measurable_srwLaw_marginal
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (a : ℤ) (n : ℕ) :
    Measurable (fun ω => (srwLaw (M ω) a).map
      (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ))) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hres : Measurable (Preorder.frestrictLe n :
      (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) := Preorder.measurable_frestrictLe n
  simp_rw [Measure.map_apply hres hA]
  have heq : (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' A =
      ⋃ x : A, (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1} := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    constructor
    · intro hy
      exact ⟨⟨Preorder.frestrictLe n y, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      simp [hx]
  have hdisj : Pairwise (Disjoint on fun x : A =>
      (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1}) := by
    intro x y hxy
    apply Disjoint.preimage
    exact disjoint_singleton.mpr (fun h => hxy (Subtype.ext h))
  have hsets : ∀ x : A, MeasurableSet ((Preorder.frestrictLe n :
      (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1}) := fun x =>
    (measurableSet_singleton _).preimage (Preorder.measurable_frestrictLe n)
  simp_rw [heq, measure_iUnion hdisj hsets]
  apply Measurable.tsum
  intro x
  let z : ℕ → ℤ := fun i => if hi : i ≤ n then x.1 ⟨i, Finset.mem_Iic.mpr hi⟩ else 0
  have hc : (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1} =
      {y | ∀ i ≤ n, y i = z i} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · intro hy i hi
      have hv := congrFun hy ⟨i, Finset.mem_Iic.mpr hi⟩
      simpa [Preorder.frestrictLe, z, hi] using hv
    · intro hy
      funext i
      have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.property
      simpa [Preorder.frestrictLe, z, hi] using hy i hi
  rw [hc]
  exact measurable_srwLaw_cylinder M hM a n z

/-- The full law of simple random walk is measurable in the environment. -/
theorem measurable_srwLaw
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (a : ℤ) : Measurable (fun ω => srwLaw (M ω) a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => Measurable (fun ω => srwLaw (M ω) a t))
    (s := measurableCylinders (fun _ : ℕ => ℤ)) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?_) (fun t mt ht => ?_)
    (fun f disf mf hf => ?_)
  · obtain ⟨N, A, hA, rfl⟩ : ∃ N A, MeasurableSet A ∧ t = cylinder (Finset.Iic N) A := by
      simpa [measurableCylinders_nat] using ht
    have hm := (Measure.measurable_coe hA).comp (measurable_srwLaw_marginal M hM a N)
    have hres : Measurable (Preorder.frestrictLe N :
        (ℕ → ℤ) → ((i : Finset.Iic N) → ℤ)) := Preorder.measurable_frestrictLe N
    change Measurable (fun ω => ((srwLaw (M ω) a).map
      (Preorder.frestrictLe N : (ℕ → ℤ) → ((i : Finset.Iic N) → ℤ))) A) at hm
    simp_rw [Measure.map_apply hres hA] at hm
    simpa [cylinder, Preorder.frestrictLe] using hm
  · simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

/-- Green functions for a measurable random vertex set are measurable. -/
theorem measurable_greenFn
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (V : Ω → Set ℤ) (hV : Measurable V) (a b : ℤ) :
    Measurable (fun ω => greenFn (M ω) (V ω) a b) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (M ω) a, measurable_srwLaw M hM a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw _ _⟩
  have h := (measurable_visitsBeforeExit_random_set V hV b).lintegral_kernel_prod_right' (κ := κ)
  exact h.ennreal_toReal

/-- The degree-normalized Green kernel for a measurable random vertex set
is measurable. -/
theorem measurable_greenKernel
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (V : Ω → Set ℤ) (hV : Measurable V) (a b : ℤ) :
    Measurable (fun ω => greenKernel (M ω) (V ω) a b) := by
  unfold greenKernel
  exact (measurable_greenFn M hM V hV a b).div
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_finsum_nat (fun ω k => M ω b k) (fun k => hM b k)))

end MatedCRT.GreenEnvironment
