import MatedCRT.Proofs.WalkPotential.Markov

/-!
# The quenched walk law depends measurably on the multiplicities

For the edge multiplicity `m : ℤ → ℤ → ℕ` (the space of arrays carries the product `σ`-algebra) the law
`srwLaw m a` of simple random walk on the multigraph `m` started at `a` is a probability measure on the paths
`ℕ → ℤ`, and `m ↦ srwLaw m a` is measurable for the evaluation (Giry) `σ`-algebra of `Measure (ℕ → ℤ)`.
Proof: the one-step probabilities `srwStep m c {d} = m(c,d)/deg(c)` are measurable in `m`, hence so are the cylinder
probabilities `srwLaw_cylinder`, hence so are all measurable cylinders over a finite set of times (a countable sum
of cylinder probabilities), and a Dynkin argument extends this to every measurable set of paths.

This is the measurability of the *quenched law* `ω ↦ srwLaw (S.mult ε ω) k` of the walk on the random map, needed
to view the interpolated step-function law `P̃^ε` as a random element of a space of probability measures.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem edgeMeasure_singleton (m : ℤ → ℤ → ℕ) (a b : ℤ) : edgeMeasure m a {b} = (m a b : ℝ≥0∞) := by
  unfold edgeMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton b), tsum_eq_single b]
  · simp
  · intro c hc
    simp [Measure.dirac_apply' _ (measurableSet_singleton b), hc]

theorem edgeMeasure_univ_eq_tsum (m : ℤ → ℤ → ℕ) (a : ℤ) : edgeMeasure m a univ = ∑' c, (m a c : ℝ≥0∞) := by
  unfold edgeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp

open Classical in
/-- The one-step probabilities of simple random walk on the multigraph `m`:
`p(a, b) = m(a,b)/deg(a)` (`b = a` with probability one at a vertex of degree `0` or `∞`). -/
theorem srwStep_singleton (m : ℤ → ℤ → ℕ) (a b : ℤ) :
    srwStep m a {b} =
      if (∑' c, (m a c : ℝ≥0∞)) ≠ 0 ∧ (∑' c, (m a c : ℝ≥0∞)) ≠ ⊤ then
        (∑' c, (m a c : ℝ≥0∞))⁻¹ * (m a b : ℝ≥0∞) else if a = b then 1 else 0 := by
  unfold srwStep
  simp only [edgeMeasure_univ_eq_tsum]
  split_ifs with h h2
  · rw [cond_apply MeasurableSet.univ, univ_inter, edgeMeasure_singleton, edgeMeasure_univ_eq_tsum]
  · simp [Measure.dirac_apply' _ (measurableSet_singleton b), h2]
  · simp [Measure.dirac_apply' _ (measurableSet_singleton b), h2]

/-- The one-step probabilities are measurable functions of the multiplicity array. -/
theorem measurable_srwStep_singleton (a b : ℤ) :
    Measurable fun m : ℤ → ℤ → ℕ => srwStep m a {b} := by
  have hT : Measurable fun m : ℤ → ℤ → ℕ => ∑' c, (m a c : ℝ≥0∞) :=
    Measurable.tsum fun c =>
      (measurable_from_top (f := ((↑) : ℕ → ℝ≥0∞))).comp ((measurable_pi_apply c).comp (measurable_pi_apply a))
  have hm : Measurable fun m : ℤ → ℤ → ℕ => (m a b : ℝ≥0∞) :=
    (measurable_from_top (f := ((↑) : ℕ → ℝ≥0∞))).comp ((measurable_pi_apply b).comp (measurable_pi_apply a))
  simp_rw [srwStep_singleton]
  refine Measurable.ite ?_ (hT.inv.mul hm) measurable_const
  exact (hT (measurableSet_singleton (0 : ℝ≥0∞)).compl).inter (hT (measurableSet_singleton (⊤ : ℝ≥0∞)).compl)

/-- The cylinder probabilities of the walk are measurable in the multiplicity array. -/
theorem measurable_srwLaw_cylinder (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    Measurable fun m : ℤ → ℤ → ℕ => srwLaw m a {y | ∀ i ≤ n, y i = x i} := by
  simp_rw [srwLaw_cylinder]
  exact measurable_const.mul (Finset.measurable_prod _ fun i _ => measurable_srwStep_singleton (x i) (x (i + 1)))

/-- The extension of a finite history to a path (by `0` after time `n`). -/
def extendHistory (n : ℕ) (w : Finset.Iic n → ℤ) : ℕ → ℤ :=
  fun i => if h : i ≤ n then w ⟨i, Finset.mem_Iic.2 h⟩ else 0

theorem frestrictLe_extendHistory (n : ℕ) (w : Finset.Iic n → ℤ) :
    Preorder.frestrictLe n (extendHistory n w) = w := by
  funext i
  obtain ⟨i, hi⟩ := i
  simp [extendHistory, Preorder.frestrictLe, Finset.mem_Iic.1 hi]

theorem measurable_srwLaw_measurableCylinder (a : ℤ) (s : Finset ℕ) (S : Set (s → ℤ)) :
    Measurable fun m : ℤ → ℤ → ℕ => srwLaw m a (cylinder s S) := by
  classical
  set n : ℕ := s.sup id with hn
  have hle : ∀ i ∈ s, i ≤ n := fun i hi => Finset.le_sup (f := id) hi
  let B : Set (Finset.Iic n → ℤ) :=
    {w | (fun i : s => w ⟨i.1, Finset.mem_Iic.2 (hle i.1 i.2)⟩) ∈ S}
  have hcyl : cylinder s S = (Preorder.frestrictLe n : (ℕ → ℤ) → (Finset.Iic n → ℤ)) ⁻¹' B := by
    ext y
    exact Iff.rfl
  have hBm : MeasurableSet B := (Set.to_countable B).measurableSet
  have key : ∀ m : ℤ → ℤ → ℕ, srwLaw m a (cylinder s S) =
      ∑' w : Finset.Iic n → ℤ, B.indicator
        (fun w => srwLaw m a {y | ∀ i ≤ n, y i = extendHistory n w i}) w := by
    intro m
    rw [hcyl, ← Measure.map_apply (Preorder.measurable_frestrictLe n) hBm,
      ← Measure.tsum_indicator_apply_singleton _ B hBm]
    refine tsum_congr fun w => ?_
    by_cases hw : w ∈ B
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw,
        Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton w), 
        cylinder_eq_preimage, frestrictLe_extendHistory]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  simp_rw [key]
  refine Measurable.tsum fun w => ?_
  by_cases hw : w ∈ B
  · simp only [Set.indicator_of_mem hw]
    exact measurable_srwLaw_cylinder a n (extendHistory n w)
  · simp only [Set.indicator_of_notMem hw]
    exact measurable_const

/-- For every measurable set of paths, the probability of the set under the quenched walk law is a measurable
function of the multiplicity array. -/
theorem measurable_srwLaw_apply (a : ℤ) {t : Set (ℕ → ℤ)} (ht : MeasurableSet t) :
    Measurable fun m : ℤ → ℤ → ℕ => srwLaw m a t := by
  refine MeasurableSpace.induction_on_inter (C := fun t _ => Measurable fun m : ℤ → ℤ → ℕ => srwLaw m a t)
    (generateFrom_measurableCylinders (α := fun _ : ℕ => ℤ)).symm isPiSystem_measurableCylinders
    ?_ ?_ ?_ ?_ t ht
  · simp
  · intro t ht
    obtain ⟨s, S, -, rfl⟩ := (mem_measurableCylinders t).1 ht
    exact measurable_srwLaw_measurableCylinder a s S
  · intro t htm ih
    simp_rw [prob_compl_eq_one_sub htm]
    exact measurable_const.sub ih
  · intro f hd hfm ih
    simp_rw [measure_iUnion hd hfm]
    exact Measurable.tsum ih

/-- The quenched walk law `m ↦ srwLaw m a` is a Giry-measurable map of the multiplicity array. -/
theorem measurable_srwLaw (a : ℤ) : Measurable fun m : ℤ → ℤ → ℕ => srwLaw m a :=
  Measure.measurable_of_measurable_coe _ fun _ ht => measurable_srwLaw_apply a ht

/-- The quenched walk law as a probability measure on paths. -/
noncomputable def srwLawPM (m : ℤ → ℤ → ℕ) (a : ℤ) : ProbabilityMeasure (ℕ → ℤ) :=
  ⟨srwLaw m a, inferInstance⟩

theorem measurable_srwLawPM (a : ℤ) : Measurable fun m : ℤ → ℤ → ℕ => srwLawPM m a :=
  Measurable.subtype_mk (measurable_srwLaw a)

end MatedCRT
