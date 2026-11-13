import MatedCRT.Proofs.WalkPotential.Markov
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge

/-!
# Reversibility of simple random walk on a multigraph: `n`-step detailed balance

Simple random walk on a symmetric, locally finite multigraph `m : ℤ → ℤ → ℕ` is reversible with respect to the
degree measure `x ↦ deg(x)`. Writing `p_n(x, y) = P^x[X_n = y]` for the `n`-step transition probabilities,

* `mdeg_mul_srwStep_singleton`: one-step detailed balance `deg(x) p(x, y) = m(x, y)` (also at a vertex of degree
  `0`, where both sides vanish);
* `srwLaw_eval_succ`, `srwLaw_eval_succ'`: the Chapman-Kolmogorov equations
  `p_{n+1}(x, y) = ∑_z p(x, z) p_n(z, y) = ∑_z p_n(x, z) p(z, y)`;
* `mdeg_mul_srwLaw_eval_eq`: `n`-step detailed balance `deg(x) p_n(x, y) = deg(y) p_n(y, x)`;
* `sum_mdeg_mul_integral_comp_eval_symm`, `tsum_mdeg_mul_integral_comp_eval_symm`: for finitely supported
  `f, g : ℤ → ℝ`, the pairing `∑_x deg(x) f(x) E^x[g(X_n)]` is symmetric in `(f, g)`;
* the same identities for the mated-CRT map: the edge count `bmEdgeCount ε L R` of Definition 1.1 for a locally finite
  realization (`mdeg_mul_srwLaw_eval_eq_bmEdgeCount`, `tsum_mdeg_mul_integral_comp_eval_symm_bmEdgeCount`), and the
  map `S.mult ε ω` of an environment where it is locally finite (`mdeg_mul_srwLaw_eval_eq_mult`,
  `tsum_mdeg_mul_integral_comp_eval_symm_mult`).

This is the exact discrete reversibility identity used in the proof of Lemma 7.6 of Berestycki-Gwynne (2020).

Local finiteness is stated either as `IsLocallyFiniteMult m` (every vertex has finitely many neighbours) or, in the
form of the non-junk branch of `srwStep`, as `edgeMeasure m a univ ≠ ⊤` for every `a`; the two are equivalent
(`isLocallyFiniteMult_of_edgeMeasure_ne_top`, `edgeMeasure_univ_ne_top`). No positivity of the degrees is needed.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## Local finiteness -/

/-- The total mass of `∑_b m(a,b) δ_b` is the total edge multiplicity at `a`. -/
theorem edgeMeasure_univ_eq_tsum_mult (m : ℤ → ℤ → ℕ) (a : ℤ) :
    edgeMeasure m a univ = ∑' b, (m a b : ℝ≥0∞) := by
  unfold edgeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp

/-- A vertex whose edge measure has finite total mass has finitely many neighbours. -/
theorem isLocallyFiniteMult_of_edgeMeasure_ne_top {m : ℤ → ℤ → ℕ} (hfin : ∀ a, edgeMeasure m a univ ≠ ⊤) :
    IsLocallyFiniteMult m := by
  intro a
  have hsum : ∑' b, (m a b : ℝ≥0∞) ≠ ⊤ := by
    rw [← edgeMeasure_univ_eq_tsum_mult]
    exact hfin a
  refine (ENNReal.finite_const_le_of_tsum_ne_top hsum one_ne_zero).subset fun b hb => ?_
  simp only [mem_ofPred_eq] at hb ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.2 hb

/-- On a locally finite multigraph every edge measure is finite. -/
theorem edgeMeasure_univ_ne_top {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (a : ℤ) :
    edgeMeasure m a univ ≠ ⊤ := by
  rw [edgeMeasure_univ hlf a]
  exact ENNReal.natCast_ne_top _

/-! ## One-step detailed balance and the Chapman-Kolmogorov equations -/

/-- **One-step detailed balance.** `deg(x) p(x, y) = m(x, y)`; at a vertex of degree `0` both sides vanish. -/
theorem mdeg_mul_srwStep_singleton {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (x y : ℤ) :
    (mdeg m x : ℝ≥0∞) * srwStep m x {y} = m x y := by
  have hzero : y ∉ nbrs hlf x → m x y = 0 := fun hy => by
    by_contra hne
    exact hy ((mem_nbrs hlf).2 hne)
  by_cases hx : mdeg m x = 0
  · have hxy : m x y = 0 := hzero (by rw [nbrs_eq_empty_of_mdeg_eq_zero hlf hx]; exact Finset.notMem_empty y)
    simp [hx, hxy]
  · have h := lintegral_srwStep hlf hx (Set.indicator {y} 1)
    rw [lintegral_indicator_one (measurableSet_singleton y)] at h
    have hx0 : (mdeg m x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hx
    rw [h, ← mul_assoc, ENNReal.mul_inv_cancel hx0 (ENNReal.natCast_ne_top _), one_mul, Finset.sum_eq_single y]
    · rw [Set.indicator_of_mem (Set.mem_singleton y), Pi.one_apply, mul_one]
    · intro b _ hb
      rw [Set.indicator_of_notMem (show b ∉ ({y} : Set ℤ) from hb), mul_zero]
    · intro hy
      rw [hzero hy, Nat.cast_zero, zero_mul]

/-- The event `{X_n = y}` is measurable. -/
theorem measurableSet_eval_eq (n : ℕ) (y : ℤ) : MeasurableSet {ω : ℕ → ℤ | ω n = y} :=
  (measurable_pi_apply n : Measurable fun ω : ℕ → ℤ => ω n) (measurableSet_singleton y)

/-- The walk starts at its starting point: `p_0(x, y) = 1{y = x}`. -/
theorem srwLaw_eval_zero (m : ℤ → ℤ → ℕ) (x y : ℤ) :
    srwLaw m x {ω | ω 0 = y} = if y = x then 1 else 0 := by
  have hset : {ω : ℕ → ℤ | ω 0 = y} = {ω | ∀ i ≤ 0, ω i = (fun _ : ℕ => y) i} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h i hi
      obtain rfl := Nat.le_zero.1 hi
      exact h
    · intro h
      exact h 0 le_rfl
  rw [hset, srwLaw_cylinder]
  simp

/-- **Chapman-Kolmogorov, first step.** `p_{n+1}(x, y) = ∑_z p(x, z) p_n(z, y)`. -/
theorem srwLaw_eval_succ (m : ℤ → ℤ → ℕ) (n : ℕ) (x y : ℤ) :
    srwLaw m x {ω | ω (n + 1) = y} = ∑' z, srwStep m x {z} * srwLaw m z {ω | ω n = y} := by
  rw [srwLaw_apply_eq_lintegral m x (measurableSet_eval_eq (n + 1) y), lintegral_countable']
  refine tsum_congr fun z => ?_
  have hpre : pathCons x ⁻¹' {ω : ℕ → ℤ | ω (n + 1) = y} = {ω | ω n = y} := rfl
  rw [hpre]
  exact mul_comm _ _

/-- **Chapman-Kolmogorov, last step.** `p_{n+1}(x, y) = ∑_z p_n(x, z) p(z, y)`. -/
theorem srwLaw_eval_succ' (m : ℤ → ℤ → ℕ) (n : ℕ) (x y : ℤ) :
    srwLaw m x {ω | ω (n + 1) = y} = ∑' z, srwLaw m x {ω | ω n = z} * srwStep m z {y} := by
  induction n generalizing x y with
  | zero =>
    have h1 : ∑' z, srwStep m x {z} * srwLaw m z {ω | ω 0 = y} =
        srwStep m x {y} * srwLaw m y {ω | ω 0 = y} :=
      tsum_eq_single y fun z hz => by simp [srwLaw_eval_zero, Ne.symm hz]
    have h2 : ∑' z, srwLaw m x {ω | ω 0 = z} * srwStep m z {y} =
        srwLaw m x {ω | ω 0 = x} * srwStep m x {y} :=
      tsum_eq_single x fun z hz => by simp [srwLaw_eval_zero, hz]
    rw [srwLaw_eval_succ, h1, h2, srwLaw_eval_zero, srwLaw_eval_zero]
    simp
  | succ n ih =>
    calc srwLaw m x {ω | ω (n + 1 + 1) = y}
        = ∑' w, srwStep m x {w} * ∑' z, srwLaw m w {ω | ω n = z} * srwStep m z {y} := by
          rw [srwLaw_eval_succ]
          exact tsum_congr fun w => by rw [ih]
      _ = ∑' z, (∑' w, srwStep m x {w} * srwLaw m w {ω | ω n = z}) * srwStep m z {y} := by
          simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
          exact ENNReal.tsum_comm
      _ = ∑' z, srwLaw m x {ω | ω (n + 1) = z} * srwStep m z {y} := by
          simp_rw [srwLaw_eval_succ m n x]

/-! ## `n`-step detailed balance -/

/-- **`n`-step detailed balance** on a symmetric locally finite multigraph:
`deg(x) p_n(x, y) = deg(y) p_n(y, x)`. -/
theorem mdeg_mul_srwLaw_eval_eq_of_isLocallyFiniteMult {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (n : ℕ) (x y : ℤ) :
    (mdeg m x : ℝ≥0∞) * srwLaw m x {ω | ω n = y} = (mdeg m y : ℝ≥0∞) * srwLaw m y {ω | ω n = x} := by
  induction n generalizing x y with
  | zero =>
    rw [srwLaw_eval_zero, srwLaw_eval_zero]
    by_cases h : y = x
    · subst h
      rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    calc (mdeg m x : ℝ≥0∞) * srwLaw m x {ω | ω (n + 1) = y}
        = ∑' z, ((mdeg m x : ℝ≥0∞) * srwLaw m x {ω | ω n = z}) * srwStep m z {y} := by
          rw [srwLaw_eval_succ', ← ENNReal.tsum_mul_left]
          simp only [mul_assoc]
      _ = ∑' z, srwLaw m z {ω | ω n = x} * ((mdeg m z : ℝ≥0∞) * srwStep m z {y}) := by
          refine tsum_congr fun z => ?_
          rw [ih x z]
          ring
      _ = ∑' z, srwLaw m z {ω | ω n = x} * (m y z : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          rw [mdeg_mul_srwStep_singleton hlf, hsymm z y]
      _ = ∑' z, (mdeg m y : ℝ≥0∞) * (srwStep m y {z} * srwLaw m z {ω | ω n = x}) := by
          refine tsum_congr fun z => ?_
          rw [← mdeg_mul_srwStep_singleton hlf y z]
          ring
      _ = (mdeg m y : ℝ≥0∞) * srwLaw m y {ω | ω (n + 1) = x} := by
          rw [ENNReal.tsum_mul_left, srwLaw_eval_succ]

/-- **`n`-step detailed balance** for simple random walk on a symmetric multigraph whose edge measures are finite
(the non-junk branch of `srwStep` at vertices of positive degree): `deg(x) p_n(x, y) = deg(y) p_n(y, x)`. -/
theorem mdeg_mul_srwLaw_eval_eq {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hfin : ∀ a, edgeMeasure m a univ ≠ ⊤) (n : ℕ) (x y : ℤ) :
    (mdeg m x : ℝ≥0∞) * srwLaw m x {ω | ω n = y} = (mdeg m y : ℝ≥0∞) * srwLaw m y {ω | ω n = x} :=
  mdeg_mul_srwLaw_eval_eq_of_isLocallyFiniteMult hsymm (isLocallyFiniteMult_of_edgeMeasure_ne_top hfin) n x y

/-- The real form of `n`-step detailed balance. -/
theorem mdeg_mul_srwLaw_real_eval_eq {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (n : ℕ) (x y : ℤ) :
    (mdeg m x : ℝ) * (srwLaw m x).real {ω | ω n = y} = (mdeg m y : ℝ) * (srwLaw m y).real {ω | ω n = x} := by
  have h := congrArg ENNReal.toReal (mdeg_mul_srwLaw_eval_eq_of_isLocallyFiniteMult hsymm hlf n x y)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h
  rw [measureReal_def, measureReal_def]
  exact h

/-! ## The symmetric pairing -/

/-- For `g` vanishing off a finite set `s`, `E^x[g(X_n)] = ∑_{y ∈ s} g(y) p_n(x, y)`. -/
theorem integral_comp_eval_eq_sum (m : ℤ → ℤ → ℕ) (n : ℕ) (x : ℤ) {g : ℤ → ℝ} {s : Finset ℤ}
    (hgs : ∀ y ∉ s, g y = 0) :
    ∫ ω, g (ω n) ∂(srwLaw m x) = ∑ y ∈ s, g y * (srwLaw m x).real {ω | ω n = y} := by
  have hpt : ∀ ω : ℕ → ℤ, g (ω n) = ∑ y ∈ s, g y * ({ω' : ℕ → ℤ | ω' n = y}.indicator 1 ω) := by
    intro ω
    by_cases hω : ω n ∈ s
    · rw [Finset.sum_eq_single (ω n)]
      · rw [Set.indicator_of_mem (show ω ∈ {ω' : ℕ → ℤ | ω' n = ω n} from rfl), Pi.one_apply, mul_one]
      · intro b _ hb
        rw [Set.indicator_of_notMem (show ω ∉ {ω' : ℕ → ℤ | ω' n = b} from fun h => hb (Eq.symm h)),
          mul_zero]
      · intro h
        exact absurd hω h
    · rw [hgs _ hω]
      refine (Finset.sum_eq_zero fun y hy => ?_).symm
      have hne : ω n ≠ y := fun h => hω (h ▸ hy)
      rw [Set.indicator_of_notMem (show ω ∉ {ω' : ℕ → ℤ | ω' n = y} from hne), mul_zero]
  calc ∫ ω, g (ω n) ∂(srwLaw m x)
      = ∫ ω, ∑ y ∈ s, g y * ({ω' : ℕ → ℤ | ω' n = y}.indicator 1 ω) ∂(srwLaw m x) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∑ y ∈ s, ∫ ω, g y * ({ω' : ℕ → ℤ | ω' n = y}.indicator 1 ω) ∂(srwLaw m x) :=
        integral_finsetSum s fun y _ =>
          ((integrable_const (1 : ℝ)).indicator (measurableSet_eval_eq n y)).const_mul (g y)
    _ = ∑ y ∈ s, g y * (srwLaw m x).real {ω | ω n = y} := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [integral_const_mul, integral_indicator_one (measurableSet_eval_eq n y)]

/-- **Symmetric pairing, finite sums.** For `f, g` vanishing off a finite set `s`,
`∑_{x ∈ s} deg(x) f(x) E^x[g(X_n)] = ∑_{x ∈ s} deg(x) g(x) E^x[f(X_n)]`. -/
theorem sum_mdeg_mul_integral_comp_eval_symm {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (n : ℕ) {f g : ℤ → ℝ} (s : Finset ℤ) (hfs : ∀ x ∉ s, f x = 0)
    (hgs : ∀ x ∉ s, g x = 0) :
    ∑ x ∈ s, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x) =
      ∑ x ∈ s, (mdeg m x : ℝ) * g x * ∫ ω, f (ω n) ∂(srwLaw m x) := by
  calc ∑ x ∈ s, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x)
      = ∑ x ∈ s, ∑ y ∈ s, f x * g y * ((mdeg m x : ℝ) * (srwLaw m x).real {ω | ω n = y}) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [integral_comp_eval_eq_sum m n x hgs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = ∑ x ∈ s, ∑ y ∈ s, f x * g y * ((mdeg m y : ℝ) * (srwLaw m y).real {ω | ω n = x}) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [mdeg_mul_srwLaw_real_eval_eq hsymm hlf n x y]
    _ = ∑ y ∈ s, ∑ x ∈ s, f x * g y * ((mdeg m y : ℝ) * (srwLaw m y).real {ω | ω n = x}) :=
        Finset.sum_comm
    _ = ∑ y ∈ s, (mdeg m y : ℝ) * g y * ∫ ω, f (ω n) ∂(srwLaw m y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [integral_comp_eval_eq_sum m n y hfs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- **Symmetric pairing** on a symmetric locally finite multigraph, for finitely supported `f, g`:
`∑_x deg(x) f(x) E^x[g(X_n)] = ∑_x deg(x) g(x) E^x[f(X_n)]`. -/
theorem tsum_mdeg_mul_integral_comp_eval_symm_of_isLocallyFiniteMult {m : ℤ → ℤ → ℕ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m) {f g : ℤ → ℝ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) (n : ℕ) :
    ∑' x, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x) =
      ∑' x, (mdeg m x : ℝ) * g x * ∫ ω, f (ω n) ∂(srwLaw m x) := by
  classical
  have hfs : ∀ x ∉ hf.toFinset ∪ hg.toFinset, f x = 0 := fun x hx => by
    by_contra h
    exact hx (Finset.mem_union_left _ (hf.mem_toFinset.2 h))
  have hgs : ∀ x ∉ hf.toFinset ∪ hg.toFinset, g x = 0 := fun x hx => by
    by_contra h
    exact hx (Finset.mem_union_right _ (hg.mem_toFinset.2 h))
  have hL : ∑' x, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x) =
      ∑ x ∈ hf.toFinset ∪ hg.toFinset, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x) :=
    tsum_eq_sum fun x hx => by simp [hfs x hx]
  have hR : ∑' x, (mdeg m x : ℝ) * g x * ∫ ω, f (ω n) ∂(srwLaw m x) =
      ∑ x ∈ hf.toFinset ∪ hg.toFinset, (mdeg m x : ℝ) * g x * ∫ ω, f (ω n) ∂(srwLaw m x) :=
    tsum_eq_sum fun x hx => by simp [hgs x hx]
  rw [hL, hR]
  exact sum_mdeg_mul_integral_comp_eval_symm hsymm hlf n _ hfs hgs

/-- **Symmetric pairing** for simple random walk on a symmetric multigraph with finite edge measures, for finitely
supported `f, g`: `∑_x deg(x) f(x) E^x[g(X_n)] = ∑_x deg(x) g(x) E^x[f(X_n)]`. -/
theorem tsum_mdeg_mul_integral_comp_eval_symm {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hfin : ∀ a, edgeMeasure m a univ ≠ ⊤) {f g : ℤ → ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (n : ℕ) :
    ∑' x, (mdeg m x : ℝ) * f x * ∫ ω, g (ω n) ∂(srwLaw m x) =
      ∑' x, (mdeg m x : ℝ) * g x * ∫ ω, f (ω n) ∂(srwLaw m x) :=
  tsum_mdeg_mul_integral_comp_eval_symm_of_isLocallyFiniteMult hsymm
    (isLocallyFiniteMult_of_edgeMeasure_ne_top hfin) hf hg n

/-! ## The mated-CRT map -/

section BMEdgeCount

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- For `ε ≥ 0` and a locally finite realization, the edge count of Definition 1.1 is locally finite: the neighbours
of `x` are the endpoints of the darts out of `x` in Bonanno's multigraph. -/
theorem isLocallyFiniteMult_bmEdgeCount (hε : 0 ≤ ε) :
    IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) := fun x =>
  (((MatedCRTHarmonic.MatedCRT.graph ε ω h).outDarts x).image
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt).finite_toSet.subset fun _ hy =>
      Finset.mem_coe.2 (bmEdgeCount_ne_zero_mem_image h hε hy)

/-- **`n`-step detailed balance on the mated-CRT map** (Definition 1.1), for a locally finite realization. -/
theorem mdeg_mul_srwLaw_eval_eq_bmEdgeCount (hε : 0 ≤ ε) (n : ℕ) (x y : ℤ) :
    (mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x : ℝ≥0∞) *
        srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x {w | w n = y} =
      (mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) y : ℝ≥0∞) *
        srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) y {w | w n = x} :=
  mdeg_mul_srwLaw_eval_eq_of_isLocallyFiniteMult (bmEdgeCount_symm ε _ _) (isLocallyFiniteMult_bmEdgeCount h hε)
    n x y

/-- **Symmetric pairing on the mated-CRT map** (Definition 1.1), for a locally finite realization and finitely
supported `f, g`. -/
theorem tsum_mdeg_mul_integral_comp_eval_symm_bmEdgeCount (hε : 0 ≤ ε) {f g : ℤ → ℝ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) (n : ℕ) :
    ∑' x, (mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x : ℝ) * f x *
        ∫ w, g (w n) ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x) =
      ∑' x, (mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x : ℝ) * g x *
        ∫ w, f (w n) ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x) :=
  tsum_mdeg_mul_integral_comp_eval_symm_of_isLocallyFiniteMult (bmEdgeCount_symm ε _ _)
    (isLocallyFiniteMult_bmEdgeCount h hε) hf hg n

end BMEdgeCount

section Env

variable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ε : ℝ} {ω : Ω}

/-- **`n`-step detailed balance on the map `𝒢^ε` of an environment**, at a realization where it is locally finite. -/
theorem mdeg_mul_srwLaw_eval_eq_mult (hlf : IsLocallyFiniteMult (S.mult ε ω)) (n : ℕ) (x y : ℤ) :
    (mdeg (S.mult ε ω) x : ℝ≥0∞) * srwLaw (S.mult ε ω) x {w | w n = y} =
      (mdeg (S.mult ε ω) y : ℝ≥0∞) * srwLaw (S.mult ε ω) y {w | w n = x} :=
  mdeg_mul_srwLaw_eval_eq_of_isLocallyFiniteMult (S.mult_symm ε ω) hlf n x y

/-- **Symmetric pairing on the map `𝒢^ε` of an environment**, at a realization where it is locally finite, for
finitely supported `f, g`: `∑_x deg(x) f(x) E^x[g(X_n)] = ∑_x deg(x) g(x) E^x[f(X_n)]`. -/
theorem tsum_mdeg_mul_integral_comp_eval_symm_mult (hlf : IsLocallyFiniteMult (S.mult ε ω)) {f g : ℤ → ℝ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) (n : ℕ) :
    ∑' x, (mdeg (S.mult ε ω) x : ℝ) * f x * ∫ w, g (w n) ∂(srwLaw (S.mult ε ω) x) =
      ∑' x, (mdeg (S.mult ε ω) x : ℝ) * g x * ∫ w, f (w n) ∂(srwLaw (S.mult ε ω) x) :=
  tsum_mdeg_mul_integral_comp_eval_symm_of_isLocallyFiniteMult (S.mult_symm ε ω) hlf hf hg n

end Env

end MatedCRT.FirstPass.Derived
