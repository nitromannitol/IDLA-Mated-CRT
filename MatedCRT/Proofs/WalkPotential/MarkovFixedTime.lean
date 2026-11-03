import MatedCRT.Proofs.WalkPotential.Markov

/-!
# Simple random walk on a multigraph: the Markov property at a fixed time

For an edge multiplicity `m : ℤ → ℤ → ℕ` (no hypothesis) and `n : ℕ`, write `pathHist n x = (x_0, …, x_n)` and
`pathShift n x = (x_n, x_{n+1}, …)`. Under `P^a = srwLaw m a`, conditionally on the history up to time `n`, the shifted
path is simple random walk started at `x_n`:

* `lintegral_srwLaw_markov`: `E^a[f(X_0, …, X_n) g(X_n, X_{n+1}, …)] = E^a[f(X_0, …, X_n) E^{X_n}[g]]` for every
  `f ≥ 0` and measurable `g ≥ 0`;
* `srwLaw_markov` (cylinder form): `P^a[(X_0, …, X_n) ∈ F, (X_{n+k})_k ∈ E] = ∫_{(x_0,…,x_n) ∈ F} P^{x_n}[E] dP^a(x)`.

Both follow by induction on `n` from the Markov property at the first step (`srwLaw_eq_srwFirstStepLaw`,
MatedCRT/Proofs/WalkPotential/Markov.lean): `E^a[F] = ∫ E^b[F(a, ·)] p(a, db)` (`lintegral_srwLaw_eq`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The history `(x_0, …, x_n)` of a path. -/
def pathHist (n : ℕ) (x : ℕ → ℤ) : Fin (n + 1) → ℤ := fun i => x i

/-- The path shifted by `n`: `(x_n, x_{n+1}, …)`. -/
def pathShift (n : ℕ) (x : ℕ → ℤ) : ℕ → ℤ := fun k => x (n + k)

theorem measurable_pathHist (n : ℕ) : Measurable (pathHist n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_pathShift (n : ℕ) : Measurable (pathShift n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem pathHist_pathCons (a : ℤ) (n : ℕ) (y : ℕ → ℤ) :
    pathHist (n + 1) (pathCons a y) = Fin.cons a (pathHist n y) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [pathHist]
  | succ j => simp [pathHist]

theorem pathShift_pathCons (a : ℤ) (n : ℕ) (y : ℕ → ℤ) : pathShift (n + 1) (pathCons a y) = pathShift n y := by
  funext k
  simp only [pathShift]
  rw [show n + 1 + k = (n + k) + 1 by omega]
  rfl

theorem pathShift_zero (x : ℕ → ℤ) : pathShift 0 x = x := by
  funext k
  simp [pathShift]

/-- **First-step decomposition of integrals**: `E^a[F] = ∫ E^b[F(a, ·)] p(a, db)`. -/
theorem lintegral_srwLaw_eq (m : ℤ → ℤ → ℕ) (a : ℤ) {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂srwLaw m a = ∫⁻ b, ∫⁻ y, F (pathCons a y) ∂srwLaw m b ∂srwStep m a := by
  rw [srwLaw_eq_srwFirstStepLaw m a, srwFirstStepLaw,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [lintegral_map hF (measurable_pathCons a)]

/-- **Markov property at time `n`**: `E^a[f(X_0, …, X_n) g(X_{n+·})] = E^a[f(X_0, …, X_n) E^{X_n}[g]]`. -/
theorem lintegral_srwLaw_markov (m : ℤ → ℤ → ℕ) (n : ℕ) :
    ∀ (a : ℤ) (f : (Fin (n + 1) → ℤ) → ℝ≥0∞) {g : (ℕ → ℤ) → ℝ≥0∞}, Measurable g →
      ∫⁻ x, f (pathHist n x) * g (pathShift n x) ∂srwLaw m a =
        ∫⁻ x, f (pathHist n x) * ∫⁻ y, g y ∂srwLaw m (x n) ∂srwLaw m a := by
  induction n with
  | zero =>
    intro a f g hg
    have hae : ∀ᵐ x ∂srwLaw m a, pathHist 0 x = fun _ => a := by
      filter_upwards [srwLaw_ae_start m a] with x hx
      funext i
      show x i = a
      rw [show (i : ℕ) = 0 by have := i.2; omega, hx]
    calc ∫⁻ x, f (pathHist 0 x) * g (pathShift 0 x) ∂srwLaw m a
        = ∫⁻ x, f (fun _ => a) * g x ∂srwLaw m a := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx, pathShift_zero]
      _ = f (fun _ => a) * ∫⁻ x, g x ∂srwLaw m a := lintegral_const_mul _ hg
      _ = ∫⁻ x, f (fun _ => a) * ∫⁻ y, g y ∂srwLaw m a ∂srwLaw m a := by
          rw [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ x, f (pathHist 0 x) * ∫⁻ y, g y ∂srwLaw m (x 0) ∂srwLaw m a := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae, srwLaw_ae_start m a] with x hx hx0
          rw [hx, hx0]
  | succ n ih =>
    intro a f g hg
    have hF1 : Measurable fun x => f (pathHist (n + 1) x) * g (pathShift (n + 1) x) :=
      ((measurable_of_countable f).comp (measurable_pathHist _)).mul (hg.comp (measurable_pathShift _))
    have hG : Measurable fun b : ℤ => ∫⁻ y, g y ∂srwLaw m b := measurable_of_countable _
    have hF2 : Measurable fun x => f (pathHist (n + 1) x) * ∫⁻ y, g y ∂srwLaw m (x (n + 1)) :=
      ((measurable_of_countable f).comp (measurable_pathHist _)).mul (hG.comp (measurable_pi_apply _))
    rw [lintegral_srwLaw_eq m a hF1, lintegral_srwLaw_eq m a hF2]
    refine lintegral_congr fun b => ?_
    simp only [pathHist_pathCons, pathShift_pathCons, pathCons_succ]
    exact ih b (fun z => f (Fin.cons a z)) hg

/-- **Markov property at time `n`, cylinder form**:
`P^a[(X_0, …, X_n) ∈ F, (X_{n+k})_k ∈ E] = ∫_{(x_0, …, x_n) ∈ F} P^{x_n}[E] dP^a(x)`. -/
theorem srwLaw_markov (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) (F : Set (Fin (n + 1) → ℤ)) {E : Set (ℕ → ℤ)}
    (hE : MeasurableSet E) :
    srwLaw m a {x | pathHist n x ∈ F ∧ pathShift n x ∈ E} =
      ∫⁻ x in {x | pathHist n x ∈ F}, srwLaw m (x n) E ∂srwLaw m a := by
  have hS : MeasurableSet {x : ℕ → ℤ | pathHist n x ∈ F} :=
    measurable_pathHist n (Set.to_countable F).measurableSet
  have hSE : MeasurableSet {x : ℕ → ℤ | pathHist n x ∈ F ∧ pathShift n x ∈ E} :=
    hS.inter (measurable_pathShift n hE)
  have h := lintegral_srwLaw_markov m n a (F.indicator (1 : (Fin (n + 1) → ℤ) → ℝ≥0∞))
    (g := E.indicator (1 : (ℕ → ℤ) → ℝ≥0∞)) (measurable_one.indicator hE)
  have hl : ∀ x, (F.indicator 1 (pathHist n x) : ℝ≥0∞) * E.indicator 1 (pathShift n x) =
      {x : ℕ → ℤ | pathHist n x ∈ F ∧ pathShift n x ∈ E}.indicator 1 x := by
    intro x
    by_cases h1 : pathHist n x ∈ F
    · by_cases h2 : pathShift n x ∈ E
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | pathHist n x ∈ F ∧ pathShift n x ∈ E} from ⟨h1, h2⟩)]
        simp
      · rw [Set.indicator_of_mem h1, Set.indicator_apply_eq_zero.2 fun h => absurd h h2,
          Set.indicator_apply_eq_zero.2 fun h => absurd h.2 h2, mul_zero]
    · rw [Set.indicator_apply_eq_zero.2 fun h => absurd h h1, zero_mul,
        Set.indicator_apply_eq_zero.2 fun h => absurd h.1 h1]
  have hr : ∀ x, (F.indicator 1 (pathHist n x) : ℝ≥0∞) * ∫⁻ y, E.indicator 1 y ∂srwLaw m (x n) =
      {x : ℕ → ℤ | pathHist n x ∈ F}.indicator (fun x => srwLaw m (x n) E) x := by
    intro x
    rw [lintegral_indicator_one hE]
    by_cases h1 : pathHist n x ∈ F
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | pathHist n x ∈ F} from h1)]
      simp
    · rw [Set.indicator_apply_eq_zero.2 fun h => absurd h h1, zero_mul]
      symm
      exact Set.indicator_apply_eq_zero.2 fun h => absurd h h1
  rw [lintegral_congr hl, lintegral_congr hr, lintegral_indicator_one hSE, lintegral_indicator hS] at h
  exact h

end MatedCRT
