import MatedCRT.Proofs.Sec6.AbelianIDLA.Exchange
import MatedCRT.Steps.Sec6.IterativeBound

/-!
# Lemma 6.3 (lemma:abelian-IDLA, line 2289): the Abelian property of IDLA, proved

Cited in the paper from Diaconis-Fulton (1991, Section 4); proved here on every multigraph `m` on `ℤ`, for arbitrary
starting sites (`isAbelianIDLA`), with no hypothesis on `m`.

Proof. Write `F(A; L)` for the law of the IDLA aggregate from the occupied set `A` with walkers released from the list
`L` (`aggValue`, tested against the indicator of each value `B`). By the exchangeability of IDLA (`aggValue_perm`,
MatedCRT/Proofs/Sec6/AbelianIDLA/Exchange.lean), `F(A; L)` depends on `L` only as a multiset. Run the stopped process
of Definition 6.2 walker by walker, from the state `(A, P)` (`A ⊆ Θ'` occupied, `P` stopped positions), and restart
the stopped walkers at the end: by induction on the number of remaining walkers this has the law `F(A; P ++ L)`
(`runValue_stopped`). Indeed a walker leaving `A` at `b ∈ Θ'` is absorbed at `b` in both processes, while a walker
stopped at `b ∉ Θ'` is restarted from `b ∉ A` and, by exchangeability, may be released first, when it settles at `b`
at once. With `A = Θ`, `P = []` this is Lemma 6.3.
-/

namespace MatedCRT

namespace AbelianIDLA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- **The stopped process followed by the restarted walkers**: from the state `(A, P)` with `A ⊆ Θ'`, releasing the
walkers `L` with stopping outside `Θ'` and then restarting the stopped walkers gives the law of IDLA from `A` with
walkers `P ++ L`. -/
theorem runValue_stopped (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) {Θ' : Set ℤ} :
    ∀ (L : List ℤ) (A : Set ℤ) (P : List ℤ), A ⊆ Θ' →
      runValue m Θ' (fun s => aggValue m G s.1 s.2) (A, P) L = aggValue m G A (P ++ L)
  | [], A, P, _ => by rw [runValue_nil, List.append_nil]
  | z :: L, A, P, hA => by
    rw [runValue_cons]
    have hpt : ∀ x : ℕ → ℤ, runValue m Θ' (fun s => aggValue m G s.1 s.2) (idlaStep Θ' (A, P) x) L =
        aggValue m G (Absorption.nextAgg univ A (firstExitSite A x)) (P ++ L) := by
      intro x
      rw [idlaStep_eq_stepOpt]
      cases ho : firstExitSite A x with
      | none => exact runValue_stopped m G L A P hA
      | some b =>
        by_cases hb : b ∈ Θ'
        · rw [show stepOpt Θ' (A, P) (some b) = (A ∪ {b}, P) from ite_eq_left hb,
            runValue_stopped m G L (A ∪ {b}) P (union_subset hA (singleton_subset_iff.2 hb)), nextAgg_univ_some]
        · have hbA : b ∉ A := fun h => hb (hA h)
          rw [show stepOpt Θ' (A, P) (some b) = (A, P ++ [b]) from ite_eq_right hb,
            runValue_stopped m G L A (P ++ [b]) hA, nextAgg_univ_some,
            aggValue_perm m G (show (P ++ [b] ++ L).Perm (b :: (P ++ L)) by
              rw [List.append_assoc, List.singleton_append]; exact List.perm_middle) A,
            aggValue_cons]
          have hae : ∀ᵐ y ∂srwLaw m b, aggValue m G (Absorption.nextAgg univ A (firstExitSite A y)) (P ++ L) =
              aggValue m G (A ∪ {b}) (P ++ L) := by
            filter_upwards [srwLaw_ae_start m b] with y hy
            rw [firstExitSite_of_start_not_mem (hy ▸ hbA : y 0 ∉ A), hy, nextAgg_univ_some]
          rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]
    rw [lintegral_congr hpt, aggValue_perm m G List.perm_middle A, aggValue_cons]

open Classical in
/-- The indicator of the value `B` of the aggregate. -/
noncomputable def valueIndicator (B A : Set ℤ) : ℝ≥0∞ := if A = B then 1 else 0

/-- The law of the IDLA aggregate, at the value `B`, is the recursion `aggValue`. -/
theorem walkersLaw_idlaAggregate_eq (m : ℤ → ℤ → ℕ) (A B : Set ℤ) {k : ℕ} (b : Fin k → ℤ) :
    walkersLaw m b {ys | idlaAggregate A univ (List.ofFn ys) = B} =
      aggValue m (valueIndicator B) A (List.ofFn b) := by
  have hmeas : MeasurableSet {ys : Fin k → ℕ → ℤ | idlaAggregate A univ (List.ofFn ys) = B} :=
    measurableSet_foldl_idlaStep univ k (A, []) fun s => s.1 = B
  rw [← lintegral_indicator_one hmeas, ← runValue_univ m (valueIndicator B) (List.ofFn b) A [],
    ← lintegral_walkersLaw_foldl m univ _ k (A, []) b]
  refine lintegral_congr fun ys => ?_
  show _ = valueIndicator B (idlaAggregate A univ (List.ofFn ys))
  by_cases h : idlaAggregate A univ (List.ofFn ys) = B
  · rw [indicator_of_mem (show ys ∈ {ys : Fin k → ℕ → ℤ | idlaAggregate A univ (List.ofFn ys) = B} from h),
      Pi.one_apply]
    exact (ite_eq_left h).symm
  · rw [indicator_of_notMem (show ys ∉ {ys : Fin k → ℕ → ℤ | idlaAggregate A univ (List.ofFn ys) = B} from h)]
    exact (ite_eq_right h).symm

/-- **Lemma 6.3 on a fixed multigraph, for arbitrary starting sites** (Diaconis-Fulton 1991, Section 4): for every
multigraph `m` on `ℤ`, every `Θ ⊆ Θ'` and all starting sites `a₁, …, a_k`, the law of `A(Θ; a₁, …, a_k)` is that of
the restarted aggregate `A(A(Θ; a → Θ'); P(Θ; a → Θ'))`. -/
theorem isAbelianIDLA (m : ℤ → ℤ → ℕ) : IsAbelianIDLA m := by
  intro Θ Θ' k a hΘ B
  have hin : ∀ xs : Fin k → ℕ → ℤ,
      walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = B} =
      aggValue m (valueIndicator B) ((List.ofFn xs).foldl (idlaStep Θ') (Θ, [])).1
        ((List.ofFn xs).foldl (idlaStep Θ') (Θ, [])).2 := by
    intro xs
    rw [walkersLaw_idlaAggregate_eq, List.ofFn_get]
    rfl
  rw [walkersLaw_idlaAggregate_eq]
  calc aggValue m (valueIndicator B) Θ (List.ofFn a)
      = aggValue m (valueIndicator B) Θ ([] ++ List.ofFn a) := rfl
    _ = runValue m Θ' (fun s => aggValue m (valueIndicator B) s.1 s.2) (Θ, []) (List.ofFn a) :=
        (runValue_stopped m _ (List.ofFn a) Θ [] hΘ).symm
    _ = ∫⁻ xs, aggValue m (valueIndicator B) ((List.ofFn xs).foldl (idlaStep Θ') (Θ, [])).1
          ((List.ofFn xs).foldl (idlaStep Θ') (Θ, [])).2 ∂walkersLaw m a :=
        (lintegral_walkersLaw_foldl m Θ' (fun s => aggValue m (valueIndicator B) s.1 s.2) k (Θ, []) a).symm
    _ = _ := lintegral_congr fun xs => (hin xs).symm

/-- **Lemma 6.3 on a fixed multigraph** in the form of the identity of `AbelianIDLAStmt`, for arbitrary starting
sites. -/
theorem abelianIDLA_fixed (m : ℤ → ℤ → ℕ) (Θ Θ' : Set ℤ) (k : ℕ) (a : Fin k → ℤ) (hΘ : Θ ⊆ Θ') (B : Set ℤ) :
    walkersLaw m a {xs | idlaAggregate Θ univ (List.ofFn xs) = B} =
      ∫⁻ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = B}
        ∂walkersLaw m a :=
  isAbelianIDLA m Θ Θ' k a hΘ B

/-- The step `AbelianIDLAAnyStartStep` of Lemma 6.10 holds (for every environment). -/
theorem abelianIDLAAnyStartStep (𝒮 : SpaceFillingSLEModel) : AbelianIDLAAnyStartStep 𝒮 :=
  fun _ _ _ _ _ S _ => ae_of_all _ fun ω ε _ => isAbelianIDLA (S.mult ε ω)

/-- **Lemma 6.3** (lemma:abelian-IDLA, line 2289), proved. -/
theorem abelianIDLA (𝒮 : SpaceFillingSLEModel) : AbelianIDLAStmt 𝒮 :=
  (abelianIDLAAnyStartStep 𝒮).abelianIDLA

end AbelianIDLA

end MatedCRT
