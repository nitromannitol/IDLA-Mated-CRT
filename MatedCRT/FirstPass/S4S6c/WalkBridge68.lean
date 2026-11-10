import Mathlib
import MatedCRT.Defs.RandomWalk
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.FirstPass.S6e.Relation
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6r.Amplification
import MatedCRT.FirstPass.S4S6c.ExitNull68

/-!
# Lemma 6.8, walk bridge (q2, S10 item (b))

The quenched exit probability `Lemma68Config.exitQ S ε ω r i` is the `srwLaw` probability of
`Lemma68Walk.exitEvent U A` with `U = killed ε η Θ F0 r` and `A = i.A` (S6h/Core.lean). The event is the
no-escape event `{X n ∈ A for all n < τ_U}` of `prefix_bad_bound` (S6r/Amplification.lean), with coordinates
`X n x = x n`, killing time `τ_U = vExitTime U` (Defs/RandomWalk.lean) and the natural filtration
`coordFiltration` of the coordinates. Hence the strong-Markov chain bound of `prefix_bad_bound` transfers to `exitQ`.

Named hypotheses, not proved here: the one-test bound `hone` (strong Markov at `T k`; z8, S6r/OneTest.lean),
the stopping times `T k`, `L k` (z9, S6r/ShellWiring.lean) and the pathwise shell inequalities `hTT`, `hLT`,
`hcross`, `hend` (z9). Nothing here uses the environment.
-/

open MeasureTheory

namespace MatedCRT

namespace Lemma68WalkBridge

open Lemma68Window

/-- The natural filtration of the coordinate process `n ↦ x n` on path space `ℕ → ℤ`. -/
noncomputable def coordFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℤ)) :=
  Filtration.natural (fun n (x : ℕ → ℤ) => x n) (fun n => (measurable_pi_apply n).stronglyMeasurable)

/-- The coordinate `x n` is `coordFiltration n`-measurable. -/
theorem coord_measurable (n : ℕ) : Measurable[coordFiltration n] (fun x : ℕ → ℤ => x n) := by
  intro s _
  exact (le_iSup₂ (f := fun (j : ℕ) (_ : j ≤ n) =>
    MeasurableSpace.comap (fun x : ℕ → ℤ => x j) (inferInstance : MeasurableSpace ℤ)) n le_rfl)
    _ ⟨s, ‹MeasurableSet s›, rfl⟩

/-- The first exit time `vExitTime U` of a path from `U` is a stopping time of `coordFiltration`
(the set `{τ_U ≤ i}` is `{∃ k ≤ i, x k ∉ U}`, by `lt_vExitTime_iff'`). -/
theorem isStoppingTime_vExitTime (U : Set ℤ) : IsStoppingTime coordFiltration (vExitTime U) := by
  intro i
  have hiff : ∀ x : ℕ → ℤ, vExitTime U x ≤ (i : ℕ∞) ↔ ¬ ∀ k ≤ i, x k ∈ U := fun x => by
    rw [← not_lt, Lemma68Relation.lt_vExitTime_iff']
  have hset2 : {x : ℕ → ℤ | ∀ k ≤ i, x k ∈ U} = ⋂ k ∈ Set.Iic i, (fun x : ℕ → ℤ => x k) ⁻¹' U := by
    ext x
    simp
  have key : MeasurableSet[coordFiltration i] {x : ℕ → ℤ | ∀ k ≤ i, x k ∈ U}ᶜ := by
    refine MeasurableSet.compl ?_
    rw [hset2]
    refine MeasurableSet.biInter (Set.to_countable _) fun k hk => ?_
    exact coordFiltration.mono (Set.mem_Iic.1 hk) _ (coord_measurable k MeasurableSet.of_discrete)
  convert key using 1
  exact Set.ext hiff

/-- A path functional whose sublevel sets `{τ ≤ n}` are determined by the prefix `(x 0, …, x n)` is a stopping time
of `coordFiltration`: the prefix map is `coordFiltration n`-measurable and the prefix space is countable. This is the
form in which the shell times `T k`, `L k` (hitting-type functionals of the path) enter `prefix_bad_bound_of_lt`. -/
theorem isStoppingTime_of_prefix (τ : (ℕ → ℤ) → ℕ∞)
    (h : ∀ n : ℕ, ∃ S : Set (Fin (n + 1) → ℤ),
      {x : ℕ → ℤ | τ x ≤ (n : ℕ∞)} = {x : ℕ → ℤ | (fun k : Fin (n + 1) => x k) ∈ S}) :
    IsStoppingTime coordFiltration τ := by
  intro n
  obtain ⟨S, hS⟩ := h n
  have hpre : Measurable[coordFiltration n] (fun x : ℕ → ℤ => (fun k : Fin (n + 1) => x k)) := by
    let _ : MeasurableSpace (ℕ → ℤ) := coordFiltration n
    exact Measurable.of_eval fun (k : Fin (n + 1)) =>
      (coord_measurable (k : ℕ)).mono (coordFiltration.mono (Nat.lt_succ_iff.mp k.isLt)) le_rfl
  have key : MeasurableSet[coordFiltration n]
      ((fun x : ℕ → ℤ => (fun k : Fin (n + 1) => x k)) ⁻¹' S) :=
    hpre (Set.to_countable S).measurableSet
  convert key using 1
  ext x
  exact Set.ext_iff.1 hS x

/-- The walk exit event is the no-escape event of the coordinates killed at `vExitTime U`. -/
theorem exitEvent_eq_noEscapeSet (U A : Set ℤ) :
    Lemma68Walk.exitEvent U A = noEscapeSet (fun n (x : ℕ → ℤ) => x n) A (vExitTime U) := by
  ext x
  simp only [Lemma68Walk.exitEvent, noEscapeSet, Set.mem_ofPred_eq]
  exact ⟨fun h n hn => h n (Lemma68Relation.lt_vExitTime_iff'.1 hn),
    fun h n hn => h n (Lemma68Relation.lt_vExitTime_iff'.2 hn)⟩

/-- `exitQ` as a no-escape probability for the simple random walk law. -/
theorem srw_exit_eq_noEscape (m : ℤ → ℤ → ℕ) (a : ℤ) (U A : Set ℤ) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) =
      (srwLaw m a).real (noEscapeSet (fun n (x : ℕ → ℤ) => x n) A (vExitTime U)) := by
  rw [exitEvent_eq_noEscapeSet]

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- Prefix events and test events, restricted form (the form the pathwise shell chain delivers): the
shell-order hypotheses `hTT`, `hLT` are needed only where `T (j+1) < τ_U`, since `P_{j+1} ⊆ {T_{j+1} < τ_U}`. -/
theorem prefixSet_succ_subset_of_lt {E : Type*} {X : ℕ → Ω → E} {A : Set E} {Tj Tj1 Lj : Ω → ℕ∞}
    {τU : Ω → ℕ∞} (h1 : ∀ ω, Tj1 ω < τU ω → Tj ω ≤ Tj1 ω) (h2 : ∀ ω, Tj1 ω < τU ω → Lj ω ≤ Tj1 ω) :
    prefixSet X A Tj1 τU ⊆ prefixSet X A Tj τU ∩ testFailSet X A Tj Lj := by
  intro ω hω
  simp only [prefixSet, testFailSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨hlt, hpre⟩ := hω
  refine ⟨⟨lt_of_le_of_lt (h1 ω hlt) hlt, fun n hn => hpre n (lt_of_lt_of_le hn (h1 ω hlt))⟩,
    fun n _ hnL => hpre n (lt_of_lt_of_le hnL (h2 ω hlt))⟩

/-- `prefix_bad_bound` in restricted form: `hcross`, `hend` are needed only on `{τ_U ≠ ⊤}`, and the null
set `{τ_U = ⊤}` is discharged by `hnull`. The bound is the same `μ(B) ≤ (1 - q)^(n + 1)`. -/
theorem prefix_bad_bound_of_lt {E : Type*} [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E}
    (hA : MeasurableSet A) {T L : ℕ → Ω → ℕ∞} {τU : Ω → ℕ∞}
    (hT : ∀ k, IsStoppingTime 𝓕 (T k)) (hL : ∀ k, IsStoppingTime 𝓕 (L k))
    (hτ : IsStoppingTime 𝓕 τU) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ ω ∂μ, ω ∈ prefixSet X A (T k) τU →
      μ[(testFailSet X A (T k) (L k)).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] ω
        ≤ 1 - q)
    (hTT : ∀ j < n, ∀ ω, T (j + 1) ω < τU ω → T j ω ≤ T (j + 1) ω)
    (hLT : ∀ j < n, ∀ ω, T (j + 1) ω < τU ω → L j ω ≤ T (j + 1) ω)
    (hcross : ∀ ω ∈ noEscapeSet X A τU, τU ω ≠ ⊤ → T n ω < τU ω)
    (hend : ∀ ω ∈ noEscapeSet X A τU, τU ω ≠ ⊤ → L n ω ≤ τU ω)
    (hnull : μ {ω | τU ω = ⊤} = 0) :
    μ.real (noEscapeSet X A τU) ≤ (1 - q) ^ (n + 1) := by
  have hsub : noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤} ⊆
      prefixSet X A (T n) τU ∩ testFailSet X A (T n) (L n) := by
    rintro ω ⟨hω, hfin⟩
    have hT' : T n ω < τU ω := hcross ω hω hfin
    have hL' : L n ω ≤ τU ω := hend ω hω hfin
    have hB : ∀ m : ℕ, (m : ℕ∞) < τU ω → X m ω ∈ A := hω
    exact ⟨⟨hT', fun m hm => hB m (lt_trans hm hT')⟩, fun m _ hmL => hB m (lt_of_lt_of_le hmL hL')⟩
  have hchain : μ.real (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ≤ (1 - q) ^ (n + 1) :=
    shell_chain_bound (P := fun k => prefixSet X A (T k) τU)
      (F := fun k => testFailSet X A (T k) (L k))
      (B := noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤})
      (𝓖 := fun k => (hT k).measurableSpace) (fun k => (hT k).measurableSpace_le) hq1 n
      (fun k _ => measurableSet_prefixSet 𝓕 hX hA (hT k) hτ)
      (fun k _ => measurableSet_testFailSet 𝓕 hX hA (hT k) (hL k)) hone
      (fun k hk => prefixSet_succ_subset_of_lt (fun ω h => hTT k hk ω h)
        (fun ω h => hLT k hk ω h))
      hsub
  have hcov : noEscapeSet X A τU ⊆ (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ∪ {ω | τU ω = ⊤} := by
    intro ω hω
    by_cases h : τU ω = ⊤
    · exact Or.inr h
    · exact Or.inl ⟨hω, h⟩
  have hnull' : μ.real {ω | τU ω = ⊤} = 0 := by
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
  calc μ.real (noEscapeSet X A τU)
      ≤ μ.real ((noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ∪ {ω | τU ω = ⊤}) := measureReal_mono hcov
    _ ≤ μ.real (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) + μ.real {ω | τU ω = ⊤} :=
        measureReal_union_le _ _
    _ ≤ (1 - q) ^ (n + 1) := by rw [hnull', add_zero]; exact hchain

end Generic

/-- Walk-level chain bound: `prefix_bad_bound_of_lt` for the simple random walk law, with the exit event
of `U` in place of the no-escape event. The null set `{vExitTime U = ⊤}` is the input `hnull`. -/
theorem srw_exit_le_pow {m : ℤ → ℤ → ℕ} {a : ℤ} {U A : Set ℤ}
    {T L : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    (hL : ∀ k, IsStoppingTime coordFiltration (L k)) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw m a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) A (T k) (vExitTime U) →
        (srwLaw m a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) A (T k) (L k)).indicator
          (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ x, T (j + 1) x < vExitTime U x → T j x ≤ T (j + 1) x)
    (hLT : ∀ j < n, ∀ x, T (j + 1) x < vExitTime U x → L j x ≤ T (j + 1) x)
    (hcross : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U),
      vExitTime U x ≠ ⊤ → T n x < vExitTime U x)
    (hend : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) A (vExitTime U),
      vExitTime U x ≠ ⊤ → L n x ≤ vExitTime U x)
    (hnull : srwLaw m a {x | vExitTime U x = ⊤} = 0) :
    (srwLaw m a).real (Lemma68Walk.exitEvent U A) ≤ (1 - q) ^ (n + 1) := by
  rw [srw_exit_eq_noEscape]
  exact prefix_bad_bound_of_lt coordFiltration coord_measurable MeasurableSet.of_discrete hT hL
    (isStoppingTime_vExitTime U) hq1 n hone hTT hLT hcross hend hnull

/-- The killed set `killed ε η Θ F0 r` is finite: it is contained in the finite set `F0`. -/
theorem killed_finite (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (r : ℝ) :
    (Lemma68Admissible.killed ε η Θ F0 r).Finite :=
  F0.finite_toSet.subset fun _ hv => hv.1

/-- The null set `{τ_U = ⊤}` of the killed set vanishes for the simple random walk law, under local finiteness
of the multiplicities and nonzero nearest-neighbour multiplicities (`ExitNull68.exit_null_of_finite`). -/
theorem srw_killed_top_null {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (r : ℝ) :
    srwLaw m a {x | vExitTime (Lemma68Admissible.killed ε η Θ F0 r) x = ⊤} = 0 :=
  ExitNull68.exit_null_of_finite hlf hcons (killed_finite ε η Θ F0 r) a

/-- The quenched exit probability `exitQ` of a Lemma 6.8 configuration satisfies the walk-level chain bound
`(1 - q)^(n + 1)`; `U` is the killed set `killed ε η Θ F0 r` and `A = i.A` (S6h/Core.lean). -/
theorem exitQ_le_pow {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r : ℝ)
    (i : Lemma68Config.Config68) {T L : ℕ → (ℕ → ℤ) → ℕ∞}
    (hT : ∀ k, IsStoppingTime coordFiltration (T k)) (hL : ∀ k, IsStoppingTime coordFiltration (L k))
    {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k)
          (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ) (T k)
          (L k)).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x ≤ 1 - q)
    (hTT : ∀ j < n, ∀ x, T (j + 1) x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x →
      T j x ≤ T (j + 1) x)
    (hLT : ∀ j < n, ∀ x, T (j + 1) x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x →
      L j x ≤ T (j + 1) x)
    (hcross : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)),
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
        T n x < vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x)
    (hend : ∀ x ∈ noEscapeSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
        (vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)),
      vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ →
        L n x ≤ vExitTime (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) x)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ (n + 1) := by
  unfold Lemma68Config.exitQ
  exact srw_exit_le_pow hT hL hq1 n hone hTT hLT hcross hend
    (srw_killed_top_null hlf hcons i.a ε (S.η ω) i.Θ i.F0 r)

/-- `q0 / (1 + log (1/r))^2 ≤ 1` for `0 ≤ q0 ≤ 1` and `0 < r ≤ 1`. -/
theorem q_le_one {q0 r : ℝ} (hq0 : 0 ≤ q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hD : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  calc q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q0 := div_le_self hq0 hD
    _ ≤ 1 := hq1

end Lemma68WalkBridge

end MatedCRT
