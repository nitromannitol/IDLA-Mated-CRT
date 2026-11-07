import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.RandomGraphMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Measurability of exit values from random vertex sets -/

namespace MatedCRT.GreenEnvironment

open Set MeasureTheory ProbabilityTheory

/-- Exit time from a measurable random vertex set is jointly measurable. -/
theorem measurable_vExitTime_random_set {Ω : Type} [MeasurableSpace Ω]
    (V : Ω → Set ℤ) (hV : Measurable V) :
    Measurable (fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2) := by
  have hmem : ∀ n, MeasurableSet {p : Ω × (ℕ → ℤ) | p.2 n ∈ V p.1} := by
    intro n
    apply measurableSet_setOfPred.mpr
    exact measurable_countable_evaluation (fun p : Ω × (ℕ → ℤ) => p.2 n)
      ((measurable_pi_apply n).comp measurable_snd) (fun k p => k ∈ V p.1)
      (fun k => ((measurable_set_mem k).comp hV).comp measurable_fst)
  have hlt : ∀ k : ℕ, MeasurableSet
      {p : Ω × (ℕ → ℤ) | (k : ℕ∞) < vExitTime (V p.1) p.2} := by
    intro k
    have heq : {p : Ω × (ℕ → ℤ) | (k : ℕ∞) < vExitTime (V p.1) p.2} =
        ⋂ j : ℕ, ⋂ (_ : j ≤ k), {p | p.2 j ∈ V p.1} := by
      ext p
      simp only [mem_iInter]
      exact natCast_lt_vExitTime_iff
    rw [heq]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hmem j
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have heq : (fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2) ⁻¹' {⊤} =
        ⋂ n : ℕ, {p | p.2 n ∈ V p.1} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, mem_iInter]
      exact vExitTime_eq_top_iff
    rw [heq]
    exact MeasurableSet.iInter hmem
  | coe k =>
    have heq : (fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2) ⁻¹' {(k : ℕ∞)} =
        {p | (k : ℕ∞) < vExitTime (V p.1) p.2}ᶜ ∩
          ⋂ j : ℕ, ⋂ (_ : j < k), {p | p.2 j ∈ V p.1} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_iInter]
      exact vExitTime_eq_natCast_iff
    rw [heq]
    exact (hlt k).compl.inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => hmem j)

/-- The exit position is jointly measurable in the vertex set and the path. -/
theorem measurable_vExitPosition_random_set {Ω : Type} [MeasurableSpace Ω]
    (V : Ω → Set ℤ) (hV : Measurable V) :
    Measurable (fun p : Ω × (ℕ → ℤ) => vExitPosition (V p.1) p.2) := by
  have hk : Measurable (fun p : Ω × (ℕ → ℤ) => (vExitTime (V p.1) p.2).toNat) :=
    (measurable_of_countable ENat.toNat).comp (measurable_vExitTime_random_set V hV)
  refine measurable_to_countable' fun y => ?_
  have heq : (fun p : Ω × (ℕ → ℤ) => vExitPosition (V p.1) p.2) ⁻¹' {y} =
      ⋃ n : ℕ, (fun p : Ω × (ℕ → ℤ) => (vExitTime (V p.1) p.2).toNat) ⁻¹' {n} ∩
        (fun p : Ω × (ℕ → ℤ) => p.2 n) ⁻¹' {y} := by
    ext p
    simp only [vExitPosition, mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff]
    constructor
    · intro h; exact ⟨_, rfl, h⟩
    · rintro ⟨n, hn, h⟩; rw [hn]; exact h
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hk (measurableSet_singleton n)).inter
    (((measurable_pi_apply n).comp measurable_snd) (measurableSet_singleton y))

/-- Expected exit values depend measurably on a random graph, random domain,
and measurable boundary data. -/
theorem measurable_expected_exitValue {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V : Ω → Set ℤ) (hV : Measurable V) (g : Ω → ℤ → ℝ)
    (hg : ∀ b, Measurable fun ω => g ω b) (a : ℤ) :
    Measurable (fun ω => ∫ x, g ω (vExitPosition (V ω) x) ∂srwLaw (M ω) a) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (M ω) a, measurable_srwLaw M hM a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw _ _⟩
  have hm : Measurable (fun p : Ω × (ℕ → ℤ) => g p.1 (vExitPosition (V p.1) p.2)) := by
    exact measurable_countable_evaluation _ (measurable_vExitPosition_random_set V hV)
      (fun b p => g p.1 b) (fun b => (hg b).comp measurable_fst)
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

end MatedCRT.GreenEnvironment
