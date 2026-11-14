import MatedCRT.FirstPass.Derived.ExitCouplingGlue
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.RandomGraphMeasurable
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Measurability of stopped embedded walk laws

For a measurable family of vertex sets and embeddings, the stopped interpolated walk and its
quenched law depend measurably on the environment.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set LatticeProb
open scoped NNReal ENNReal
open MatedCRT.ExitCouplingGlue

variable {Ω : Type} [MeasurableSpace Ω]

/-- The exit time is jointly measurable in a random vertex set and a vertex path. -/
theorem measurable_vExitTime_random_set (V : Ω → Set ℤ) (hV : Measurable V) :
    Measurable fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2 := by
  classical
  have hmem : ∀ n : ℕ, MeasurableSet {p : Ω × (ℕ → ℤ) | p.2 n ∈ V p.1} := by
    intro n
    apply measurableSet_setOfPred.mpr
    exact measurable_countable_evaluation (fun p : Ω × (ℕ → ℤ) => p.2 n)
      ((measurable_pi_apply n).comp measurable_snd) (fun k p => k ∈ V p.1)
      (fun k => ((measurable_set_mem k).comp hV).comp measurable_fst)
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have h : (fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2) ⁻¹' {⊤} =
        ⋂ n : ℕ, {p | p.2 n ∈ V p.1} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, mem_iInter]
      exact vExitTime_eq_top_iff
    rw [h]
    exact MeasurableSet.iInter hmem
  | coe k =>
    have h : (fun p : Ω × (ℕ → ℤ) => vExitTime (V p.1) p.2) ⁻¹' {(k : ℕ∞)} =
        {p | p.2 k ∈ V p.1}ᶜ ∩ ⋂ j : ℕ, ⋂ (_ : j < k), {p | p.2 j ∈ V p.1} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_iInter]
      constructor
      · intro hk
        exact ⟨apply_vExitTime_not_mem hk, fun j hj =>
          (vExitTime_eq_natCast_iff.mp hk).2 j hj⟩
      · rintro ⟨hk, hj⟩
        apply vExitTime_eq_natCast_iff.mpr
        refine ⟨?_, hj⟩
        intro ht
        exact hk ((natCast_lt_vExitTime_iff.mp ht) k le_rfl)
    rw [h]
    exact (hmem k).compl.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hmem j)

/-- The stopped interpolated walk is jointly measurable in the environment and the walk. -/
theorem measurable_stoppedInterp_random (V : Ω → Set ℤ) (hV : Measurable V)
    (v : Ω → ℤ → ℂ) (hv : Measurable v) (m : ℝ≥0) :
    Measurable fun p : Ω × (ℕ → ℤ) => stoppedInterp (v p.1) m (V p.1) p.2 := by
  have hi : Measurable fun p : Ω × (ℕ → ℤ) => interpPathCM (v p.1) m.coe_nonneg p.2 := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    have h1 : ∀ n : ℕ, Measurable fun p : Ω × (ℕ → ℤ) => v p.1 (p.2 n) := fun n =>
      (measurable_from_prod_countable_left (f := fun q : (ℤ → ℂ) × ℤ => q.1 q.2)
        fun y => measurable_pi_apply y).comp
        ((hv.comp measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd))
    simp only [interpPathCM_apply, interpPathFn, linInterp]
    exact (measurable_const.mul (h1 _)).add (measurable_const.mul (h1 _))
  have ht : Measurable fun p : Ω × (ℕ → ℤ) =>
      (((vExitTime (V p.1) p.2).toNat : ℝ≥0) / m) := by
    exact ((measurable_of_countable (fun n : ℕ∞ => (n.toNat : ℝ≥0))).comp
      (measurable_vExitTime_random_set V hV)).div_const m
  exact measurable_stopPath hi ht

/-- The quenched law of the stopped interpolated walk is measurable in the environment. -/
theorem measurable_stoppedInterp_srwLaw (V : Ω → Set ℤ) (hV : Measurable V)
    (v : Ω → ℤ → ℂ) (hv : Measurable v) (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k) (m : ℝ≥0) (a : ℤ) :
    Measurable fun ω => (srwLaw (M ω) a).map (stoppedInterp (v ω) m (V ω)) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (M ω) a,
    GreenEnvironment.measurable_srwLaw M hM a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw (M ω) a⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hset : MeasurableSet {p : Ω × (ℕ → ℤ) | stoppedInterp (v p.1) m (V p.1) p.2 ∈ s} :=
    measurable_stoppedInterp_random V hV v hv m hs
  have h := κ.measurable_kernel_prodMk_left hset
  convert h using 1
  funext ω
  exact Measure.map_apply (measurable_stoppedInterp (v ω) m (V ω)) hs

end MatedCRT
