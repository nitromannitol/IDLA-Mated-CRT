import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedExitBarrier
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Dirichlet

/-! Simultaneous preparation of a countable family of uniform limits. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- A countable family of uniform-in-probability limits has a common
deterministic subsequence with almost-sure uniform convergence. -/
theorem exists_ae_countable_uniform_subsequence
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (K : Set ℂ)
    (F : ℕ → ℝ → Ω → ℂ → ℝ) (g : ℕ → Ω → ℂ → ℝ)
    (hconv : ∀ j, TendstoUniformlyOnInProbability P (F j) (g j) K)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ j,
      TendstoUniformlyOn (fun n => F j (e (φ n)) ω) (g j ω) atTop K := by
  let E : (ℕ × ℕ) → ℝ → Set Ω := fun ij ε =>
    {ω | ¬ ∃ x ∈ K, 1 / ((ij.2 : ℝ) + 1) < |F ij.1 ε ω x - g ij.1 ω x|}
  have hE : ∀ ij, ProbTendsToOne P (E ij) := by
    intro ⟨i, j⟩
    have hp : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    simpa only [ProbTendsToOne, E, compl_ofPred, not_not] using hconv i _ hp
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_mem_countable hE he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with ω hω j
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hω (j, k)] with n hn x hx
  have hb : |F j (e (φ n)) ω x - g j ω x| ≤ 1 / ((k : ℝ) + 1) :=
    le_of_not_gt (fun h => hn ⟨x, hx, h⟩)
  simpa only [Real.dist_eq, abs_sub_comm] using hb.trans_lt hk

end MatedCRT

#print axioms MatedCRT.exists_ae_countable_uniform_subsequence
