import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected
import MatedCRT.FirstPass.S3i.LensFloored

/-!
# The quenched start and far-exit bounds for the floored good environment

Floored copies (for `FP36GoodEnvFloored`, S3i/LensFloored.lean) of the Lemma 7 clauses of S3i/QuenchedBoundsCorrected.lean:
`quenchedStart_null_of_exit_fp36` (line 35) and, below, `quenchedBoundsOnGood_fp36_of_exit`. The bodies are those of the
originals; the helper lemmas that do not take the environment are reused.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Plan Lemma 7, clause 1, floored good environment** (copy of `quenchedStart_null_of_exit_fp36`,
S3i/QuenchedBoundsCorrected.lean:35). -/
theorem quenchedStart_null_of_exit_fp36_floored
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω}
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1)
    (hε : 0 < ε) (hmpos : 0 < S.mε ε)
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω) :
    srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x} = 0 := by
  obtain ⟨hA, -, -, hfin, hvin, -⟩ := hgood
  have hη : Continuous (S.η ω) := hA.1
  set a := vertexOf ε (S.η ω) y with ha
  set V := cellVertices ε (S.η ω) (ball z (r + 4 * ε ^ b)) with hV
  have hδ : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le b
  have hball : ball z r ⊆ ball z (r + 4 * ε ^ b) := ball_subset_ball (by linarith)
  have haV : a ∈ V := by
    obtain ⟨c, hc1, hc2⟩ := hvin.1
    exact ⟨c, hc1, hball hc2⟩
  have hfinV : FiniteExitData (S.mult ε ω) V := (hfin _ houter).1
  have hE' : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤} = 1 := hexit hfinV a haV
  have hnull2 : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 V)).2 hE'
  have hnull1 : srwLaw (S.mult ε ω) a {x | x 0 ≠ a} = 0 := by
    have h := ae_iff.1 (srwLaw_ae_start (S.mult ε ω) a)
    simpa [ne_eq] using h
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hnull1 hnull2)
  by_contra hxn
  simp only [mem_union, Set.mem_ofPred_eq, mem_compl_iff, not_or, not_not] at hxn hx
  obtain ⟨h0, hT⟩ := hxn
  apply hx
  unfold SameWalkGood
  refine ⟨?_, ?_⟩
  · rw [interpolatedWalk_zero_fp36, h0]
    exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη hvin
  · exact pathExitTime_lt_top_of_vertex_not_mem_fp36 hmpos
      (fun h => vertexPoint_not_mem_of_not_mem_cellVertices_fp36 hε.le
        (vExitTime_toNat_not_mem_fp36 hT) (hball h))

end FirstPass36
end MatedCRT
