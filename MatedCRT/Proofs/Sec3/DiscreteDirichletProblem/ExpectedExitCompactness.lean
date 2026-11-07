import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitMeasurable
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedPathwiseExtraction

/-! Prepared local compactness for ordinary expected exit times. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Ordinary expected exit times satisfy the prepared compactness hypotheses
on deterministic summable mesh scales. -/
theorem expectedExit_compactness_dyadic_of_prepared
    (𝒮 : SpaceFillingSLEModel) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n ∧ e n < (1 / 2) ^ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ θ : ℕ → ℕ, StrictMono θ → ∃ η : ℕ → ℕ, StrictMono η ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u (ball z r) ∧ ∀ K : Set ℂ, IsCompact K → closure K ⊆ ball z r →
          TendstoUniformlyOn (fun n => rescale (S.mε (e (ψ (φ (θ (η n))))))
            (e (ψ (φ (θ (η n))))) (S.η ω)
            (fun a => (expectedExitTime (S.mult (e (ψ (φ (θ (η n))))) ω)
              (interiorCellVertices (e (ψ (φ (θ (η n))))) (S.η ω) (ball z r)) a).toReal))
            u atTop K := by
  let d : ℕ → ℝ := e ∘ ψ
  have hd : ∀ n, 0 < d n ∧ d n < (1 / 2 : ℝ) ^ n := by
    intro n
    exact ⟨(he _).1, (he _).2.trans_le
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hψ.id_le n))⟩
  have hpoly := isPolySummableScales_of_lt_half_pow hd
  have hsize := ae_eventual_expectedExit_size_of_statements h218 h217 hγ hγ2 hρ hρ1
    S hS hball d hpoly hpoly.tendsto_zero
  have hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (d n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (d n) ω)
          (fun a => (expectedExitTime (S.mult (d n) ω)
            (interiorCellVertices (d n) (S.η ω) (ball z r)) a).toReal) a| ≤ C) ∧
      (∀ a ∈ cellVertices (d n) (S.η ω) (ball z r),
        |(expectedExitTime (S.mult (d n) ω)
          (interiorCellVertices (d n) (S.η ω) (ball z r)) a).toReal| ≤ C / d n) := by
    filter_upwards [hsize, hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω ⟨C, hC⟩ harea hp hadj
    refine ⟨max C 1, by positivity, ?_⟩
    filter_upwards [hC] with n hn
    let A := interiorCellVertices (d n) (S.η ω) (ball z r)
    let m := S.mult (d n) ω
    have hlf : IsLocallyFiniteMult m :=
      Tightness.isLocallyFiniteMult_of_cells harea.1 hp (hd n).1 (hadj (d n) (hd n).1)
    have hfin : ∀ a ∈ A, expectedExitTime m A a ≠ ⊤ :=
      fun a ha => (hn a ha.1).1
    refine ⟨?_, ?_⟩
    · intro a ha
      have hdeg : mdeg m a ≠ 0 := mdeg_ne_zero_of_ne_zero hlf (S.mult_succ_ne_zero (hd n).1.le ω a)
      have hlap := Tightness.lapSum_expectedExitTime hlf hfin ha hdeg
      have heq := mLaplacian_mul_mdeg hlf (fun b => (expectedExitTime m A b).toReal) a
      have hd0 : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hdeg
      have : matedLaplacian m (fun b => (expectedExitTime m A b).toReal) a = -1 := by
        change mLaplacian m (fun b => (expectedExitTime m A b).toReal) a = -1
        rw [hlap] at heq
        apply mul_right_cancel₀ hd0
        simpa using heq
      rw [this, abs_neg, abs_one]
      exact le_max_right _ _
    · intro a ha
      have hq := (hn a ha).2
      rw [abs_of_nonneg ENNReal.toReal_nonneg, le_div_iff₀ (hd n).1]
      nlinarith [le_max_left C 1]
  obtain ⟨φ, hφ, hcompact⟩ := preparedTightness_pathwise_local_ae 𝒮 h31 hγ hγ2 hρ hρ1
    S hS (ball z r) hball isOpen_ball ((convex_ball z r).isConnected (nonempty_ball.2 hr))
    d (fun n => (hd n).1) hpoly.tendsto_zero
    (fun ω n a => (expectedExitTime (S.mult (d n) ω)
      (interiorCellVertices (d n) (S.η ω) (ball z r)) a).toReal)
    (fun n a => by
      obtain ⟨u, hu, hae⟩ := hS.exists_envSigma_measurable_expectedExitTime (d n) (ball z r) (Or.inl isOpen_ball)
      exact ⟨fun ω => u ω a, hu a, hae.mono fun _ h => h a⟩) hbound
  exact ⟨φ, hφ, by simpa only [d, Function.comp_apply] using hcompact⟩

end MatedCRT

#print axioms MatedCRT.expectedExit_compactness_dyadic_of_prepared
