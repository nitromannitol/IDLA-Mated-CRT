import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorSubsequence
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.DeviationMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.BoundaryStep
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.RandomSubsequenceProbability
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernelPrepared

/-! # Lemma 3.3: the interior step and the final form

`GreenKernelInteriorPreparedStep` from the prepared subsequence obligation:
the uniform deviation events on `cl(B_{r'}(z)) \ B_d(y)` have `σ(h, η)`-measurable versions, so
almost-sure eventual avoidance along measurable random subsequences of a deterministic subsequence
gives convergence of their probabilities to zero (`tendsto_measure_zero_of_random_subsequence`), and
the subsequence criterion gives convergence as `ε → 0`. -/

namespace MatedCRT

open Set Metric Topology MeasureTheory Filter _root_.HarmonicBalls
open MatedCRT.GreenEnvironment

/-- Prepared Green-kernel identification along deterministic and measurable
random subsequences (corrected paper, proof of Lemma 3.3). This remains an
open obligation, including the independent Green-kernel constant issue G4. -/
def GreenKernelPreparedSubsequenceStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DegreeMeasureConvergenceStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  GreenKernelUpperBoundStmt 𝒮 → DiscretePotentialTightnessPreparedStmt 𝒮 →
  ∀ {γ ρ : ℝ}, 0 < γ → γ < 2 → 0 < ρ → ρ < 1 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ {r r' d : ℝ} {z y : ℂ}, 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
    r' < r → 0 < d →
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] 0) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ n, 0 < ε (ψ n)) ∧
      ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[S.envSigma] fun ω => I ω n) →
        (∀ ω n, n ≤ I ω n) → ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧
          TendstoUniformlyOn (fun k => rescaledBallGreenKernel S r z y (ε (ψ (I ω (φ k)))) ω)
            (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) atTop
            (closedBall z r' \ ball y d)

/-- **Lemma 3.3, interior step.** -/
theorem greenKernelInteriorPreparedStep_of_subsequence (𝒮 : SpaceFillingSLEModel)
    (hsub : GreenKernelPreparedSubsequenceStep 𝒮) : GreenKernelInteriorPreparedStep 𝒮 := by
  intro h210 h34 h214 _ h31 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy r' _ hr'r O hO d hd
    hdO δ hδ
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hK₀c : IsCompact (closedBall z r' \ ball y d) := (isCompact_closedBall z r').diff isOpen_ball
  have hOK : O ⊆ closedBall z r' \ ball y d := by
    intro x hx
    refine ⟨hO hx, fun h => ?_⟩
    have h1 := hdO x hx
    have h2 : dist x y < d := h
    rw [dist_comm] at h1
    linarith
  have hV : ContinuousOn (fun x => S.c₀ / 6 * greenFunction (ball z r) y x)
      (closedBall z r' \ ball y d) :=
    continuousOn_const.mul ((continuousOn_greenFunction_ball_compl hy).mono fun x hx hxy =>
      hx.2 (by rw [mem_singleton_iff.1 hxy]; exact mem_ball_self hd))
  suffices h : Tendsto (fun ε => S.P {ω | ∃ x ∈ closedBall z r' \ ball y d,
      δ < |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x|})
      (𝓝[>] 0) (𝓝 0) by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      fun ε => measure_mono ?_
    rintro ω ⟨x, hx, hbad⟩
    exact ⟨x, hOK hx, hbad⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, -, hpos, hkey⟩ := hsub h210 h34 h214 h31 hγ hγ2
    hρ hρ1 S hS hr hball hy hr'r hd ns hns
  refine ⟨ψ, ?_⟩
  choose A hAm hAe' using fun n => hS.exists_envSigma_measurable_greenKernel_deviation (hpos n)
    r z y _ hK₀c _ hV δ
  have hAall := ae_all_iff.2 hAe'
  have hPA : ∀ n, S.P {ω | ∃ x ∈ closedBall z r' \ ball y d, δ < |rescaledBallGreenKernel S r z y
      (ns (ψ n)) ω x - S.c₀ / 6 * greenFunction (ball z r) y x|} = S.P (A n) := fun n =>
    measure_congr (eventuallyEqSet_iff.2 (by
      filter_upwards [hAe' n] with ω hω
      exact hω.symm))
  simp only [hPA]
  apply tendsto_measure_zero_of_random_subsequence S.P S.envSigma A hAm
    (fun n => hS.nullMeasurableSet_of_envSigma (hAm n))
  intro I hIm hI
  filter_upwards [hkey I hIm hI, hAall] with ω hω hAω
  obtain ⟨φ, -, hu⟩ := hω
  refine ⟨φ, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu δ hδ] with k hk hmem
  obtain ⟨x, hx, hbad⟩ := (hAω (I ω (φ k))).1 hmem
  have h2 := hk x hx
  rw [Real.dist_eq, abs_sub_comm] at h2
  exact lt_irrefl δ (hbad.trans h2)

end MatedCRT
