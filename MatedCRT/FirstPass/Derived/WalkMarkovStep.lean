import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.InterpolatedWalkShift
import MatedCRT.FirstPass.Derived.SrwChainBridge

/-!
# The Markov step of the embedded walk in the environment, as kernels

For a valid environment `S`, the quenched law `walkKernel hS ε k₀` of the embedded simple random walk
of the mated-CRT map started from `k₀` is a kernel `Ω → (ℕ → ℤ)`.  This file records, for every
environment `ω`, the Markov property of the walk at a deterministic time `n` in the set form
`P_ω(F ∩ θₙ⁻¹ B) = ∫_F P_ω^{(x n)}(B) dP_ω` (`F` an event of the coordinates `≤ n`), where
`walkStartKernel hS ε : Kernel (Ω × ℤ) (ℕ → ℤ)` is the walk law as a function of `(ω, start vertex)`,
together with the facts about the interpolated embedded walk that turn this into the Markov step of the
interpolated walk on paths (BG20 Lemma 7.4):

* `MatedCRT.walkStartKernel`: `(ω, z) ↦ srwLaw (S.mult ε ω) z`, a Markov kernel.
* `MatedCRT.walkKernel_markov_step`: the set form of the Markov property at time `n`, for every `ω`.
* `MatedCRT.walkIntegrand v hm f`: `(ω, x) ↦ f (interpPathCM (v ω) hm x)`, measurable for measurable `f`.
* `MatedCRT.integral_walkStartKernel`: the `walkStartKernel`-average of `walkIntegrand` is the integral
  of `f` against the quenched path law `walkPathLaw`.
* `MatedCRT.walkIntegrand_walkShift`: `walkIntegrand` at the shifted walk is `f` of the time-shifted
  interpolated path.
-/

open MeasureTheory ProbabilityTheory Set Preorder MarkovProcess LatticeProb
open scoped ENNReal NNReal

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- The quenched walk law as a kernel in the environment and the start vertex. -/
noncomputable def walkStartKernel {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) : Kernel (Ω × ℤ) (ℕ → ℤ) :=
  ⟨fun q => srwLaw (S.mult ε q.1) q.2,
    measurable_from_prod_countable_left fun k =>
      (measurable_srwLaw k).comp (hS.measurable_mult_array ε)⟩

instance {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (ε : ℝ) :
    IsMarkovKernel (walkStartKernel hS ε) :=
  ⟨fun q => isProbabilityMeasure_srwLaw (S.mult ε q.1) q.2⟩

theorem walkStartKernel_apply {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) (ω : Ω) (z : ℤ) :
    walkStartKernel hS ε (ω, z) = srwLaw (S.mult ε ω) z := rfl

/-- The present state `x n` of a finite history `(x 0, …, x n)`. -/
def lastState (n : ℕ) (w : Finset.Iic n → ℤ) : ℤ := w ⟨n, Finset.mem_Iic.2 le_rfl⟩

theorem measurable_lastState (n : ℕ) : Measurable (lastState n) := measurable_pi_apply _

/-- **Markov property of the embedded walk at a deterministic time**, set form, for every environment:
for an event `{x | (x 0, …, x n) ∈ E}` of the past and measurable `B ⊆ (ℕ → ℤ)`,
`P_ω(past ∈ E, θₙ x ∈ B) = ∫_{past ∈ E} P_ω^{(x n)}(B) dP_ω`. -/
theorem walkKernel_markov_step {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) (k₀ : ℤ) (n : ℕ) (ω : Ω) {E : Set (Finset.Iic n → ℤ)}
    (hE : MeasurableSet E) {B : Set (ℕ → ℤ)} (hB : MeasurableSet B) :
    walkKernel hS ε k₀ ω (frestrictLe n ⁻¹' E ∩ MatedCRTHarmonic.Markov.walkShift n ⁻¹' B) =
      ∫⁻ x in frestrictLe n ⁻¹' E, walkStartKernel hS ε (ω, lastState n (frestrictLe n x)) B
        ∂walkKernel hS ε k₀ ω := by
  have h := MatedCRTHarmonic.Markov.chainLaw_inter_walkShift_preimage (κ := srwKernel (S.mult ε ω))
    k₀ n hE hB
  simp only [chainLaw_srwKernel] at h
  exact h

/-- The integrand `(ω, x) ↦ f (interpolated path of the walk x in the environment ω)`. -/
noncomputable def walkIntegrand (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (f : ContinuousPath ℂ → ℝ) :
    Ω × (ℕ → ℤ) → ℝ :=
  fun p => f (interpPathCM (v p.1) hm p.2)

theorem measurable_walkIntegrand {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ} (hm : 0 ≤ m)
    {f : ContinuousPath ℂ → ℝ} (hf : Measurable f) : Measurable (walkIntegrand v hm f) :=
  hf.comp ((measurable_interpPathCM_uncurry hm).comp ((hv.comp measurable_fst).prodMk measurable_snd))

/-- The average of the integrand over the walk started at `z` is the integral of `f` against the
quenched path law. -/
theorem integral_walkStartKernel {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ) (ω : Ω) (z : ℤ)
    {f : ContinuousPath ℂ → ℝ} (hf : Measurable f) :
    ∫ y, walkIntegrand v hm f (ω, y) ∂walkStartKernel hS ε (ω, z) =
      ∫ g, f g ∂(walkPathLaw S v hm ε z ω : Measure (ContinuousPath ℂ)) := by
  show ∫ y, f (interpPathCM (v ω) hm y) ∂srwLaw (S.mult ε ω) z =
    ∫ g, f g ∂Measure.map (interpPathCM (v ω) hm) (srwLaw (S.mult ε ω) z)
  rw [integral_map (measurable_interpPathCM (v ω) hm).aemeasurable hf.aestronglyMeasurable]

omit [MeasurableSpace Ω] in
/-- The integrand at the shifted walk is `f` of the time-shifted interpolated path. -/
theorem walkIntegrand_walkShift (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 < m) (f : ContinuousPath ℂ → ℝ)
    (ω : Ω) (x : ℕ → ℤ) (n : ℕ) :
    walkIntegrand v hm.le f (ω, MatedCRTHarmonic.Markov.walkShift n x) =
      f (pathShift (interpPathCM (v ω) hm.le x) ((n / m : ℝ).toNNReal)) := by
  rw [pathShift_interpPathCM (v ω) hm]
  rfl

end MatedCRT
