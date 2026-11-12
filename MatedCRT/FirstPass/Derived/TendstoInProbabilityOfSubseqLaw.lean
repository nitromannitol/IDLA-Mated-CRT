import MatedCRT.Defs.Notation
import LatticeProb.Prob.ConvergenceInLawToFunction

/-!
# Convergence in probability from convergence in law along subsequences

The final deduction of Berestycki-Gwynne (arXiv:2003.10320, proof of Theorem 1.2, lines 3630-3665) is a
sub-subsequence argument: along every sequence `ε_n → 0` there is a subsequence along which the pair
(environment data, observable) converges in law to (data, function of the data); since the limit does
not depend on the subsequence, the whole family converges, and convergence in law to a function of the
first coordinate is convergence in probability.

This file formalizes that last step, for a real-valued observable `R ε` and the convergence in
probability of `MatedCRT.TendstoInProbability`.

## Main results

* `tendstoInProbability_of_subseq`: the sub-subsequence principle for `TendstoInProbability`: if along
  every sequence of positive parameters tending to `0` some subsequence converges in measure, then
  `X ε → Y` in probability as `ε → 0⁺`.
* `tendstoInProbability_of_subseq_tendsto_law`: if along every such sequence some subsequence has the
  pairs `(X, R ε)` converging in law to `(X, u X)` with `u` bounded measurable, and `Y = u (X)` almost
  surely, then `R ε → Y` in probability.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace MatedCRT

/-- **Sub-subsequence principle for convergence in probability.** If along every sequence of positive
parameters tending to `0` there is a subsequence along which `X (ε_k) → Y` in measure, then
`X ε → Y` in probability as `ε → 0⁺` (in the sense of `TendstoInProbability`). -/
theorem tendstoInProbability_of_subseq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (Y : Ω → ℝ)
    (h : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoInMeasure P (fun k => X (e (φ k))) atTop Y) :
    TendstoInProbability P X Y := by
  intro δ hδ
  rw [tendsto_iff_seq_tendsto]
  intro e he
  have hpos : ∀ᶠ n in atTop, 0 < e n := he.eventually (eventually_mem_nhdsWithin)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have he' : Tendsto (fun n => e (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    he.comp (tendsto_add_atTop_nat N)
  have he'0 : Tendsto (fun n => e (n + N)) atTop (𝓝 (0 : ℝ)) := he'.mono_right nhdsWithin_le_nhds
  have hpos' : ∀ n, 0 < e (n + N) := fun n => hN _ (Nat.le_add_left N n)
  rw [← tendsto_add_atTop_iff_nat N]
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨φ, hφ, hconv⟩ := h (fun k => e (ns k + N)) (fun k => hpos' _)
    (he'0.comp hns)
  refine ⟨φ, ?_⟩
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv _ hδ')
    (fun _ => zero_le) (fun k => ?_)
  refine measure_mono (fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hω.le

/-- **Convergence in law along subsequences to a function of the data gives convergence in
probability.** `X : Ω → S` is the data, `R ε` bounded measurable observables, `u` a bounded measurable
function of the data and `Y = u (X)` almost surely. If along every sequence of positive parameters
tending to `0` there is a subsequence along which `(X, R ε_k) → (X, u X)` in law (integrals of bounded
continuous functions on `S × ℝ`), then `R ε → Y` in probability as `ε → 0⁺`. -/
theorem tendstoInProbability_of_subseq_tendsto_law {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → S} (hX : Measurable X)
    {R : ℝ → Ω → ℝ} (hR : ∀ ε, 0 < ε → Measurable (R ε)) {u : S → ℝ} (hu : Measurable u)
    {C : ℝ} (hC : 0 ≤ C) (hRC : ∀ ε, 0 < ε → ∀ ω, |R ε ω| ≤ C) (huC : ∀ x, |u x| ≤ C)
    {Y : Ω → ℝ} (hY : Y =ᵐ[P] fun ω => u (X ω))
    (hlaw : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : (S × ℝ) →ᵇ ℝ,
        Tendsto (fun k => ∫ ω, f (X ω, R (e (φ k)) ω) ∂P) atTop
          (𝓝 (∫ ω, f (X ω, u (X ω)) ∂P))) :
    TendstoInProbability P R Y := by
  refine tendstoInProbability_of_subseq P R Y (fun e hepos he0 => ?_)
  obtain ⟨φ, hφ, hf⟩ := hlaw e hepos he0
  refine ⟨φ, hφ, ?_⟩
  have key := LatticeProb.tendstoInMeasure_of_tendsto_integral_graph P hX
    (R := fun k => R (e (φ k))) (fun k => hR _ (hepos _)) hu hC (fun k ω => hRC _ (hepos _) ω) huC hf
  exact key.congr (fun _ => EventuallyEq.rfl) hY.symm

end MatedCRT
