import MatedCRT.FirstPass.Derived.MarkovTimeChangeIdentification

/-!
# Proportional clocks of Markovian time-changed planar Brownian motions with a common invariant measure

Berestycki–Gwynne, Proposition 7.10, from the Markov time-change property alone (up to the three Revuz inputs
`RevuzUniquenessInput`, `RevuzInvariantInput`, `TimeChangeInvariantUniqueInput`).

* `IsMarkovTCBM.exists_isPCAF_regularize_rawClock`: a Markovian time-changed planar Brownian motion `P` has a
  threshold `m ∈ (0, ∞)` and measurable functionals `F_s` of the clock-read path reading off its inverse crossing
  clock, such that the regularized half-clock `A = regularize (rawClock F)` is a positive continuous additive
  functional of planar Brownian motion and the time change `B ∘ τ` (`τ_t = clockInverse A t`) has the
  one-dimensional marginals of `P`;
* `exists_const_mul_of_isMarkovTCBM`: for two Markovian time-changed planar Brownian motions `P₁, P₂` with a
  common locally finite invariant measure `μ ≠ 0`, the clocks of the previous item satisfy `A₁ = c A₂` almost
  surely from every starting point, for some `c > 0`;
* `ae_eval_clockInverse_eq_of_isMarkovTCBM`: under the same hypotheses, `B (τ¹_u) = B (τ²_{u / c})` for all `u`,
  almost surely from every starting point.

The clocks are packaged existentially: the threshold `m_i` and the functionals `F_i` come with every property
that `exists_const_mul_of_isInvariantFor` takes as a hypothesis (measurability of `F_i`, the law of the
clock-read path, goodness of the crossing clock, strictness of the inverse crossing clock, `F_i` reads the inverse
crossing clock, and the PCAF property of `A_i`), together with the marginal identification of `P_i`.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- **The clock of a Markovian time-changed planar Brownian motion is a PCAF of planar Brownian motion.**
There are a threshold `m ∈ (0, ∞)` and measurable functionals `F_s` such that the clock-read path of the Euclidean
time-changed process has the law of `halfRead` of planar Brownian motion, the crossing clock is almost surely
good, the inverse crossing clock is almost surely strictly increasing and is read off the clock-read path by `F_s`,
the regularized half-clock `A = regularize (rawClock F)` is a positive continuous additive functional of planar
Brownian motion, and `P_z [X_t ∈ S] = P_z^{BM} [B (τ_t) ∈ S]` with `τ_t = clockInverse A t`. -/
theorem IsMarkovTCBM.exists_isPCAF_regularize_rawClock {P : PathLawFamily} (h : IsMarkovTCBM P) :
    ∃ (m : ℝ≥0∞) (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ), 0 < m ∧ m < ⊤ ∧
      (∀ s, Measurable (F s)) ∧
      (∀ z : ℂ, (euclidFamily P (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
        (LatticeProb.clockRead m) = (planarLaw z).map halfRead) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.InvClockStrict m x) ∧
      (∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m x s).toReal = F s fun t => LatticeProb.clockPath m (fun u => x u) t) ∧
      IsPCAF planarLaw (regularize (rawClock F)) ∧
      ∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F)) t w) ∈ S} := by
  obtain ⟨m, hm0, hmt, hmap, hgood, hstrict, hF⟩ := h.exists_goodAdaptedClock
  choose F hFm hFA hFsh hFad using hF
  have hS : ∀ y (t s : ℝ≥0), ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      (LatticeProb.pathClockInv m x (t + s)).toReal = (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q) :=
    fun y t s => hFsh s y t
  refine ⟨m, F, hm0, hmt, hFm, hmap, hgood, hstrict, hFA, ?_,
    fun z t _ hS' => measure_eval_eq_clockInverse hFm hmap hgood hstrict hFA z t hS'⟩
  exact isPCAF_regularize_rawClock hFm
    (fun z t => ae_halfRead_pathShift_mem_clockGoodSet hFm (hmap z) (hgood _) (hS _) t)
    (fun z t s => ae_halfRead_pathShift_mem_tset hFm (hmap z) (hgood _) (hS _) t s)
    (fun z t s => ae_halfRead_mem_rset hFm (hmap z) (hgood _) (hS _) t s)
    (fun z s => hFad s z)

/-- **Two Markovian time-changed planar Brownian motions with a common invariant measure have proportional
clocks** (Berestycki–Gwynne, Proposition 7.10, up to the three Revuz inputs).  Let `P₁, P₂` be Markovian
time-changed planar Brownian motions (Definition 7.2) and let `μ ≠ 0` be a locally finite measure invariant for
both (Definition 7.3).  Then there are thresholds `m_i ∈ (0, ∞)` and measurable functionals `F_i` reading off the
inverse crossing clocks of `P_i`, as in `IsMarkovTCBM.exists_isPCAF_regularize_rawClock`, whose regularized
half-clocks `A_i = regularize (rawClock F_i)` are PCAFs of planar Brownian motion with time changes having the
one-dimensional marginals of `P_i`, and a constant `c > 0` with `A₁ = c A₂` almost surely from every starting
point. -/
theorem exists_const_mul_of_isMarkovTCBM (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily} (hP₁ : IsMarkovTCBM P₁)
    (hP₂ : IsMarkovTCBM P₂) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ (m₁ m₂ : ℝ≥0∞) (F₁ F₂ : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ),
      0 < m₁ ∧ m₁ < ⊤ ∧ 0 < m₂ ∧ m₂ < ⊤ ∧
      (∀ s, Measurable (F₁ s)) ∧ (∀ s, Measurable (F₂ s)) ∧
      (∀ z : ℂ, (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
        (LatticeProb.clockRead m₁) = (planarLaw z).map halfRead) ∧
      (∀ z : ℂ, (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
        (LatticeProb.clockRead m₂) = (planarLaw z).map halfRead) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.GoodClock (LatticeProb.crossClock m₁ fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.GoodClock (LatticeProb.crossClock m₂ fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.InvClockStrict m₁ x) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.InvClockStrict m₂ x) ∧
      (∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m₁ x s).toReal = F₁ s fun t => LatticeProb.clockPath m₁ (fun u => x u) t) ∧
      (∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m₂ x s).toReal = F₂ s fun t => LatticeProb.clockPath m₂ (fun u => x u) t) ∧
      IsPCAF planarLaw (regularize (rawClock F₁)) ∧ IsPCAF planarLaw (regularize (rawClock F₂)) ∧
      (∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P₁ z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F₁)) t w) ∈ S}) ∧
      (∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P₂ z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F₂)) t w) ∈ S}) ∧
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ t,
        regularize (rawClock F₁) t ω = c * regularize (rawClock F₂) t ω := by
  obtain ⟨m₁, F₁, hm₁, hm₁', hF₁, hmap₁, hgood₁, hstrict₁, hFA₁, hA₁, hmarg₁⟩ :=
    hP₁.exists_isPCAF_regularize_rawClock
  obtain ⟨m₂, F₂, hm₂, hm₂', hF₂, hmap₂, hgood₂, hstrict₂, hFA₂, hA₂, hmarg₂⟩ :=
    hP₂.exists_isPCAF_regularize_rawClock
  exact ⟨m₁, m₂, F₁, F₂, hm₁, hm₁', hm₂, hm₂', hF₁, hF₂, hmap₁, hmap₂, hgood₁, hgood₂, hstrict₁, hstrict₂,
    hFA₁, hFA₂, hA₁, hA₂, hmarg₁, hmarg₂,
    exists_const_mul_of_isInvariantFor hRU hRI hTU hF₁ hF₂ hmap₁ hmap₂ hgood₁ hgood₂ hstrict₁ hstrict₂
      hFA₁ hFA₂ hA₁ hA₂ hμ h₁ h₂⟩

/-- **The identification of the time-changed paths** (Berestycki–Gwynne, Proposition 7.10, up to the three Revuz
inputs): for two Markovian time-changed planar Brownian motions `P₁, P₂` with a common locally finite invariant
measure `μ ≠ 0`, with the clocks `A_i = regularize (rawClock F_i)` of
`IsMarkovTCBM.exists_isPCAF_regularize_rawClock`, there is `c > 0` such that, from every starting point, almost
surely `B (τ¹_u) = B (τ²_{u / c})` for all `u`, where `τ^i` is the right inverse of `A_i`. -/
theorem ae_eval_clockInverse_eq_of_isMarkovTCBM (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily} (hP₁ : IsMarkovTCBM P₁)
    (hP₂ : IsMarkovTCBM P₂) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ (m₁ m₂ : ℝ≥0∞) (F₁ F₂ : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ),
      0 < m₁ ∧ m₁ < ⊤ ∧ 0 < m₂ ∧ m₂ < ⊤ ∧
      (∀ s, Measurable (F₁ s)) ∧ (∀ s, Measurable (F₂ s)) ∧
      (∀ z : ℂ, (euclidFamily P₁ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
        (LatticeProb.clockRead m₁) = (planarLaw z).map halfRead) ∧
      (∀ z : ℂ, (euclidFamily P₂ (toEuclid z) : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))).map
        (LatticeProb.clockRead m₂) = (planarLaw z).map halfRead) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.GoodClock (LatticeProb.crossClock m₁ fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.GoodClock (LatticeProb.crossClock m₂ fun u => x u)) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.InvClockStrict m₁ x) ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        LatticeProb.InvClockStrict m₂ x) ∧
      (∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₁ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m₁ x s).toReal = F₁ s fun t => LatticeProb.clockPath m₁ (fun u => x u) t) ∧
      (∀ (s : ℝ≥0) y, ∀ᵐ x ∂(euclidFamily P₂ y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m₂ x s).toReal = F₂ s fun t => LatticeProb.clockPath m₂ (fun u => x u) t) ∧
      IsPCAF planarLaw (regularize (rawClock F₁)) ∧ IsPCAF planarLaw (regularize (rawClock F₂)) ∧
      (∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P₁ z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F₁)) t w) ∈ S}) ∧
      (∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
        (P₂ z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
          planarLaw z {w | w (clockInverse (regularize (rawClock F₂)) t w) ∈ S}) ∧
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ u,
        ω (clockInverse (regularize (rawClock F₁)) u ω) =
          ω (clockInverse (regularize (rawClock F₂)) (u / c) ω) := by
  obtain ⟨m₁, F₁, hm₁, hm₁', hF₁, hmap₁, hgood₁, hstrict₁, hFA₁, hA₁, hmarg₁⟩ :=
    hP₁.exists_isPCAF_regularize_rawClock
  obtain ⟨m₂, F₂, hm₂, hm₂', hF₂, hmap₂, hgood₂, hstrict₂, hFA₂, hA₂, hmarg₂⟩ :=
    hP₂.exists_isPCAF_regularize_rawClock
  exact ⟨m₁, m₂, F₁, F₂, hm₁, hm₁', hm₂, hm₂', hF₁, hF₂, hmap₁, hmap₂, hgood₁, hgood₂, hstrict₁, hstrict₂,
    hFA₁, hFA₂, hA₁, hA₂, hmarg₁, hmarg₂,
    ae_eval_clockInverse_eq_of_isInvariantFor hRU hRI hTU hF₁ hF₂ hmap₁ hmap₂ hgood₁ hgood₂ hstrict₁
      hstrict₂ hFA₁ hFA₂ hA₁ hA₂ hμ h₁ h₂⟩

end MatedCRT
