import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-!
# Adapted tube events and the simple Markov property of planar Brownian motion

Two tools for the tube (support-theorem) argument behind the Brownian disconnection estimate in
the proof of the invariance principle of Gwynne-Miller-Sheffield (Lemma 3.14 of
arXiv:1807.07515).

* `measurableSet_forall_le_lt_canonicalFiltration`: for a functional `Φ t ω` that is adapted at
  every time `t ≤ T` and continuous in `t`, the tube event `{ω | ∀ t ≤ T, Φ t ω < c}` belongs to
  the canonical filtration at time `T`. A continuous function attains its maximum on `[0, T]`,
  so the event is a countable union of countable intersections of adapted events.
* `planarBrownian_inter_shift_preimage`: the simple Markov property of planar Brownian motion at
  a deterministic time `s`, `P_x(A ∩ θ_s⁻¹ B) = ∫_A P_{ω s}(B) dP_x` for `A` in the canonical
  filtration at time `s`; `le_planarBrownian_inter_shift_preimage` is its lower-bound form.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology
open HarmonicBalls

namespace MatedCRT

/-- **Tube events are adapted.** If `Φ t` is measurable for the canonical filtration at time
`T` for every `t ≤ T`, and `t ↦ Φ t ω` is continuous for every path `ω`, then the event
`{ω | ∀ t ≤ T, Φ t ω < c}` is measurable for the canonical filtration at time `T`. -/
theorem measurableSet_forall_le_lt_canonicalFiltration {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] (T : ℝ≥0) (Φ : ℝ≥0 → ContinuousPath α → ℝ)
    (hΦm : ∀ t ≤ T, Measurable[ContinuousPath.canonicalFiltration (alpha := α) T] (Φ t))
    (hΦc : ∀ ω, Continuous fun t => Φ t ω) (c : ℝ) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) T]
      {ω | ∀ t ≤ T, Φ t ω < c} := by
  have hset : {ω : ContinuousPath α | ∀ t ≤ T, Φ t ω < c} =
      ⋃ m : ℕ, ⋂ q : ℚ, {ω | Φ (min (Real.toNNReal q) T) ω ≤ c - 1 / ((m : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro h
      obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_isMaxOn
        (nonempty_Icc.mpr zero_le) (hΦc ω).continuousOn
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr (h t₀ ht₀.2))
      refine ⟨m, fun q => ?_⟩
      have h1 : Φ (min (Real.toNNReal q) T) ω ≤ Φ t₀ ω :=
        hmax ⟨zero_le, min_le_right _ _⟩
      linarith
    · rintro ⟨m, hm⟩ t ht
      have hcont : Continuous fun x : ℝ => Φ (min (Real.toNNReal x) T) ω :=
        (hΦc ω).comp (continuous_real_toNNReal.min continuous_const)
      have hcl : IsClosed {x : ℝ | Φ (min (Real.toNNReal x) T) ω ≤ c - 1 / ((m : ℝ) + 1)} :=
        isClosed_le hcont continuous_const
      have hsub : closure (range (Rat.cast : ℚ → ℝ)) ⊆
          {x : ℝ | Φ (min (Real.toNNReal x) T) ω ≤ c - 1 / ((m : ℝ) + 1)} :=
        hcl.closure_subset_iff.mpr (by rintro _ ⟨q, rfl⟩; exact hm q)
      have hx := hsub (by rw [Rat.denseRange_cast.closure_range]; trivial : (t : ℝ) ∈ _)
      have hle : Φ t ω ≤ c - 1 / ((m : ℝ) + 1) := by
        simpa only [mem_ofPred_eq, Real.toNNReal_coe, min_eq_left ht] using hx
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  rw [hset]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q => ?_
  exact hΦm _ (min_le_right _ _) measurableSet_Iic

/-- **Simple Markov property of planar Brownian motion at a deterministic time.** For an event
`A` of the canonical filtration at time `s` and a measurable set of paths `B`,
`P_x(A ∩ θ_s⁻¹ B) = ∫_A P_{ω s}(B) dP_x`. -/
theorem planarBrownian_inter_shift_preimage (x : ℂ) (s : ℝ≥0) {A : Set (ContinuousPath ℂ)}
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) s] A)
    {B : Set (ContinuousPath ℂ)} (hB : MeasurableSet B) :
    planarBrownianMotion x (A ∩ ContinuousPath.shift s ⁻¹' B) =
      ∫⁻ ω in A, planarBrownianMotion (ω s) B ∂(planarBrownianMotion x) := by
  have h :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup x s A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at h
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m B) h
  rw [Measure.map_apply (ContinuousPath.measurable_shift_fixed s) hB,
    Measure.restrict_apply (ContinuousPath.measurable_shift_fixed s hB),
    Measure.bind_apply hB (Kernel.aemeasurable _)] at happ
  rw [inter_comm, happ]
  rfl

/-- **Markov chaining, lower-bound form.** If `p ≤ P_{ω s}(B)` for every `ω ∈ A`, where `A` is an
event of the canonical filtration at time `s`, then `p · P_x(A) ≤ P_x(A ∩ θ_s⁻¹ B)`. -/
theorem le_planarBrownian_inter_shift_preimage (x : ℂ) (s : ℝ≥0) {A : Set (ContinuousPath ℂ)}
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) s] A)
    {B : Set (ContinuousPath ℂ)} (hB : MeasurableSet B) {p : ℝ≥0∞}
    (hp : ∀ ω ∈ A, p ≤ planarBrownianMotion (ω s) B) :
    p * planarBrownianMotion x A ≤
      planarBrownianMotion x (A ∩ ContinuousPath.shift s ⁻¹' B) := by
  rw [planarBrownian_inter_shift_preimage x s hA hB, ← setLIntegral_const]
  exact setLIntegral_mono
    ((planarBrownianMotion.measurable_coe hB).comp (continuous_eval_const s).measurable) hp

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.measurableSet_forall_le_lt_canonicalFiltration
#print axioms MatedCRT.planarBrownian_inter_shift_preimage
#print axioms MatedCRT.le_planarBrownian_inter_shift_preimage
