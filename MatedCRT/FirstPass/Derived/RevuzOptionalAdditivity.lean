import MatedCRT.FirstPass.Derived.PlanarOptionalTimeStrongMarkov
import MatedCRT.FirstPass.Derived.RevuzShiftAdditivity
import MatedCRT.FirstPass.Derived.RevuzLebesgueInvariance

/-!
# Additivity of a positive continuous additive functional at an optional time

Let `A` be a positive continuous additive functional (PCAF) of planar Brownian motion and `Ā` its
rational-time regularization (`regularize A`). The additivity `A (t + s) = A t + A s ∘ θ_t` holds
almost surely for each *fixed* time `t`. This file proves it at an *optional time* `T` of the
natural filtration (`{T < t} ∈ F⁰_t`): almost surely on `{T < ∞}`, for every `s`,
`Ā (T + s) ω = Ā T ω + Ā s (θ_T ω)` (Revuz–Yor (1999), X.1; Fukushima–Oshima–Takeda (2011),
Section A.3).

No perfection theorem is used. The proof:
1. `Ā` is jointly measurable in the time and the path, and right-continuous in the time.
2. The set `Gd` of pairs `(v, ω)` with `Ā (v + q) ω = Ā v ω + Ā q (θ_v ω)` for all rationals
   `q ≥ 0` is measurable, and each fixed-`v` section has full probability; by Tonelli, almost
   surely `(v, ω) ∈ Gd` for Lebesgue-almost every `v`.
3. The event "`Ā 0 = 0` and `(v, ·) ∈ Gd` for almost every `v`" is measurable and has
   probability one under every starting point, so it holds for `θ_T ω` (strong Markov property
   at optional times, transfer form).
4. Pathwise: for almost every `q` both `(T + q, ω)` and `(q, θ_T ω)` lie in `Gd`; then
   `D(t) := Ā (T + t) ω - Ā t (θ_T ω)` satisfies `D(q + p) = D(q)` for rationals `p`, hence
   `D` is constant on `[q, ∞)` by right-continuity, and `D(t) = D(0) = Ā T ω` by letting such
   `q` decrease to `0`.

## Main results

* `measurable_regularize_uncurry`, `continuousWithinAt_regularize_Ici`.
* `regularizeAddSet`, `measurableSet_regularizeAddSet`, `ae_ae_mem_regularizeAddSet`.
* `regularize_add_shift_of_ae`: the pathwise step.
* `ae_regularize_add_shift_optionalTime`: additivity at an optional time.
* `ae_add_regularize_shift_optionalTime`: the same with the raw clock on the unshifted path.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The regularized clock is jointly measurable in the time and the path. -/
theorem measurable_regularize_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable (fun p : ℝ≥0 × ContinuousPath ℂ => regularize A p.1 p.2) := by
  classical
  have hCm : MeasurableSet {p : ℝ≥0 × ContinuousPath ℂ |
      ∀ a b : ℚ≥0, a ≤ b → A a p.2 ≤ A b p.2} := by
    have hC : MeasurableSet {ω : ContinuousPath ℂ | ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω} := by
      have : {ω : ContinuousPath ℂ | ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω} =
          ⋂ a : ℚ≥0, ⋂ b : ℚ≥0, {ω | a ≤ b → A a ω ≤ A b ω} := by
        ext ω
        simp
      rw [this]
      refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
      by_cases hab : a ≤ b
      · simpa [hab] using measurableSet_le (hA _) (hA _)
      · simp [hab]
    exact measurable_snd hC
  have hFm : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      ⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    refine Measurable.iInf fun q => Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_fst measurable_const
    · exact ((hA _).comp measurable_snd).coe_nnreal_ennreal
  have heq : (fun p : ℝ≥0 × ContinuousPath ℂ =>
        ⨅ q : {q : ℚ≥0 // p.1 < (q : ℝ≥0)}, A (q.1 : ℝ≥0) p.2) =
      fun p => (⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤).toNNReal := by
    funext p
    have hne := nonempty_regularize_index p.1
    have hF : (⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤) =
        ((⨅ q : {q : ℚ≥0 // p.1 < (q : ℝ≥0)}, A (q.1 : ℝ≥0) p.2 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_iInf, iInf_subtype]
      refine iInf_congr fun q => ?_
      exact (iInf_eq_if _).symm
    rw [hF, ENNReal.toNNReal_coe]
  unfold regularize
  refine Measurable.ite hCm ?_ measurable_const
  rw [heq]
  exact hFm.ennreal_toNNReal

/-- The regularized clock is right-continuous in the time, along every path. -/
theorem continuousWithinAt_regularize_Ici (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0)
    (ω : ContinuousPath ℂ) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => regularize A u ω) (Ici t) t := by
  by_cases h : ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω
  · have hval : ∀ u, regularize A u ω = ⨅ q : {q : ℚ≥0 // u < (q : ℝ≥0)}, A (q.1 : ℝ≥0) ω := by
      intro u
      unfold regularize
      split_ifs
      rfl
    have hmono := regularize_monotone A ω
    unfold ContinuousWithinAt
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ha' : a < regularize A t ω := ha
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact ha'.trans_le (hmono hu)
    · have hne := nonempty_regularize_index t
      have ha' : regularize A t ω < a := ha
      rw [hval t] at ha'
      replace ha := ha'
      obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt ha
      filter_upwards [inter_mem_nhdsWithin (Ici t) (Iio_mem_nhds q.2)] with u hu
      have hne' := nonempty_regularize_index u
      rw [hval u]
      exact (ciInf_le (OrderBot.bddBelow _)
        (⟨q.1, hu.2⟩ : {q : ℚ≥0 // u < (q : ℝ≥0)})).trans_lt hq
  · have hzero : ∀ u, regularize A u ω = 0 := by
      intro u
      unfold regularize
      split_ifs
      rfl
    simp only [hzero]
    exact continuousWithinAt_const

/-- The pairs `(v, ω)` at which the regularized clock is additive at time `v` against every
rational time: `Ā (v + q) ω = Ā v ω + Ā q (θ_v ω)` for all `q ∈ ℚ≥0`. -/
def regularizeAddSet (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Set (ℝ≥0 × ContinuousPath ℂ) :=
  {p | ∀ q : ℚ≥0, regularize A (p.1 + q) p.2 =
    regularize A p.1 p.2 + regularize A q (ContinuousPath.shift p.1 p.2)}

theorem measurableSet_regularizeAddSet {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) : MeasurableSet (regularizeAddSet A) := by
  have hR := measurable_regularize_uncurry hA
  have hS : Measurable fun p : ℝ≥0 × ContinuousPath ℂ => ContinuousPath.shift p.1 p.2 :=
    (ContinuousPath.continuous_shift (alpha := ℂ)).measurable
  have hset : regularizeAddSet A = ⋂ q : ℚ≥0, {p : ℝ≥0 × ContinuousPath ℂ |
      regularize A (p.1 + q) p.2 =
        regularize A p.1 p.2 + regularize A q (ContinuousPath.shift p.1 p.2)} := by
    ext p
    simp [regularizeAddSet]
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  have hf : Measurable fun p : ℝ≥0 × ContinuousPath ℂ => regularize A (p.1 + q) p.2 :=
    hR.comp ((measurable_fst.add_const _).prodMk measurable_snd)
  have hg : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      regularize A p.1 p.2 + regularize A q (ContinuousPath.shift p.1 p.2) :=
    hR.add ((measurable_regularize hA _).comp hS)
  exact (hf.prodMk hg) measurableSet_diagonal

/-- **Tonelli step.** Almost surely, `(v, ω)` lies in `regularizeAddSet A` for Lebesgue-almost
every time `v ≥ 0` (times are indexed by `x ∈ ℝ` through `x.toNNReal`). -/
theorem ae_ae_mem_regularizeAddSet {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) :
    ∀ᵐ ω ∂planarLaw z, ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (x.toNNReal, ω) ∈ regularizeAddSet A := by
  have hS : MeasurableSet {p : ℝ × ContinuousPath ℂ | (p.1.toNNReal, p.2) ∈ regularizeAddSet A} :=
    (measurable_real_toNNReal.prodMap measurable_id) (measurableSet_regularizeAddSet hA.meas)
  have hfix : ∀ x : ℝ, ∀ᵐ ω ∂planarLaw z, (x.toNNReal, ω) ∈ regularizeAddSet A := by
    intro x
    filter_upwards [ae_regularize_add_pathShift hA z x.toNNReal] with ω hω q
    have h := hω q
    rwa [show LatticeProb.pathShift ω x.toNNReal = ContinuousPath.shift x.toNNReal ω from
      congrFun (pathShift_eq_shift x.toNNReal) ω] at h
  exact (Measure.ae_ae_comm hS).1 (Eventually.of_forall hfix)

/-- The event "`Ā 0 = 0` and `(v, ·) ∈ regularizeAddSet A` for almost every `v`" is
measurable. -/
theorem measurableSet_regularizeAddGood {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    MeasurableSet {ω : ContinuousPath ℂ | regularize A 0 ω = 0 ∧
      volume {x : ℝ | (x.toNNReal, ω) ∉ regularizeAddSet A} = 0} := by
  have hS : MeasurableSet {p : ℝ × ContinuousPath ℂ | (p.1.toNNReal, p.2) ∈ regularizeAddSet A} :=
    (measurable_real_toNNReal.prodMap measurable_id) (measurableSet_regularizeAddSet hA)
  have hm : Measurable fun ω : ContinuousPath ℂ =>
      (volume : Measure ℝ) ((fun x => (x, ω)) ⁻¹'
        {p : ℝ × ContinuousPath ℂ | (p.1.toNNReal, p.2) ∈ regularizeAddSet A}ᶜ) :=
    measurable_measure_prodMk_right hS.compl
  exact ((measurable_regularize hA 0) (measurableSet_singleton 0)).inter
    (hm (measurableSet_singleton 0))

/-- The event of `measurableSet_regularizeAddGood` has probability one under every starting
point. -/
theorem planarLaw_regularizeAddGood_eq_one {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (y : ℂ) :
    planarLaw y {ω : ContinuousPath ℂ | regularize A 0 ω = 0 ∧
      volume {x : ℝ | (x.toNNReal, ω) ∉ regularizeAddSet A} = 0} = 1 := by
  rw [← prob_compl_eq_zero_iff (measurableSet_regularizeAddGood hA.meas)]
  have h : ∀ᵐ ω ∂planarLaw y, regularize A 0 ω = 0 ∧
      volume {x : ℝ | (x.toNNReal, ω) ∉ regularizeAddSet A} = 0 := by
    filter_upwards [hA.path y, ae_ae_mem_regularizeAddSet hA y] with ω hp hgood
    refine ⟨?_, ae_iff.1 hgood⟩
    rw [regularize_eq_of_continuous_monotone hp.2.1 hp.2.2]
    exact hp.1
  exact ae_iff.1 h

/-- **Pathwise step.** If `(v, ω)` and `(v, θ_τ ω)` lie in `regularizeAddSet A` for almost every
`v`, and `Ā 0 (θ_τ ω) = 0`, then `Ā (τ + s) ω = Ā τ ω + Ā s (θ_τ ω)` for every `s`. -/
theorem regularize_add_shift_of_ae {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ}
    (τ : ℝ≥0) (h1 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (x.toNNReal, ω) ∈ regularizeAddSet A)
    (h2 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      (x.toNNReal, ContinuousPath.shift τ ω) ∈ regularizeAddSet A)
    (h0 : regularize A 0 (ContinuousPath.shift τ ω) = 0) (s : ℝ≥0) :
    regularize A (τ + s) ω = regularize A τ ω + regularize A s (ContinuousPath.shift τ ω) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0 → ℝ, ∀ u, d u =
      (regularize A (τ + u) ω : ℝ) - regularize A u (ContinuousPath.shift τ ω) :=
    ⟨_, fun _ => rfl⟩
  have hdc : ∀ u, ContinuousWithinAt d (Ici u) u := by
    intro u
    have ha : ContinuousWithinAt (fun v => regularize A (τ + v) ω) (Ici u) u :=
      (continuousWithinAt_regularize_Ici A ω (τ + u)).comp
        (continuous_const.add continuous_id).continuousWithinAt
        (fun v hv => by simp only [mem_Ici] at hv ⊢; exact add_le_add_right hv τ)
    have hb := continuousWithinAt_regularize_Ici A (ContinuousPath.shift τ ω) u
    have hsub := (NNReal.continuous_coe.continuousAt.comp_continuousWithinAt ha).sub
      (NNReal.continuous_coe.continuousAt.comp_continuousWithinAt hb)
    have hfun : d = fun v => ((regularize A (τ + v) ω : ℝ≥0) : ℝ) -
        ((regularize A v (ContinuousPath.shift τ ω) : ℝ≥0) : ℝ) := funext hd
    rw [hfun]
    exact hsub
  have h1' : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ((x + (τ : ℝ)).toNNReal, ω) ∈ regularizeAddSet A :=
    (measurePreserving_add_right volume (τ : ℝ)).quasiMeasurePreserving.ae h1
  have hgood : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), 0 ≤ x →
      ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal := by
    filter_upwards [h1', h2] with x hx1 hx2 hx0 p
    have hτx : (x + τ).toNNReal = τ + x.toNNReal := by
      rw [Real.toNNReal_add hx0 τ.coe_nonneg, Real.toNNReal_coe, add_comm]
    rw [hτx] at hx1
    have e1 := hx1 p
    have e2 := hx2 p
    simp only at e1 e2
    rw [ContinuousPath.shift_add] at e2
    rw [hd, hd, ← add_assoc, e1, e2]
    push_cast
    ring
  have hstep : ∀ q : ℝ≥0, (∀ p : ℚ≥0, d (q + p) = d q) → ∀ u, q ≤ u → d u = d q := by
    intro q hq u hqu
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδu⟩ := Metric.continuousWithinAt_iff.1 (hdc u) ε hε
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn_nnreal
      (show u - q < u - q + δ.toNNReal from lt_add_of_pos_right _ (Real.toNNReal_pos.2 hδ))
    have hv : u ≤ q + (p : ℝ≥0) := ((tsub_lt_iff_left hqu).1 hp1).le
    have hp2' : ((p : ℝ≥0) : ℝ) < (u : ℝ) - q + δ := by
      have := NNReal.coe_lt_coe.2 hp2
      rwa [NNReal.coe_add, NNReal.coe_sub hqu, Real.coe_toNNReal _ hδ.le] at this
    have hvd : dist (q + (p : ℝ≥0)) u < δ := by
      rw [NNReal.dist_eq, abs_sub_lt_iff]
      have hv' : (u : ℝ) ≤ q + (p : ℝ≥0) := by exact_mod_cast hv
      push_cast
      constructor <;> linarith
    have hlt := hδu (mem_Ici.2 hv) hvd
    rw [hq p] at hlt
    rw [dist_comm]
    exact hlt.le
  have hfinal : d s = d 0 := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
    · rw [← hs]
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδ0⟩ := Metric.continuousWithinAt_iff.1 (hdc 0) ε hε
    have hcpos : 0 < min δ (s : ℝ) := lt_min hδ (by exact_mod_cast hs)
    obtain ⟨x, hx, hxg⟩ : ∃ x ∈ Ioo (0 : ℝ) (min δ (s : ℝ)),
        0 ≤ x → ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal := by
      by_contra hcon
      have hsub : Ioo (0 : ℝ) (min δ (s : ℝ)) ⊆
          {x | ¬(0 ≤ x → ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal)} :=
        fun x hx hg => hcon ⟨x, hx, hg⟩
      have hpos : 0 < volume (Ioo (0 : ℝ) (min δ (s : ℝ))) := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.2 (by linarith)
      exact hpos.ne' (measure_mono_null hsub (ae_iff.1 hgood))
    have hx0 : 0 ≤ x := hx.1.le
    have hxs : x.toNNReal ≤ s := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hx.2.le.trans (min_le_right _ _)
    have heq := hstep x.toNNReal (hxg hx0) s hxs
    have hclose := hδ0 (mem_Ici.2 zero_le) (show dist x.toNNReal 0 < δ by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, Real.coe_toNNReal _ hx0, abs_of_nonneg hx0]
      exact hx.2.trans_le (min_le_left _ _))
    rw [heq]
    exact hclose.le
  have hd0 : d 0 = regularize A τ ω := by
    rw [hd, add_zero, h0, NNReal.coe_zero, sub_zero]
  rw [hd0, hd] at hfinal
  have hreal : (regularize A (τ + s) ω : ℝ) =
      regularize A τ ω + regularize A s (ContinuousPath.shift τ ω) := by
    linarith
  exact_mod_cast hreal

/-- **Additivity of the regularized clock at an optional time.** Let `A` be a PCAF of planar
Brownian motion and `T` an optional time of the natural filtration. Almost surely on `{T < ∞}`,
`Ā (T + s) ω = Ā T ω + Ā s (θ_T ω)` for every `s`. -/
theorem ae_regularize_add_shift_optionalTime {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t}) :
    ∀ᵐ ω ∂planarLaw z, T ω < ⊤ → ∀ s : ℝ≥0,
      regularize A ((T ω).untopD 0 + s) ω =
        regularize A ((T ω).untopD 0) ω +
          regularize A s (ContinuousPath.shift ((T ω).untopD 0) ω) := by
  filter_upwards [ae_ae_mem_regularizeAddSet hA z,
    OptionalTime.ae_shift_mem_of_forall_planarLaw_eq_one z T hT
      (measurableSet_regularizeAddGood hA.meas) (planarLaw_regularizeAddGood_eq_one hA)]
    with ω h1 h2 hfin s
  obtain ⟨h0, hnull⟩ := h2 hfin
  exact regularize_add_shift_of_ae _ h1 (ae_iff.2 hnull) h0 s

/-- **Additivity at an optional time, raw clock on the unshifted path.** Almost surely on
`{T < ∞}`, `A (T + s) ω = A T ω + Ā s (θ_T ω)` for every `s`. -/
theorem ae_add_regularize_shift_optionalTime {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t}) :
    ∀ᵐ ω ∂planarLaw z, T ω < ⊤ → ∀ s : ℝ≥0,
      A ((T ω).untopD 0 + s) ω =
        A ((T ω).untopD 0) ω + regularize A s (ContinuousPath.shift ((T ω).untopD 0) ω) := by
  filter_upwards [hA.path z, ae_regularize_add_shift_optionalTime hA z T hT]
    with ω hp hadd hfin s
  have h := hadd hfin s
  rwa [regularize_eq_of_continuous_monotone hp.2.1 hp.2.2,
    regularize_eq_of_continuous_monotone hp.2.1 hp.2.2] at h

end MatedCRT
