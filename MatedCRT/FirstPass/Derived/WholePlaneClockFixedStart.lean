import MatedCRT.FirstPass.Derived.LQGClockApproxMeasurable
import HarmonicBalls.Defs.Brownian
import LatticeProb.Prob.UniformLimitAfterPositiveTimes
import LatticeProb.Bonanno.LQGMetric.Statement.Field

/-!
# Local convergence of the dyadic clocks from the fixed-start annealed statement

Berestycki (2015) proves the convergence of the approximating Liouville clocks
`A_ε(t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(B_s)} ds` for a **fixed** starting point `y`, almost surely for
the joint law of the field and the Brownian path. The reference-environment wrapper of the
whole-plane clock instead binds the quenched statement: almost surely in the field, from
Lebesgue-almost every start, almost surely in the path, the dyadic clocks are uniformly Cauchy on
compact time intervals.

This file derives the quenched statement from the fixed-start annealed one by Fubini's theorem.
The swap of the field and the start uses the joint measurability of the event "the dyadic clocks
are uniformly Cauchy on `[0, T]`" in the field and the path.

## Main statements

* `ae_ae_ae_of_ae_prod_kernel`: for a measurable set `S ⊆ X × Z`, an s-finite kernel `κ : Y → Z`,
  if for `ν`-a.e. `y` the set `S` has full `μ ⊗ κ y`-measure, then for `μ`-a.e. `x`, `ν`-a.e. `y`
  and `κ y`-a.e. `z`, `(x, z) ∈ S`.
* `measurableSet_uniformCauchySeqOn_of_continuous`: measurability of a uniform-Cauchy event for
  functions continuous in time.
* `measurableSet_uniformCauchySeqOn_lqgClockApprox_field`: joint measurability of the
  uniform-Cauchy event in the field and the path.
* `ae_ae_ae_uniformCauchySeqOn_lqgClockApprox_of_fixedStart`: the quenched statement from the
  fixed-start annealed one.
* `ae_localUniformCauchy_wholePlane_of_fixedStart`: the same, in the form of the local clock
  hypothesis of the whole-plane reference-environment wrapper.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter HarmonicBalls LQGMetric MarkovProcess
open MatedCRT.LQGClockApproxMeasurable
open scoped NNReal

namespace MatedCRT.Sec1

/-- **Fubini for a kernel family.** If, for `ν`-almost every `y`, the measurable set `S` has full
measure for the product `μ ⊗ κ y`, then for `μ`-almost every `x`, for `ν`-almost every `y` and
`κ y`-almost every `z`, the pair `(x, z)` lies in `S`. -/
theorem ae_ae_ae_of_ae_prod_kernel {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] {S : Set (X × Z)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂ν, ∀ᵐ p ∂(μ.prod (κ y)), p ∈ S) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ∀ᵐ z ∂(κ y), (x, z) ∈ S := by
  have h1 : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ∀ᵐ z ∂(κ y), (x, z) ∈ S :=
    h.mono fun y hy => Measure.ae_ae_of_ae_prod hy
  have hT : MeasurableSet {q : (Y × X) × Z | (q.1.2, q.2) ∉ S} :=
    (hS.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).compl
  let κ' : Kernel (Y × X) Z := κ.comap (Prod.fst : Y × X → Y) measurable_fst
  have hf : Measurable fun q : Y × X => κ' q
      (Prod.mk q ⁻¹' {q : (Y × X) × Z | (q.1.2, q.2) ∉ S}) :=
    Kernel.measurable_kernel_prodMk_left hT
  have hmeas : MeasurableSet {q : Y × X | ∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S} := by
    have hEq : {q : Y × X | ∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S} =
        (fun q : Y × X => κ' q
          (Prod.mk q ⁻¹' {q : (Y × X) × Z | (q.1.2, q.2) ∉ S})) ⁻¹' {0} := by
      ext q
      show (∀ᵐ z ∂(κ q.1), (q.2, z) ∈ S) ↔ κ' q {z | (q.2, z) ∉ S} = 0
      rw [Kernel.comap_apply, ae_iff]
    rw [hEq]
    exact hf (measurableSet_singleton 0)
  exact (Measure.ae_ae_comm hmeas).1 h1

/-- **Measurability of a uniform-Cauchy event.** For a family of functions `g ω k : ℝ≥0 → ℝ` that
are continuous in time and measurable in `ω` at every time, the event that `(g ω k)_k` is uniformly
Cauchy on a set of times `s` is measurable (continuity reduces it to countably many times). -/
theorem measurableSet_uniformCauchySeqOn_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℕ → ℝ≥0 → ℝ) (hg : ∀ ω k, Continuous (g ω k))
    (hm : ∀ k t, Measurable fun ω => g ω k t) (s : Set ℝ≥0) :
    MeasurableSet {ω | UniformCauchySeqOn (g ω) atTop s} := by
  have hEq : {ω | UniformCauchySeqOn (g ω) atTop s} =
      ⋂ j : ℕ, ⋃ N : ℕ, ⋂ m ≥ N, ⋂ n ≥ N,
        {ω | ∃ t ∈ s, ((j : ℝ) + 1)⁻¹ < |g ω m t - g ω n t|}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, Metric.uniformCauchySeqOn_iff, mem_iInter, mem_iUnion,
      mem_compl_iff, not_exists, not_and, not_lt, Real.dist_eq]
    constructor
    · intro h j
      obtain ⟨N, hN⟩ := h _ (by positivity : (0 : ℝ) < ((j : ℝ) + 1)⁻¹)
      exact ⟨N, fun m hm n hn t ht => (hN m hm n hn t ht).le⟩
    · intro h ε hε
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h j
      refine ⟨N, fun m hm n hn t ht => ?_⟩
      have h1 := hN m hm n hn t ht
      rw [one_div] at hj
      exact h1.trans_lt hj
  rw [hEq]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        (LatticeProb.measurableSet_exists_mem_lt_of_continuous
          (fun ω t => |g ω m t - g ω n t|) (fun ω => ((hg ω m).sub (hg ω n)).abs)
          (fun t => ((hm m t).sub (hm n t)).abs) s _).compl

/-- **Joint measurability of the uniform-Cauchy event.** If the circle averages `F x ε` at every
dyadic scale are continuous in the point and jointly measurable in the field and the point, then
the event that the dyadic approximating clocks of the field `x` along the path `b` are uniformly
Cauchy on a set of times `s` is measurable in `(x, b)`. -/
theorem measurableSet_uniformCauchySeqOn_lqgClockApprox_field {X : Type*} [MeasurableSpace X]
    {γ : ℝ} {F : X → ℝ → ℂ → ℝ}
    (hcont : ∀ x k, Continuous (F x (HarmonicBalls.dyadicScale k)))
    (hm : ∀ k, Measurable fun q : X × ℂ => F q.1 (HarmonicBalls.dyadicScale k) q.2)
    (s : Set ℝ≥0) :
    MeasurableSet {p : X × ContinuousPath ℂ | UniformCauchySeqOn
      (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop s} := by
  have hA : ∀ k t, Measurable fun p : X × ContinuousPath ℂ =>
      lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t := fun k t => by
    have h0 := measurable_lqgClockApprox_field_path_time_of_scale (c := F) γ (hm k)
    have h1 : Measurable fun p : X × ContinuousPath ℂ => (p.1, p.2, t) :=
      measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
    exact h0.comp h1
  exact measurableSet_uniformCauchySeqOn_of_continuous
    (fun (p : X × ContinuousPath ℂ) (k : ℕ) (t : ℝ≥0) =>
      lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)
    (fun (p : X × ContinuousPath ℂ) k =>
      continuous_lqgClockApprox_field F γ _ p.1 (hcont p.1 k) p.2) hA s

/-- **Quenched local convergence from the fixed-start annealed statement.** Suppose that for
every horizon `T`, from Lebesgue-almost every start `y`, the dyadic approximating clocks of the
field `F ω` along the path `b` are uniformly Cauchy on `[0, T]` for almost every `(ω, b)` under the
product of the field law and planar Brownian motion started at `y` (Berestycki 2015, fixed starting
point). Then almost surely in the field, from Lebesgue-almost every start, almost surely in the
path, the dyadic clocks are uniformly Cauchy on every `[0, T]`. -/
theorem ae_ae_ae_uniformCauchySeqOn_lqgClockApprox_of_fixedStart {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P'] {γ : ℝ} {F : Ω' → ℝ → ℂ → ℝ}
    (hcont : ∀ ω k, Continuous (F ω (HarmonicBalls.dyadicScale k)))
    (hm : ∀ k, Measurable fun q : Ω' × ℂ => F q.1 (HarmonicBalls.dyadicScale k) q.2)
    (hfix : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T)) :
    ∀ᵐ ω ∂P', ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ T : ℝ≥0,
      UniformCauchySeqOn (fun k t => lqgClockApprox γ (F ω) (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 T) := by
  set S : Set (Ω' × ContinuousPath ℂ) := {p | ∀ N : ℕ, UniformCauchySeqOn
    (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
      (Icc 0 (N : ℝ≥0))} with hSdef
  have hS : MeasurableSet S := by
    have hEq : S = ⋂ N : ℕ, {p : Ω' × ContinuousPath ℂ | UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
          (Icc 0 (N : ℝ≥0))} := by
      ext p
      simp only [hSdef, mem_ofPred_eq, mem_iInter]
    rw [hEq]
    exact MeasurableSet.iInter fun N =>
      measurableSet_uniformCauchySeqOn_lqgClockApprox_field hcont hm _
  have h1 : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)), p ∈ S := by
    filter_upwards [ae_all_iff.2 fun N : ℕ => hfix N] with y hy
    exact ae_all_iff.2 hy
  filter_upwards [ae_ae_ae_of_ae_prod_kernel planarBrownianMotion hS h1] with ω hω
  filter_upwards [hω] with y hy
  filter_upwards [hy] with b hb T
  have hb' : ∀ N : ℕ, UniformCauchySeqOn
      (fun k t => lqgClockApprox γ (F ω) (HarmonicBalls.dyadicScale k) b t) atTop
        (Icc 0 (N : ℝ≥0)) := hb
  exact (hb' ⌈T⌉₊).mono (Icc_subset_Icc le_rfl (Nat.le_ceil T))

/-- **The local clock hypothesis of the whole-plane wrapper from the fixed-start statement.** For
a measurable field `Y'` and a version `c'` of its circle averages that is continuous at positive
radii and jointly measurable, the quenched local hypothesis (almost surely in the field, for every
horizon `h` and every closed disc avoiding the origin, from Lebesgue-almost every start, almost
surely in the path: if the path stays in the disc during `[0, h]`, the dyadic clocks are uniformly
Cauchy on `[0, h]`) follows from the fixed-start annealed uniform-Cauchy statement. -/
theorem ae_localUniformCauchy_wholePlane_of_fixedStart {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [SFinite P'] {γ : ℝ} {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ}
    (hY : Measurable Y')
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2))
    (hfix : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T)) :
    ∀ᵐ ω' ∂P', ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
      ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
        UniformCauchySeqOn
          (fun k t => lqgClockApprox γ (c' (Y' ω')) (HarmonicBalls.dyadicScale k) b t)
          atTop (Icc 0 h) := by
  have hc : ∀ x k, Continuous (c' x (HarmonicBalls.dyadicScale k)) := fun x k =>
    (hcont x).comp_continuous (continuous_const.prodMk continuous_id)
      fun z => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ z⟩
  have hm : ∀ k, Measurable fun q : Ω' × ℂ =>
      c' (Y' q.1) (HarmonicBalls.dyadicScale k) q.2 := fun k =>
    hmeas.comp (((measurable_const : Measurable fun _ : Ω' × ℂ =>
      (⟨HarmonicBalls.dyadicScale k, HarmonicBalls.dyadicScale_pos k⟩ : Ioi (0 : ℝ))).prodMk
        measurable_snd).prodMk (hY.comp measurable_fst))
  filter_upwards [ae_ae_ae_uniformCauchySeqOn_lqgClockApprox_of_fixedStart
    (F := fun ω => c' (Y' ω)) (fun ω k => hc (Y' ω) k) hm hfix] with ω hω h a r _
  filter_upwards [hω] with y hy
  filter_upwards [hy] with b hb _
  exact hb h

end MatedCRT.Sec1
