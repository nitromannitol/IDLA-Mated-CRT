import MatedCRT.FirstPass.Derived.ExitTimeFieldSplit
import MatedCRT.FirstPass.Derived.ExitTimeGaussianIndependence
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# The field `h̃` on `B_{1/2}` as a function of the lateral field and the later radial increments

In the mating-of-trees coupling of a valid environment the circle-average field of the `γ`-quantum cone splits on
`B_{1/2}` as `h_ε(z) = B_{t₀} + h̃_ε(z)` with `t₀ = log (5/3)` (`splitTime`, `ae_hcirc_eq_add_hTilde`). Here `h̃`
(`hTilde`) is the circle average of the lateral part of the whole-plane GFF `X` plus the circle average of the
radial function `w ↦ (B_u - B_{t₀}) + γ u`, `u = log(1/|w|)`. This file shows that `h̃` depends on the radial
Brownian motion `B` only through its increments `v_u = B_{t₀ + u} - B_{t₀}` after `t₀`, measurably, and that `B_{t₀}`
is independent of every measurable function of `(X, v)` and of an independent Brownian path.

* `incrTilde γ X v ε z`: the circle average at `(z, ε)` of the lateral part of `X` plus the circle average of the
  radial function `w ↦ v̄_{u - t₀} + γ u`, `u = log(1/|w|)`, where `v̄ = gridRegularization v` is the upper limit of
  `v` along the grid approximations of mesh `1/(n+1)` from below. For a continuous path `v`, `v̄ = v`
  (`gridRegularization_of_continuous`); the regularization makes `incrTilde` measurable for the product σ-algebra
  on the paths `ℝ≥0 → ℝ`.
* (T1, `hTilde_eq_incrTilde`) for a continuous path `b`, `ε ∈ (0, 1/10)` and `z ∈ B_{1/2}`:
  `h̃_ε(z) = incrTilde γ X (u ↦ b_{t₀ + u} - b_{t₀}) ε z`, since every circle `∂B_ε(z)` lies in `B_{3/5}`, where
  `log(1/|w|) > t₀`.
* (T2, `measurable_incrTilde`, `measurable_incrTilde_scale`, `measurable_incrTilde_comp`) `(X, v, ε, z) ↦
  incrTilde γ X v ε z` is jointly measurable; at a fixed scale `ε`, `(ω, z) ↦ incrTilde γ (G ω).1 (G ω).2 ε z` is
  measurable for every measurable `G`, which is the hypothesis of the joint measurability of the approximating LQG
  clocks.
* (T3, `isMatingOfTreesCoupling_indepFun_splitTime_comp`,
  `MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_splitTime_comp`) under `P ⊗ Q`, `B_{t₀}` is independent of
  `Ψ (X, (B_{t₀ + u} - B_{t₀})_u, b)` for every measurable `Ψ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

/-! ## Grid regularization of paths -/

namespace TildeField

/-- The grid approximation `⌊(n+1) u⌋ / (n+1)` of a time `u ≥ 0` from below, with mesh `1/(n+1)`. -/
noncomputable def gridTime (n : ℕ) (u : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((⌊(u : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1))

theorem coe_gridTime (n : ℕ) (u : ℝ≥0) :
    ((gridTime n u : ℝ≥0) : ℝ) = (⌊(u : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1) :=
  Real.coe_toNNReal _ (by positivity)

/-- The grid approximations of `u` converge to `u`. -/
theorem tendsto_gridTime (u : ℝ≥0) : Tendsto (fun n : ℕ => gridTime n u) atTop (𝓝 u) := by
  have hlow : ∀ n : ℕ, (u : ℝ) - 1 / ((n : ℝ) + 1) ≤ ((gridTime n u : ℝ≥0) : ℝ) := by
    intro n
    rw [coe_gridTime]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have key : (u : ℝ) * ((n : ℝ) + 1) - 1 ≤ (⌊(u : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) := by
      linarith [Nat.lt_floor_add_one ((u : ℝ) * ((n : ℝ) + 1))]
    have e : (u : ℝ) - 1 / ((n : ℝ) + 1) = ((u : ℝ) * ((n : ℝ) + 1) - 1) / ((n : ℝ) + 1) := by
      rw [sub_div, mul_div_assoc, div_self hpos.ne', mul_one]
    rw [e]
    gcongr
  have hup : ∀ n : ℕ, ((gridTime n u : ℝ≥0) : ℝ) ≤ (u : ℝ) := by
    intro n
    rw [coe_gridTime, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact Nat.floor_le (by positivity)
  have hlim : Tendsto (fun n : ℕ => (u : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (u : ℝ)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (u : ℝ)
    simpa using this
  exact NNReal.tendsto_coe.1 (tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup)

/-- The grid regularization of a path `v : ℝ≥0 → ℝ`: the upper limit of `v` along the grid approximations of `u`
from below. It only reads `v` at the countably many grid times. -/
noncomputable def gridRegularization (v : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ :=
  limsup (fun n : ℕ => v (gridTime n u)) atTop

/-- The grid regularization of a continuous path is the path itself. -/
theorem gridRegularization_of_continuous {v : ℝ≥0 → ℝ} (hv : Continuous v) (u : ℝ≥0) :
    gridRegularization v u = v u :=
  ((hv.tendsto u).comp (tendsto_gridTime u)).limsup_eq

/-- The value of a path at a grid time is jointly measurable in the path (product σ-algebra) and the time. -/
theorem measurable_eval_gridTime (n : ℕ) :
    Measurable fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (gridTime n p.2) := by
  have hk : Measurable fun u : ℝ≥0 => ⌊(u : ℝ) * ((n : ℝ) + 1)⌋₊ :=
    Measurable.nat_floor (measurable_coe_nnreal_real.mul_const _)
  have hG : Measurable fun q : (ℝ≥0 → ℝ) × ℕ => q.1 (Real.toNNReal ((q.2 : ℝ) / ((n : ℝ) + 1))) :=
    measurable_from_prod_countable_left fun j =>
      measurable_pi_apply (Real.toNNReal ((j : ℝ) / ((n : ℝ) + 1)))
  exact hG.comp (measurable_fst.prodMk (hk.comp measurable_snd))

/-- The grid regularization is jointly measurable in the path (product σ-algebra) and the time. -/
theorem measurable_gridRegularization :
    Measurable fun p : (ℝ≥0 → ℝ) × ℝ≥0 => gridRegularization p.1 p.2 :=
  Measurable.limsup fun n => measurable_eval_gridTime n

/-- Circle averages of a jointly measurable family of functions are jointly measurable in the parameter, the
radius and the center. -/
theorem measurable_circleAverage_param {α : Type*} [MeasurableSpace α] {f : α → ℂ → ℝ}
    (hf : Measurable fun q : α × ℂ => f q.1 q.2) :
    Measurable fun p : α × ℝ × ℂ => Real.circleAverage (f p.1) p.2.2 p.2.1 := by
  have hm : Measurable fun q : (α × ℝ × ℂ) × ℝ => f q.1.1 (circleMap q.1.2.2 q.1.2.1 q.2) := by
    refine hf.comp ((measurable_fst.comp measurable_fst).prodMk ?_)
    fun_prop
  have hI := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
  have hS : StronglyMeasurable fun p : α × ℝ × ℂ => Real.circleAverage (f p.1) p.2.2 p.2.1 := by
    convert hI using 1
    funext p
    simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rfl
  exact hS.measurable

/-- The radial part `w ↦ X_{|w|}(0)` of a field is jointly measurable in the field and the point. -/
theorem measurable_radialFun :
    Measurable fun q : LQGMetric.DistC × ℂ => MatedCRTHarmonic.MoTPort.radialFun q.1 q.2 :=
  LQGMetric.measurable_circleAvg.comp
    (f := fun q : LQGMetric.DistC × ℂ => (q.1, ‖q.2‖, (0 : ℂ)))
    (measurable_fst.prodMk ((measurable_norm.comp measurable_snd).prodMk measurable_const))

end TildeField

open TildeField

/-! ## The field `h̃` through the later radial increments -/

/-- The radial function of the quantum cone above the split time, read through the increments
`v_u = b_{t₀ + u} - b_{t₀}` after `t₀`: `w ↦ v̄_{u - t₀} + γ u` at `u = log(1/|w|)`, where `v̄` is the grid
regularization of `v`. -/
noncomputable def incrementRadialProfile (γ : ℝ) (v : ℝ≥0 → ℝ) (w : ℂ) : ℝ :=
  gridRegularization v (Real.toNNReal (-Real.log ‖w‖ - (splitTime : ℝ))) + γ * -Real.log ‖w‖

/-- The field `h̃` of the split of the quantum cone on `B_{1/2}`, as a function of the lateral field `X` and of the
increments `v_u = b_{t₀ + u} - b_{t₀}` of the radial process after the split time: the circle average at `(z, ε)` of
the lateral part of `X` plus the circle average of `incrementRadialProfile γ v`. -/
noncomputable def incrTilde (γ : ℝ) (X : LQGMetric.DistC) (v : ℝ≥0 → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  lateralCircleAverage X ε z + Real.circleAverage (incrementRadialProfile γ v) z ε

/-- **(T1)** On `B_{1/2}`, at the scales `ε < 1/10`, the field `h̃` depends on a continuous radial path `b` only through
its increments after the split time `t₀`. -/
theorem hTilde_eq_incrTilde (γ : ℝ) (X : LQGMetric.DistC) {b : ℝ≥0 → ℝ} (hb : Continuous b) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) (1 / 10)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) :
    hTilde γ X b ε z = incrTilde γ X (fun u => b (splitTime + u) - b splitTime) ε z := by
  have hv : Continuous fun u : ℝ≥0 => b (splitTime + u) - b splitTime :=
    (hb.comp (continuous_const.add continuous_id)).sub continuous_const
  have hz' : ‖z‖ < 1 / 2 := mem_ball_zero_iff.1 hz
  unfold hTilde incrTilde
  congr 1
  refine FieldSplit.circleAverage_congr_of_ne hε.1.ne' 0 fun w hw hw0 => ?_
  have hlt : ‖w‖ < 3 / 5 :=
    FieldSplit.norm_lt_of_mem_sphere hw (by rw [abs_of_pos hε.1]; linarith [hε.2])
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hlog : (splitTime : ℝ) ≤ -Real.log ‖w‖ := by
    have h1 : Real.log ‖w‖ < Real.log (3 / 5) := Real.log_lt_log hpos hlt
    have h2 : Real.log (3 / 5 : ℝ) = -Real.log (5 / 3) := by
      rw [show (3 / 5 : ℝ) = (5 / 3)⁻¹ by norm_num, Real.log_inv]
    show Real.log (5 / 3) ≤ -Real.log ‖w‖
    linarith
  have hsplit : splitTime + Real.toNNReal (-Real.log ‖w‖ - (splitTime : ℝ)) =
      Real.toNNReal (-Real.log ‖w‖) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.2 hlog),
      Real.coe_toNNReal _ ((NNReal.coe_nonneg splitTime).trans hlog)]
    ring
  simp only [splitRadialProfile, incrementRadialProfile, gridRegularization_of_continuous hv, hsplit]

/-- Joint measurability of the radial function read through the increments, in the increments (product σ-algebra)
and the point. -/
theorem measurable_incrementRadialProfile (γ : ℝ) :
    Measurable fun q : (ℝ≥0 → ℝ) × ℂ => incrementRadialProfile γ q.1 q.2 := by
  have hlog : Measurable fun w : ℂ => -Real.log ‖w‖ := (Real.measurable_log.comp measurable_norm).neg
  have hu : Measurable fun w : ℂ => Real.toNNReal (-Real.log ‖w‖ - (splitTime : ℝ)) :=
    measurable_real_toNNReal.comp (hlog.sub_const _)
  show Measurable fun q : (ℝ≥0 → ℝ) × ℂ =>
    gridRegularization q.1 (Real.toNNReal (-Real.log ‖q.2‖ - (splitTime : ℝ))) + γ * -Real.log ‖q.2‖
  exact (measurable_gridRegularization.comp (measurable_fst.prodMk (hu.comp measurable_snd))).add
    ((hlog.comp measurable_snd).const_mul γ)

/-- **(T2)** `(X, v, ε, z) ↦ incrTilde γ X v ε z` is jointly measurable (product σ-algebra on the increments). -/
theorem measurable_incrTilde (γ : ℝ) :
    Measurable fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ =>
      incrTilde γ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have h1 : Measurable fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ =>
      LQGMetric.circleAvg p.1 p.2.2.1 p.2.2.2 :=
    LQGMetric.measurable_circleAvg.comp
      (f := fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ => (p.1, p.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ =>
      Real.circleAverage (MatedCRTHarmonic.MoTPort.radialFun p.1) p.2.2.2 p.2.2.1 :=
    (measurable_circleAverage_param measurable_radialFun).comp
      (f := fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ => (p.1, p.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h3 : Measurable fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ =>
      Real.circleAverage (incrementRadialProfile γ p.2.1) p.2.2.2 p.2.2.1 :=
    (measurable_circleAverage_param (measurable_incrementRadialProfile γ)).comp
      (f := fun p : LQGMetric.DistC × (ℝ≥0 → ℝ) × ℝ × ℂ => (p.2.1, p.2.2))
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  unfold incrTilde lateralCircleAverage
  exact (h1.sub h2).add h3

/-- **(T2) at a fixed scale.** For every `ε`, `((X, v), z) ↦ incrTilde γ X v ε z` is jointly measurable: the
field `φ (X, v) := incrTilde γ X v` on the space of pairs (lateral field, increments) has jointly measurable circle
averages at the scale `ε`. -/
theorem measurable_incrTilde_scale (γ ε : ℝ) :
    Measurable fun p : (LQGMetric.DistC × (ℝ≥0 → ℝ)) × ℂ => incrTilde γ p.1.1 p.1.2 ε p.2 :=
  (measurable_incrTilde γ).comp
    (f := fun p : (LQGMetric.DistC × (ℝ≥0 → ℝ)) × ℂ => (p.1.1, p.1.2, ε, p.2))
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (measurable_const.prodMk measurable_snd)))

/-- **(T2) for a random pair.** If `G : Ω → (lateral field, increments)` is measurable, then for every `ε` the
circle averages `(ω, z) ↦ incrTilde γ (G ω).1 (G ω).2 ε z` are jointly measurable. -/
theorem measurable_incrTilde_comp {Ω : Type*} [MeasurableSpace Ω] {G : Ω → LQGMetric.DistC × (ℝ≥0 → ℝ)}
    (hG : Measurable G) (γ ε : ℝ) :
    Measurable fun p : Ω × ℂ => incrTilde γ (G p.1).1 (G p.1).2 ε p.2 :=
  (measurable_incrTilde_scale γ ε).comp (f := fun p : Ω × ℂ => (G p.1, p.2))
    ((hG.comp measurable_fst).prodMk measurable_snd)

/-! ## Independence of `B_{t₀}` -/

/-- **(T3)** In the mating-of-trees coupling, under `P ⊗ Q`, the value `B_{t₀}` of the radial Brownian motion at the
split time is independent of every measurable function `Ψ` of the whole-plane GFF `X`, the increments
`u ↦ B_{t₀ + u} - B_{t₀}` and the second coordinate. -/
theorem isMatingOfTreesCoupling_indepFun_splitTime_comp {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {Ψ : MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ) × Ω' → α} (hΨ : Measurable Ψ) :
    IndepFun (fun p : Ω × Ω' => B splitTime p.1)
      (fun p => Ψ (X p.1, (fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)) (P.prod Q) := by
  have := h.isProbabilityMeasure
  have hB := h.bm_B.toIsPreBrownianReal
  obtain ⟨Z', hZ'm, hZZ⟩ :=
    exists_measurable_preimage_ae_eq_prodMk_increments h.gff.measurable hB.aemeasurable splitTime
  have hY := hB.aemeasurable splitTime
  have hind := (isMatingOfTreesCoupling_indepFun_eval_prodMk_increments h splitTime).1
  have hYY : ∀ s, MeasurableSet s →
      (fun ω => B splitTime ω) ⁻¹' s =ᵐ[P] hY.mk (B splitTime) ⁻¹' s := by
    intro s _
    filter_upwards [hY.ae_eq_mk] with ω hω
    exact congrArg (· ∈ s) hω
  have h2 := indepFun_comp_fst_prodMk_snd_of_preimage_ae_eq (Q := Q) hY.measurable_mk hZ'm hYY hZZ hind
  exact h2.comp measurable_id
    (hΨ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))

/-- **(T3) for valid environments.** The mating-of-trees coupling of a valid environment can be chosen so that,
besides the link of `matingOfTrees` with the field and the curve, under `S.P ⊗ Q` the value `B_{t₀}` is independent
of every measurable function of the lateral field `X`, the increments `u ↦ B_{t₀ + u} - B_{t₀}` and the second
coordinate. -/
theorem MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_splitTime_comp {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      ∀ (Ω' α : Type) [MeasurableSpace Ω'] [MeasurableSpace α] (Q : Measure Ω') [IsProbabilityMeasure Q]
        (Ψ : MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ) × Ω' → α), Measurable Ψ →
        IndepFun (fun p : Ω × Ω' => B splitTime p.1)
          (fun p => Ψ (X p.1, (fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2))
          (S.P.prod Q) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hS.matingOfTrees
  exact ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae,
    fun _ _ _ _ _ _ _ hΨ => isMatingOfTreesCoupling_indepFun_splitTime_comp hC hΨ⟩

end MatedCRT
