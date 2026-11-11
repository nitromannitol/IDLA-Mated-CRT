import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalConeIdentification

/-!
# Finite-dimensional entrance kernels of the conditioned drifted Brownian motion

Component of env-steps.tex:217-242 (audited, sha256 26dfc02c…aa03ae4): the killed
drifted kernel `p_t^d`, the survival function `h_d(x) = 1 - e^{-2dx}`, the
conditioned kernel `p_t^d(x,y) h_d(y)/h_d(x)`, the entrance density, and the
finite-dimensional chain of conditioned kernels.

The entrance-density analytic limit and its Gaussian specialisation are
results in `CanonicalConeIdentification` (`tendsto_conditioned_entrance_density`,
`tendsto_gaussian_conditioned_entrance_density`); they are reused, not reproved.

The Markov/disintegration premise and the domination premise are explicit
hypotheses (`ConditionedDriftFDDPremise`, `ConditionedDriftChainDomination`),
not theorems. This file does not use DMS Remark 4.4 (Duplantier-Miller-Sheffield
2014, Remark 4.4, pp. 74-75): no weak-limit identity is claimed to be that remark.

Terminology: Doob h-transform (conditioning on survival), reflection principle,
entrance law (Armitage-Gardiner potential theory; Duplantier-Sheffield LQG).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MatedCRT.Sec1

/-- Killed transition density of Brownian motion with drift `d` at time `t`, from
the reflection principle: `p_t^d(x,y) = e^{d(y-x) - d²t/2} (g_t(y-x) - g_t(y+x))`,
with `g_t` the centred normal density of variance `t` (env-steps.tex:220-223). -/
def killedDriftDensity (d t x y : ℝ) : ℝ :=
  Real.exp (d * (y - x) - d ^ 2 * t / 2) *
    (gaussianPDFReal 0 t.toNNReal (y - x) - gaussianPDFReal 0 t.toNNReal (y + x))

/-- Survival function of drift-`d` Brownian motion killed at `0`:
`h_d(x) = 1 - e^{-2dx}` (env-steps.tex:223). -/
def driftSurvival (d x : ℝ) : ℝ :=
  1 - Real.exp (-2 * d * x)

/-- Conditioned (Doob h-transform, conditioning on survival) transition density
`p_t^d(x,y) h_d(y) / h_d(x)` (env-steps.tex:229). -/
def conditionedDriftDensity (d t x y : ℝ) : ℝ :=
  killedDriftDensity d t x y * driftSurvival d y / driftSurvival d x

/-- Entrance density of the conditioned kernel as `x ↓ 0`:
`(y/(dt)) g_t(y) e^{dy - d²t/2} (1 - e^{-2dy})` (env-steps.tex:231-232). -/
def entranceDriftDensity (d t y : ℝ) : ℝ :=
  y / (d * t) * gaussianPDFReal 0 t.toNNReal y * Real.exp (d * y - d ^ 2 * t / 2) *
    (1 - Real.exp (-2 * d * y))

theorem driftSurvival_zero (d : ℝ) : driftSurvival d 0 = 0 := by
  simp [driftSurvival]

theorem driftSurvival_pos {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    0 < driftSurvival d x := by
  unfold driftSurvival
  have h1 : Real.exp (-2 * d * x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  linarith

theorem tendsto_driftSurvival_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (driftSurvival d) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (-2 * d * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have h2 : Tendsto (fun x : ℝ => 1 - Real.exp (-2 * d * x)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h1
  rw [sub_zero] at h2
  exact h2

theorem hasDerivAt_driftSurvival (d x : ℝ) :
    HasDerivAt (driftSurvival d) (2 * d * Real.exp (-2 * d * x)) x := by
  have h : HasDerivAt (fun y : ℝ => 1 - Real.exp (-2 * d * y))
      (-(Real.exp (-2 * d * x) * (-2 * d * 1))) x :=
    (((hasDerivAt_id x).const_mul (-2 * d)).exp).const_sub 1
  have he : -(Real.exp (-2 * d * x) * (-2 * d * 1)) = 2 * d * Real.exp (-2 * d * x) := by
    ring
  rw [he] at h
  exact h

/-- Generator identity `½ h'' + d h' = 0` for the survival function. -/
theorem driftSurvival_generator (d x : ℝ) :
    (1 / 2 : ℝ) * (-(4 * d ^ 2) * Real.exp (-2 * d * x)) +
      d * (2 * d * Real.exp (-2 * d * x)) = 0 := by
  ring

/-- Survival identification (env-steps.tex:227-228, "solve ½u'' + du' = 0, u(0) = 0,
u(∞) = 1"): a function that is differentiable on `(0,∞)` with derivative `v` and `v'=w`
there, satisfies `½ w + d v = 0` on `(0,∞)`, tends to `0` as `x ↓ 0` and to `1` as
`x → ∞`, is the survival function `h_d`. -/
theorem driftSurvival_eq_of_generator {d : ℝ} (hd : 0 < d) {u v w : ℝ → ℝ}
    (hu : ∀ x, 0 < x → HasDerivAt u (v x) x)
    (hv : ∀ x, 0 < x → HasDerivAt v (w x) x)
    (hode : ∀ x, 0 < x → (1 / 2 : ℝ) * w x + d * v x = 0)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0))
    (h1 : Tendsto u atTop (𝓝 1)) :
    ∀ x, 0 < x → u x = driftSurvival d x := by
  have hd0 : d ≠ 0 := hd.ne'
  have hexp : ∀ c x : ℝ, HasDerivAt (fun y => Real.exp (c * y)) (Real.exp (c * x) * c) x := by
    intro c x
    simpa using ((hasDerivAt_id x).const_mul c).exp
  -- v(x) e^{2dx} is constant on (0,∞)
  have hF1 : ∀ x, 0 < x → HasDerivAt (fun y => v y * Real.exp (2 * d * y)) 0 x := by
    intro x hx
    have hz : w x * Real.exp (2 * d * x) + v x * (Real.exp (2 * d * x) * (2 * d)) = 0 := by
      linear_combination (2 * Real.exp (2 * d * x)) * hode x hx
    have h := (hv x hx).mul (hexp (2 * d) x)
    rw [hz] at h
    exact h
  have hF1c : ∀ x, 0 < x → v x * Real.exp (2 * d * x) = v 1 * Real.exp (2 * d) := by
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun y => v y * Real.exp (2 * d * y)) (Set.Ioi 0) :=
      fun y hy => (hF1 y hy).differentiableAt.differentiableWithinAt
    have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi hdiff
      (fun y hy => (hF1 y hy).deriv) hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    simpa using hconst
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = v 1 * Real.exp (2 * d) := ⟨_, rfl⟩
  have hvexp : ∀ x, 0 < x → v x = c * Real.exp (-2 * d * x) := by
    intro x hx
    have h := hF1c x hx
    rw [← hc] at h
    have hprod : Real.exp (-2 * d * x) * Real.exp (2 * d * x) = 1 := by
      rw [← Real.exp_add]
      have h0' : -2 * d * x + 2 * d * x = 0 := by ring
      rw [h0', Real.exp_zero]
    calc v x = v x * Real.exp (2 * d * x) * Real.exp (-2 * d * x) := by
          rw [mul_assoc, mul_comm (Real.exp (2 * d * x)), hprod, mul_one]
      _ = c * Real.exp (-2 * d * x) := by rw [h]
  -- u - (c/2d) h_d has zero derivative on (0,∞)
  have hF2 : ∀ x, 0 < x →
      HasDerivAt (fun y => u y - c / (2 * d) * driftSurvival d y) 0 x := by
    intro x hx
    have h := (hu x hx).sub ((hasDerivAt_driftSurvival d x).const_mul (c / (2 * d)))
    have hk : c / (2 * d) * (2 * d * Real.exp (-2 * d * x)) = c * Real.exp (-2 * d * x) := by
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero two_ne_zero hd0)]
      ring
    have hz : v x - c / (2 * d) * (2 * d * Real.exp (-2 * d * x)) = 0 := by
      rw [hk, hvexp x hx, sub_self]
    rw [hz] at h
    exact h
  have hdiff2 : DifferentiableOn ℝ (fun y => u y - c / (2 * d) * driftSurvival d y)
      (Set.Ioi 0) :=
    fun y hy => (hF2 y hy).differentiableAt.differentiableWithinAt
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = u 1 - c / (2 * d) * driftSurvival d 1 := ⟨_, rfl⟩
  have hF2c : ∀ x, 0 < x → u x = K + c / (2 * d) * driftSurvival d x := by
    intro x hx
    have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi hdiff2
      (fun y hy => (hF2 y hy).deriv) hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    have hconst' : u x - c / (2 * d) * driftSurvival d x = K := by
      rw [hK]
      exact hconst
    linarith
  -- at 0+: K = 0
  have hK0 : K = 0 := by
    have hcts : Tendsto (driftSurvival d) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (driftSurvival d) := by
        unfold driftSurvival
        fun_prop
      have h := hcont.tendsto 0
      rw [driftSurvival_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hcont0 : Tendsto (fun x => K + c / (2 * d) * driftSurvival d x) (𝓝[>] 0) (𝓝 K) := by
      have := (tendsto_const_nhds (x := K)).add (hcts.const_mul (c / (2 * d)))
      simpa using this
    have hu0 : Tendsto (fun x => K + c / (2 * d) * driftSurvival d x) (𝓝[>] 0) (𝓝 0) := by
      refine h0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hF2c x hx
    exact tendsto_nhds_unique hcont0 hu0
  -- at ∞: c/(2d) = 1
  have hc1 : c / (2 * d) = 1 := by
    have hlim : Tendsto (fun x => c / (2 * d) * driftSurvival d x) atTop
        (𝓝 (c / (2 * d) * 1)) :=
      (tendsto_driftSurvival_atTop hd).const_mul (c / (2 * d))
    have hu_inf : Tendsto (fun x => c / (2 * d) * driftSurvival d x) atTop (𝓝 1) := by
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [hF2c x hx, hK0, zero_add]
    have h := tendsto_nhds_unique hu_inf hlim
    rw [mul_one] at h
    exact h.symm
  intro x hx
  rw [hF2c x hx, hK0, zero_add, hc1, one_mul]

/-- Chain of conditioned kernels for the finite-dimensional laws. Started at
position `x` at time `s`, observed at times `τ 0, …, τ (n-1)` at positions
`y 0, …, y (n-1)`; each factor is a conditioned kernel over the gap to the
previous observation (the Markov product, env-steps.tex:234-237). -/
def conditionedChainDensity (d : ℝ) : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, _, _, _ => 1
  | n + 1, s, x, τ, y =>
      conditionedDriftDensity d (τ 0 - s) x (y 0) *
        conditionedChainDensity d n (τ 0) (y 0) (Fin.tail τ) (Fin.tail y)

/-- Entrance chain: the first conditioned kernel (from time `0`) replaced by the
entrance density; the remaining factors are the conditioned kernels. -/
def entranceChainDensity (d : ℝ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, _ => 1
  | n + 1, τ, y =>
      entranceDriftDensity d (τ 0) (y 0) *
        conditionedChainDensity d n (τ 0) (y 0) (Fin.tail τ) (Fin.tail y)

/-- The positive orthant `(0,∞)ⁿ` on which the conditioned process lives at
positive times. -/
def positiveOrthant (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioi 0

/-- The conditioned kernel converges to the entrance density as the starting
point decreases to `0` (env-steps.tex:230-232). The analytic limit is
`tendsto_gaussian_conditioned_entrance_density`. -/
theorem tendsto_conditionedDriftDensity_entrance {d τ y : ℝ} (hd : d ≠ 0) (hτ : 0 < τ) :
    Tendsto (fun x => conditionedDriftDensity d τ x y) (𝓝[>] 0)
      (𝓝 (entranceDriftDensity d τ y)) := by
  have h := tendsto_gaussian_conditioned_entrance_density d y τ.toNNReal hd
    (Real.toNNReal_pos.mpr hτ).ne'
  rw [Real.coe_toNNReal τ hτ.le] at h
  exact h

/-- First-factor limit of the finite-dimensional chain: the only factor that depends
on the starting point `x` is the first conditioned kernel. -/
theorem tendsto_conditionedChainDensity_entrance {d : ℝ} (hd : d ≠ 0) (n : ℕ)
    {τ y : Fin n → ℝ} (hτ : ∀ i, 0 < τ i) :
    Tendsto (fun x => conditionedChainDensity d n 0 x τ y) (𝓝[>] 0)
      (𝓝 (entranceChainDensity d n τ y)) := by
  cases n with
  | zero => simp [conditionedChainDensity, entranceChainDensity]
  | succ n =>
    simp only [conditionedChainDensity, entranceChainDensity, sub_zero]
    exact (tendsto_conditionedDriftDensity_entrance hd (hτ 0)).mul_const _

/-- The killed kernel is nonnegative on `(0,∞)²`: the reflected Gaussian term is
dominated by the direct one, since `(y-x)² ≤ (y+x)²` for `x, y > 0`. -/
theorem killedDriftDensity_nonneg {d t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ killedDriftDensity d t x y := by
  unfold killedDriftDensity
  refine mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr ?_)
  unfold gaussianPDFReal
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  exact div_le_div_of_nonneg_right (by nlinarith [mul_pos hx hy]) (by positivity)

theorem conditionedDriftDensity_nonneg {d t x y : ℝ} (hd : 0 < d) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ conditionedDriftDensity d t x y :=
  div_nonneg (mul_nonneg (killedDriftDensity_nonneg hx hy) (driftSurvival_pos hd hy).le)
    (driftSurvival_pos hd hx).le

theorem conditionedChainDensity_nonneg {d : ℝ} (hd : 0 < d) :
    ∀ (n : ℕ) (s x : ℝ) (τ y : Fin n → ℝ), 0 < x → y ∈ positiveOrthant n →
      0 ≤ conditionedChainDensity d n s x τ y
  | 0, _, _, _, _, _, _ => by simp [conditionedChainDensity]
  | n + 1, s, x, τ, y, hx, hy => by
      have hy0 : 0 < y 0 := Set.mem_Ioi.mp (Set.mem_univ_pi.mp hy 0)
      have htail : Fin.tail y ∈ positiveOrthant n :=
        Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mp hy i.succ
      simp only [conditionedChainDensity]
      exact mul_nonneg (conditionedDriftDensity_nonneg hd hx hy0)
        (conditionedChainDensity_nonneg hd n _ _ _ _ hy0 htail)

/-- Joint measurability of the conditioned kernel in (starting point, endpoint). -/
theorem measurable_conditionedDriftDensity_pair (d a : ℝ) :
    Measurable (fun p : ℝ × ℝ => conditionedDriftDensity d a p.1 p.2) := by
  have hg : Measurable (gaussianPDFReal 0 a.toNNReal) := measurable_gaussianPDFReal _ _
  have he : Measurable Real.exp := Real.continuous_exp.measurable
  have hsub : Measurable (fun p : ℝ × ℝ => p.2 - p.1) := measurable_snd.sub measurable_fst
  have hadd : Measurable (fun p : ℝ × ℝ => p.2 + p.1) := measurable_snd.add measurable_fst
  have hx1 : Measurable (fun p : ℝ × ℝ => p.1) := measurable_fst
  have hy1 : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
  unfold conditionedDriftDensity killedDriftDensity driftSurvival
  exact ((((he.comp ((measurable_const.mul hsub).sub measurable_const)).mul
      ((hg.comp hsub).sub (hg.comp hadd))).mul
      (measurable_const.sub (he.comp (measurable_const.mul hy1)))).div
      (measurable_const.sub (he.comp (measurable_const.mul hx1))))

/-- Joint measurability of the chain density in (starting point, positions). -/
theorem measurable_conditionedChainDensity (d : ℝ) :
    ∀ (n : ℕ) (s : ℝ) (τ : Fin n → ℝ),
      Measurable (fun p : ℝ × (Fin n → ℝ) => conditionedChainDensity d n s p.1 τ p.2)
  | 0, _, _ => by simp [conditionedChainDensity]
  | n + 1, s, τ => by
      have hfst : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => p.1) := measurable_fst
      have hy0 : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htl : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => Fin.tail p.2) :=
        Measurable.of_eval fun (i : Fin n) => (measurable_pi_apply i.succ).comp measurable_snd
      have hA := (measurable_conditionedDriftDensity_pair d (τ 0 - s)).comp (hfst.prodMk hy0)
      have hB := (measurable_conditionedChainDensity d n (τ 0) (Fin.tail τ)).comp
        (hy0.prodMk htl)
      simp only [conditionedChainDensity]
      exact hA.mul hB

/-- Markov and disintegration premise (explicit hypothesis, not proved in this file).
For every starting point `x > 0` of the conditioned drifted process `X` (law `P x`)
and every strictly increasing family of positive observation times `τ`, the law of
`(X (τ i))_i` is the chain density restricted to the positive orthant. This encodes the
Markov property of the h-transform together with its disintegration
(env-steps.tex:229-237). It is not DMS Remark 4.4. -/
def ConditionedDriftFDDPremise {Ω : Type*} [MeasurableSpace Ω] (d : ℝ)
    (X : ℝ → Ω → ℝ) (P : ℝ → Measure Ω) : Prop :=
  ∀ x : ℝ, 0 < x → ∀ (n : ℕ) (τ : Fin n → ℝ), StrictMono τ → (∀ i, 0 < τ i) →
    ∀ A : Set (Fin n → ℝ), MeasurableSet A →
      P x {ω | (fun i => X (τ i) ω) ∈ A} =
        ∫⁻ y in A ∩ positiveOrthant n, ENNReal.ofReal (conditionedChainDensity d n 0 x τ y)

/-- Domination premise (explicit hypothesis, not proved in this file): an integrable
majorant on the positive orthant of the chain densities, uniform for starting points in
some interval `(0, ε)`. The source does not write this majorant. -/
def ConditionedDriftChainDomination (d : ℝ) (n : ℕ) (τ : Fin n → ℝ) : Prop :=
  ∃ bound : (Fin n → ℝ) → ℝ, Integrable bound (volume.restrict (positiveOrthant n)) ∧
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ y ∈ positiveOrthant n,
      |conditionedChainDensity d n 0 x τ y| ≤ bound y

theorem measurableSet_positiveOrthant (n : ℕ) : MeasurableSet (positiveOrthant n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

/-- Finite-dimensional entrance-kernel limit, setwise form. Under the explicit
Markov premise `hM` and the explicit domination premise `hD`, the probabilities that the
conditioned process started at `x` lies in `A` at the observation times converge, as
`x ↓ 0`, to the integral of the entrance chain over `A` on the positive orthant. -/
theorem tendsto_fdd_setwise_entrance {Ω : Type*} [MeasurableSpace Ω]
    {d : ℝ} (hd : 0 < d) {X : ℝ → Ω → ℝ} {P : ℝ → Measure Ω}
    (hM : ConditionedDriftFDDPremise d X P)
    {n : ℕ} {τ : Fin n → ℝ} (hτ : StrictMono τ) (hτ0 : ∀ i, 0 < τ i)
    (hD : ConditionedDriftChainDomination d n τ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Tendsto (fun x => (P x {ω | (fun i => X (τ i) ω) ∈ A}).toReal) (𝓝[>] 0)
      (𝓝 (∫ y in A ∩ positiveOrthant n, entranceChainDensity d n τ y)) := by
  obtain ⟨bound, hbound_int, hbound_ev⟩ := hD
  have hAO : MeasurableSet (A ∩ positiveOrthant n) :=
    hA.inter (measurableSet_positiveOrthant n)
  have hlim : ∀ᵐ y ∂(volume.restrict (A ∩ positiveOrthant n)),
      Tendsto (fun x => conditionedChainDensity d n 0 x τ y) (𝓝[>] 0)
        (𝓝 (entranceChainDensity d n τ y)) :=
    ae_of_all _ fun y => tendsto_conditionedChainDensity_entrance hd.ne' n hτ0
  have hmx : ∀ x : ℝ, AEStronglyMeasurable (fun y => conditionedChainDensity d n 0 x τ y)
      (volume.restrict (A ∩ positiveOrthant n)) := by
    intro x
    have hpair : Measurable (fun y : Fin n → ℝ => (x, y)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_conditionedChainDensity d n 0 τ).comp hpair).aestronglyMeasurable
  have hmeas : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun y => conditionedChainDensity d n 0 x τ y)
        (volume.restrict (A ∩ positiveOrthant n)) :=
    Eventually.of_forall hmx
  have hbd : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂(volume.restrict (A ∩ positiveOrthant n)),
      ‖conditionedChainDensity d n 0 x τ y‖ ≤ bound y :=
    hbound_ev.mono fun x hx =>
      ae_restrict_of_forall_mem hAO fun y hy => by
        rw [Real.norm_eq_abs]
        exact hx y hy.2
  have hbound_restr : Integrable bound (volume.restrict (A ∩ positiveOrthant n)) :=
    hbound_int.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have hDCT := tendsto_integral_filter_of_dominated_convergence bound hmeas hbd
    hbound_restr hlim
  have hident : ∀ x : ℝ, 0 < x →
      (P x {ω | (fun i => X (τ i) ω) ∈ A}).toReal =
        ∫ y in A ∩ positiveOrthant n, conditionedChainDensity d n 0 x τ y := by
    intro x hx
    have h0 : ∀ᵐ y ∂(volume.restrict (A ∩ positiveOrthant n)),
        (0 : ℝ) ≤ conditionedChainDensity d n 0 x τ y :=
      ae_restrict_of_forall_mem hAO fun y hy =>
        conditionedChainDensity_nonneg hd n 0 x τ y hx hy.2
    rw [hM x hx n τ hτ hτ0 A hA, integral_eq_lintegral_of_nonneg_ae h0 (hmx x)]
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := eventually_mem_nhdsWithin
  exact Tendsto.congr' (hev.mono fun x hx => (hident x hx).symm) hDCT

end MatedCRT.Sec1
