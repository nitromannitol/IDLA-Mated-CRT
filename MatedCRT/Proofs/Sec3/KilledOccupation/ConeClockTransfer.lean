import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockClosure
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationAssembly

/-!
# Identification of a clock from convergence of its approximants (fibre argument)

Abstract form of the identification `φ = Φ` of the killed-occupation chain (tex:370-425, appendix-occupation-C16.tex):
the approximants `ψ k` (dyadic scales `k`) converge in probability over the product of the environment and the planar
Brownian path to `Φ`, and for each environment the approximants converge in probability over the Brownian path to the
clock `clock ω`. Then the clock equals `Φ` almost surely, on `[0, σ]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open Metric MarkovProcess

namespace MatedCRT.KilledOccupation

/-- **Fibre identification of a clock** (Duplantier-Sheffield, Berestycki-Powell convergence in probability, applied
to the product space `Ω × β` of environments and Brownian paths). A subsequence of approximants converges almost
surely on the product (Borel-Cantelli), Fubini gives fibrewise convergence, and uniqueness of the limit in
probability along each fibre identifies the clock with `Φ` on `[0, σ]`. -/
theorem clock_eq_of_approx_convergence {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure β) [IsProbabilityMeasure Q]
    (σ : β → ℝ≥0) (ψ : ℕ → Ω → β → ℝ≥0 → ℝ) (Φ clock : Ω → β → ℝ≥0 → ℝ)
    (hconv : ∀ η : ℝ, 0 < η → Tendsto (fun k : ℕ => (P.prod Q)
      {p : Ω × β | ∃ s ≤ σ p.2, η ≤ |ψ k p.1 p.2 s - Φ p.1 p.2 s|}) atTop (𝓝 0))
    (hlq : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Tendsto (fun k : ℕ => Q
      {b | ∃ t ≤ T, η ≤ |ψ k ω b t - clock ω b t|}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ s ≤ σ b, clock ω b s = Φ ω b s := by
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ, ∀ m, η m = 1 / ((m : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hηpos : ∀ m, 0 < η m := fun m => by rw [hη]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℕ → Set (Ω × β), ∀ m k,
      A m k = {p : Ω × β | ∃ s ≤ σ p.2, η m ≤ |ψ k p.1 p.2 s - Φ p.1 p.2 s|} := ⟨_, fun _ _ => rfl⟩
  -- Step 1: along a subsequence the bad sets are summable (Borel-Cantelli)
  have hsub : ∀ m, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∑' j, (P.prod Q) (A m (φ j)) ≠ ⊤ := by
    intro m
    have h0 : Tendsto (fun k => (P.prod Q) (A m k)) atTop (𝓝 0) := by
      simp only [hA]
      exact hconv (η m) (hηpos m)
    have hev : ∀ j : ℕ, ∀ᶠ k in atTop, (P.prod Q) (A m k) ≤ ((2 : ℝ≥0∞)⁻¹) ^ j := by
      intro j
      have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ j :=
        ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) j
      filter_upwards [(tendsto_order.1 h0).2 _ hpos] with k hk
      exact hk.le
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_forall_of_eventually hev
    refine ⟨φ, hφ, ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => hφb j)⟩
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_ne_top.2 (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  choose φ hφ hsum using hsub
  -- Step 2: almost surely on the product, the approximants eventually avoid the bad sets
  have hBC : ∀ᵐ p ∂(P.prod Q), ∀ m, ∀ᶠ j in atTop, p ∉ A m (φ m j) := by
    rw [ae_all_iff]
    intro m
    exact ae_eventually_notMem (hsum m)
  have hBC2 : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ m, ∀ᶠ j in atTop, (ω, b) ∉ A m (φ m j) :=
    Measure.ae_ae_of_ae_prod hBC
  filter_upwards [hBC2, hlq] with ω hω1 hω2
  -- Step 3: fibrewise, the clock and `Φ` agree on `[0, σ]`
  have hnull : ∀ T m : ℕ, ∀ᵐ b ∂Q, ¬ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧
      η m ≤ |clock ω b s - Φ ω b s| := by
    intro T m
    obtain ⟨m', hm'⟩ := exists_nat_one_div_lt (half_pos (hηpos m))
    have hm'' : η m' < η m / 2 := by rw [hη]; exact hm'
    -- the event that the approximant is far from the clock at a time `≤ T`
    obtain ⟨E, hE⟩ : ∃ E : ℕ → Set β, ∀ j, E j =
        {b | ∃ t ≤ (T : ℝ≥0), η m / 2 ≤ |ψ (φ m' j) ω b t - clock ω b t|} := ⟨_, fun _ => rfl⟩
    have hEt : Tendsto (fun j => Q (E j)) atTop (𝓝 0) := by
      have h := (hω2 (T : ℝ≥0) (η m / 2) (half_pos (hηpos m))).comp (hφ m').tendsto_atTop
      simp only [hE]
      exact h
    -- almost surely in `b`, the approximants are eventually `η m'`-close to `Φ` on `[0, σ b]`
    have hclose : ∀ᵐ b ∂Q, ∀ᶠ j in atTop, ∀ s ≤ σ b, |ψ (φ m' j) ω b s - Φ ω b s| < η m' := by
      filter_upwards [hω1] with b hb
      filter_upwards [hb m'] with j hj
      intro s hs
      by_contra h
      rw [hA] at hj
      exact hj (show ∃ s' ≤ σ b, η m' ≤ |ψ (φ m' j) ω b s' - Φ ω b s'| from
        ⟨s, hs, not_lt.1 h⟩)
    -- the exceptional sets `F N` are null
    obtain ⟨F, hF⟩ : ∃ F : ℕ → Set β, ∀ N, F N = {b | ∀ j, N ≤ j → b ∈ E j} := ⟨_, fun _ => rfl⟩
    have hFnull : ∀ N, Q (F N) = 0 := by
      intro N
      refine le_antisymm (ge_of_tendsto hEt ?_) zero_le
      refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
      exact measure_mono (fun b (hb : b ∈ F N) => by rw [hF] at hb; exact hb j hj)
    have hFae : ∀ᵐ b ∂Q, b ∉ ⋃ N, F N := by
      rw [ae_iff]
      simp only [not_not, Set.ofPred_mem_eq]
      exact measure_iUnion_null hFnull
    have h1 : ∀ᵐ b ∂Q, (∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧ η m ≤ |clock ω b s - Φ ω b s|) →
        ∃ N, ∀ j, N ≤ j → b ∈ E j := by
      filter_upwards [hclose] with b hb hBb
      obtain ⟨s, hsT, hsσ, hs⟩ := hBb
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.mono fun j hj => hj s hsσ)
      refine ⟨N, fun j hj => ?_⟩
      have hcl := hN j hj
      rw [hE]
      refine ⟨s, hsT, ?_⟩
      have htri : |clock ω b s - Φ ω b s| ≤ |ψ (φ m' j) ω b s - clock ω b s| +
          |ψ (φ m' j) ω b s - Φ ω b s| := by
        have := abs_sub_le (clock ω b s) (ψ (φ m' j) ω b s) (Φ ω b s)
        rw [abs_sub_comm (clock ω b s) (ψ (φ m' j) ω b s)] at this
        linarith
      linarith
    filter_upwards [h1, hFae] with b hb1 hb2 hBb
    obtain ⟨N, hN⟩ := hb1 hBb
    refine hb2 (mem_iUnion.2 ⟨N, ?_⟩)
    rw [hF]
    exact fun j hj => hN j hj
  have hall : ∀ᵐ b ∂Q, ∀ T m : ℕ, ¬ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧
      η m ≤ |clock ω b s - Φ ω b s| :=
    ae_all_iff.2 fun T => ae_all_iff.2 fun m => hnull T m
  filter_upwards [hall] with b hb s hs
  by_contra hne
  have hpos : 0 < |clock ω b s - Φ ω b s| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  have hm' : η m ≤ |clock ω b s - Φ ω b s| := by rw [hη]; exact hm.le
  exact hb (⌈s⌉₊) m ⟨s, Nat.le_ceil s, hs, hm'⟩

/-! ### The cone field in the GFF interface of the clock identification -/

/-- The cone circle averages with the logarithmic part added back: `coneShift γ hcirc r z = hcirc r z +
γ · (average of log‖·‖ over ∂B_r(z))`, the inverse of `HarmonicBalls.fieldCircleAverage`. With `hcirc` the circle
averages `h_r(z)` of the γ-quantum cone `h = h^ℂ - γ log|·|` (eq:gff, tex:427-445), `coneShift γ hcirc` is the
whole-plane circle average field `h^ℂ_r(z)` of that identity. -/
noncomputable def coneShift (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hcirc r z + γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r

/-- The circle averages of the cone are recovered from `coneShift`:
`fieldCircleAverage γ (coneShift γ hcirc) = hcirc`. -/
lemma fieldCircleAverage_coneShift (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) :
    HarmonicBalls.fieldCircleAverage γ (coneShift γ hcirc) r z = hcirc r z := by
  unfold HarmonicBalls.fieldCircleAverage coneShift
  ring

/-- For `ε > 0` the logarithmic part of `coneShift` is `γ log (max |x| ε)` (Jensen's formula,
`circleAverage_log_norm_eq`), so `coneShift γ hcirc ε` is continuous wherever `hcirc ε` is. -/
lemma continuous_coneShift {γ : ℝ} {hcirc : ℝ → ℂ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hcont : Continuous fun x : ℂ => hcirc ε x) : Continuous fun x : ℂ => coneShift γ hcirc ε x := by
  have h : (fun x : ℂ => coneShift γ hcirc ε x) =
      fun x : ℂ => hcirc ε x + γ * Real.log (max ‖x‖ ε) := by
    funext x
    unfold coneShift
    rw [circleAverage_log_norm_eq hε x]
  rw [h]
  exact hcont.add (continuous_const.mul
    ((continuous_norm.max continuous_const).log fun x => (lt_max_of_lt_right hε).ne'))

/-- **Cone version of `exists_null_continuous`.** Off a measurable null set of environments the circle averages of
the quantum cone are continuous in the centre for every positive radius (`IsQuantumCone.ae_continuousOn_circle`),
hence so are those of `coneShift`. -/
lemma exists_null_continuous_cone {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => coneShift γ (hcirc ω) ε x := by
  have h := hcone.ae_continuousOn_circle
  rw [ae_iff] at h
  refine ⟨toMeasurable P {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)},
    measurableSet_toMeasurable _ _, by rw [measure_toMeasurable]; exact h, fun ω hω ε hε => ?_⟩
  have hgood : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    by_contra hbad
    exact hω (subset_toMeasurable _ _ hbad)
  have h1 : ContinuousOn (fun x : ℂ => ((ε, x) : ℝ × ℂ)) univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h2 : ContinuousOn (fun x : ℂ => hcirc ω ε x) univ :=
    hgood.comp h1 (fun x _ => ⟨mem_Ioi.2 hε, mem_univ x⟩)
  exact continuous_coneShift hε (continuousOn_univ.mp h2)

/-! ### The regularized cone clock is the approximating LQG clock -/

/-- Lower integral of `e^{g}` against the time measure: for continuous nonnegative `g`, the integral over `[0, t]` of
`ofReal (g u)` with respect to `timeLeb` is `ofReal` of the Lebesgue integral `∫_0^t g`. -/
lemma lintegral_Icc_timeLeb_ofReal {g : ℝ≥0 → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) (t : ℝ≥0) :
    ∫⁻ u in Icc 0 t, ENNReal.ofReal (g u) ∂timeLeb =
      ENNReal.ofReal (∫ x in (0 : ℝ)..(t : ℝ), g x.toNNReal) := by
  have hf : Continuous fun x : ℝ => g x.toNNReal := hg.comp continuous_real_toNNReal
  have hpre : MeasurableSet (Real.toNNReal ⁻¹' Icc 0 t) := measurable_real_toNNReal measurableSet_Icc
  have hset : Real.toNNReal ⁻¹' Icc 0 t ∩ Ici (0 : ℝ) = Icc (0 : ℝ) (t : ℝ) := by
    ext x
    simp [Real.toNNReal_le_iff_le_coe, and_comm]
  unfold timeLeb
  rw [Measure.restrict_map measurable_real_toNNReal measurableSet_Icc,
    lintegral_map hg.measurable.ennreal_ofReal measurable_real_toNNReal,
    Measure.restrict_restrict hpre, hset]
  have hint : IntegrableOn (fun x : ℝ => g x.toNNReal) (Icc 0 (t : ℝ)) := hf.integrableOn_Icc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => hg0 _),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t), integral_Icc_eq_integral_Ioc]

/-- The regularized clock of the cone is the approximating LQG clock: at a time `s ≤ σ`, `regClock` of the field
`coneShift γ hcirc` equals `ofReal` of `lqgClockApprox γ hcirc ε b s = ∫_0^s ε^{γ²/2} e^{γ h_ε(b_u)} du`, for a
continuous path `b` and a scale `ε > 0` with `hcirc ε` continuous. -/
lemma regClock_coneShift_eq_ofReal {γ ε : ℝ} (hε : 0 < ε) {hcirc : ℝ → ℂ → ℝ}
    (hcont : Continuous fun x : ℂ => coneShift γ hcirc ε x) (b : ContinuousPath ℂ) (σ s : ℝ≥0) (hs : s ≤ σ) :
    regClock γ ε (coneShift γ hcirc) σ ⇑b s = ENNReal.ofReal (HarmonicBalls.lqgClockApprox γ hcirc ε b s) := by
  -- the circle averages `hcirc ε` are the shifted field minus the logarithmic part
  have hcirc_cont : Continuous fun x : ℂ => hcirc ε x := by
    have h : (fun x : ℂ => hcirc ε x) =
        fun x : ℂ => coneShift γ hcirc ε x - γ * Real.log (max ‖x‖ ε) := by
      funext x
      unfold coneShift
      rw [circleAverage_log_norm_eq hε x]
      ring
    rw [h]
    exact hcont.sub (continuous_const.mul
      ((continuous_norm.max continuous_const).log fun x => (lt_max_of_lt_right hε).ne'))
  have hdens : ∀ x : ℂ, regDensity γ ε (coneShift γ hcirc) x =
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x)) := by
    intro x
    unfold regDensity
    rw [fieldCircleAverage_coneShift]
  have hg : Continuous fun u : ℝ≥0 => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε (b u)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcirc_cont.comp b.continuous)))
  have hg0 : ∀ u : ℝ≥0, 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε (b u)) :=
    fun u => (mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)).le
  unfold regClock
  rw [min_eq_left hs]
  simp only [hdens]
  rw [lintegral_Icc_timeLeb_ofReal hg hg0 s]
  rfl

/-- The approximating LQG clock is nonnegative (its integrand `ε^{γ²/2} e^{γ h_ε}` is positive). -/
lemma lqgClockApprox_nonneg {γ ε : ℝ} (hε : 0 < ε) (hcirc : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    0 ≤ HarmonicBalls.lqgClockApprox γ hcirc ε b t := by
  unfold HarmonicBalls.lqgClockApprox
  exact intervalIntegral.integral_nonneg (NNReal.coe_nonneg t)
    fun u _ => (mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)).le

/-- The `ennDist` of two `ofReal` values dominates `ofReal` of the distance of the reals, `ennDist x y = (x - y) +
(y - x)` in truncated subtraction. -/
lemma ofReal_le_ennDist_ofReal {a b η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : η ≤ |a - b|) :
    ENNReal.ofReal η ≤ ennDist (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  unfold ennDist
  rcases le_total a b with hab | hab
  · have h1 : η ≤ b - a := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at hη
      exact hη
    calc ENNReal.ofReal η ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal b - ENNReal.ofReal a := ENNReal.ofReal_sub b ha
      _ ≤ (ENNReal.ofReal a - ENNReal.ofReal b) + (ENNReal.ofReal b - ENNReal.ofReal a) := le_add_self
  · have h1 : η ≤ a - b := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)] at hη
      exact hη
    calc ENNReal.ofReal η ≤ ENNReal.ofReal (a - b) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal a - ENNReal.ofReal b := ENNReal.ofReal_sub a hb
      _ ≤ (ENNReal.ofReal a - ENNReal.ofReal b) + (ENNReal.ofReal b - ENNReal.ofReal a) := le_self_add

/-- **Convergence of the approximants of the cone clock** (abstract form of `regClock_identification_cone` with the
approximants `lqgClockApprox γ (hcirc ω) (dyadicScale k)` in place of the regularized clocks). The hypotheses are the
a.s. continuity off a null set `N` (`exists_null_continuous_cone`), the a.s. finiteness of the total clock mass, and
the conclusion of `regClock_identification_cone` for the sup-distance `clockDistD`; the sup-distance dominates the
approximation error at each time `s ≤ σ` (`regClock_coneShift_eq_ofReal`). -/
theorem tendsto_approx_cone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (ContinuousPath ℂ)) [IsProbabilityMeasure Q] {γ : ℝ}
    (hcirc : Ω → ℝ → ℂ → ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (hN : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => coneShift γ (hcirc ω) ε x)
    (hfin : ∀ᵐ x ∂(P.prod Q),
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)
    (hcv : ∀ η : ℝ, 0 < η → Tendsto (fun ε => (P.prod Q)
      {x | ENNReal.ofReal η < clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ ε x})
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun k : ℕ => (P.prod Q) {x : Ω × ContinuousPath ℂ | ∃ s ≤ σ x.2,
      η ≤ |HarmonicBalls.lqgClockApprox γ (hcirc x.1) (HarmonicBalls.dyadicScale k) x.2 s -
        (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s).toReal|}) atTop (𝓝 0) := by
  obtain ⟨N, hNm, hN0, hcont⟩ := hN
  have hΦ : Tendsto (fun k : ℕ => HarmonicBalls.dyadicScale k) atTop (𝓝[>] (0 : ℝ)) := by
    unfold HarmonicBalls.dyadicScale
    exact tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num),
      Filter.Eventually.of_forall fun k => Set.mem_Ioi.2 (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) k)⟩
  have hE := (hcv (η / 2) (half_pos hη)).comp hΦ
  have hNull : (P.prod Q) {x : Ω × ContinuousPath ℂ | x.1 ∈ N} = 0 := by
    have hset : {x : Ω × ContinuousPath ℂ | x.1 ∈ N} = N ×ˢ univ := by
      ext x
      simp
    rw [hset, Measure.prod_prod, hN0, zero_mul]
  have hF := ae_iff.1 hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun k => zero_le) (fun k => ?_)
  have hεpos : 0 < HarmonicBalls.dyadicScale k := by
    unfold HarmonicBalls.dyadicScale
    exact pow_pos (by norm_num) k
  have hsub : {x : Ω × ContinuousPath ℂ | ∃ s ≤ σ x.2,
      η ≤ |HarmonicBalls.lqgClockApprox γ (hcirc x.1) (HarmonicBalls.dyadicScale k) x.2 s -
        (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s).toReal|} ⊆
      ({x : Ω × ContinuousPath ℂ | ENNReal.ofReal (η / 2) <
          clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x} ∪
        {x : Ω × ContinuousPath ℂ | x.1 ∈ N}) ∪
      {x : Ω × ContinuousPath ℂ | ¬ (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)} := by
    intro x hx
    obtain ⟨s, hs, hsη⟩ := hx
    by_cases hxN : x.1 ∈ N
    · exact Or.inl (Or.inr hxN)
    by_cases hfx : weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) = ⊤
    · exact Or.inr (fun h => h hfx)
    refine Or.inl (Or.inl ?_)
    show ENNReal.ofReal (η / 2) < clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x
    have hw : weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s ≠ ⊤ :=
      ne_top_of_le_ne_top hfx (weightedClock_mono _ _ _ hs)
    have hreg := regClock_coneShift_eq_ofReal hεpos (hcont x.1 hxN _ hεpos) x.2 (σ x.2) s hs
    have hle : ENNReal.ofReal η ≤ ennDist
        (regClock γ (HarmonicBalls.dyadicScale k) (coneShift γ (hcirc x.1)) (σ x.2) ⇑x.2 s)
        (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s) := by
      rw [hreg, ← ENNReal.ofReal_toReal hw]
      exact ofReal_le_ennDist_ofReal (lqgClockApprox_nonneg hεpos _ _ _) ENNReal.toReal_nonneg hsη
    have hlt : ENNReal.ofReal (η / 2) < ENNReal.ofReal η :=
      (ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith)
    unfold clockDistD
    exact lt_of_lt_of_le hlt (hle.trans (le_iSup (fun s' : ℝ≥0 => ennDist
      (regClock γ (HarmonicBalls.dyadicScale k) (coneShift γ (hcirc x.1)) (σ x.2) ⇑x.2 s')
      (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s')) s))
  calc (P.prod Q) {x : Ω × ContinuousPath ℂ | ∃ s ≤ σ x.2,
        η ≤ |HarmonicBalls.lqgClockApprox γ (hcirc x.1) (HarmonicBalls.dyadicScale k) x.2 s -
          (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s).toReal|}
      ≤ (P.prod Q) (({x : Ω × ContinuousPath ℂ | ENNReal.ofReal (η / 2) <
          clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x} ∪
        {x : Ω × ContinuousPath ℂ | x.1 ∈ N}) ∪
      {x : Ω × ContinuousPath ℂ | ¬ (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)}) :=
        measure_mono hsub
    _ ≤ (P.prod Q) ({x : Ω × ContinuousPath ℂ | ENNReal.ofReal (η / 2) <
          clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x} ∪
        {x : Ω × ContinuousPath ℂ | x.1 ∈ N}) +
        (P.prod Q) {x : Ω × ContinuousPath ℂ | ¬ (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)} :=
        measure_union_le _ _
    _ ≤ ((P.prod Q) {x : Ω × ContinuousPath ℂ | ENNReal.ofReal (η / 2) <
          clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x} +
        (P.prod Q) {x : Ω × ContinuousPath ℂ | x.1 ∈ N}) +
        (P.prod Q) {x : Ω × ContinuousPath ℂ | ¬ (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) (σ x.2) ≠ ⊤)} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ = (P.prod Q) {x : Ω × ContinuousPath ℂ | ENNReal.ofReal (η / 2) <
          clockDistD γ (fun ω => coneShift γ (hcirc ω)) dA σ (HarmonicBalls.dyadicScale k) x} := by
        rw [hNull, hF, add_zero, add_zero]

/-! ### The cone version of the closed identification of the clock -/

/-- **Cone version of `regClock_identification_closed`** (tex:370-414 for the γ-quantum cone). The whole-plane GFF
`hGFF` of `regClock_identification_closed` is replaced by the quantum cone `hcone` (continuity of the circle averages
off a null set, measurability of each circle average, `exists_null_continuous_cone`), and the origin tail moment by its
cone form `hT0cone` for the field `hc = coneShift γ hcirc` (lem:occ-tails, appendix tex:296, through eq:occ-field,
tex:20-29), a named hypothesis. The other hypotheses are those of `regClock_identification_closed`. -/
theorem regClock_identification_cone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc)
    (hc : Ω → ℝ → ℂ → ℝ) (hc_def : hc = fun ω => coneShift γ (hcirc ω))
    (hT0cone : ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    (μ ν : Ω → Measure ℂ) (hD : ball z r ⊆ ball (0 : ℂ) 1)
    (hbase : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), q (b u) ∂(dA ω b) ∂(HarmonicBalls.planarBrownianMotion y) =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * HarmonicBalls.greenFunction (ball z r) y x) * q x ∂(ν ω))
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (exitNN z r b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω))
    (hS3 : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(μ ω) < ⊤)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ hc dA (exitNN z r) ε a x}) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistD γ hc dA (exitNN z r) ε x}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have hσ : Measurable (exitNN z r) :=
    ENNReal.measurable_toNNReal.comp (ContinuousPath.measurable_exitTime (ball z r) Metric.isOpen_ball)
  obtain ⟨N, hN, hN0, hgood0⟩ := exists_null_continuous_cone γ hcone
  have hgood : ∀ ω, ω ∉ N → ∀ ε : ℝ, 0 < ε → Continuous fun x : ℂ => hc ω ε x := fun ω hω ε hε => by
    rw [hc_def]
    exact hgood0 ω hω ε hε
  have hmeasCirc : ∀ ε : ℝ, 0 < ε → ∀ x : ℂ, Measurable fun ω => hc ω ε x := fun ε hε x => by
    rw [hc_def]
    exact (hcone.measurable_circle ε x hε).add measurable_const
  have hreg' : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (modField N hc ω)) := fun ω ε hε =>
    measurable_regDensity_of_continuous γ ε hε _ (modField_continuous hgood ω ε hε)
  have hνm' : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (nuDensity γ ε (modField N hc ω)) := fun ω ε hε =>
    measurable_nuDensity_of_continuous γ ε _ (modField_continuous hgood ω ε hε)
  have hRm' : ∀ ε a : ℝ, 0 < ε → Measurable (clockDistR γ (modField N hc) (exitNN z r) ε a) :=
    fun ε a hε => measurable_modField_clockDistR hN hmeasCirc hgood γ ε a hε (exitNN z r) hσ
  have hQm : ∀ a : ℝ, Measurable (clockDistQ γ dA (exitNN z r) a) :=
    fun a => measurable_clockDistQ_of_kernel γ dA K hK hσ a
  have hfin := weightedClock_ae_prod_ne_top P (HarmonicBalls.planarBrownianMotion y) γ hD μ ν dA
    (exitNN z r) K hK hσ hbase hmeas hweight hS3
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  -- the origin tail moment of the modified field, transferred from `hc` along the null set `N`
  have hT0 : ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (modField N hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := by
    obtain ⟨C, a₀, ha₀, hT⟩ := hT0cone
    refine ⟨C, a₀, ha₀, fun a ha ε hε => ?_⟩
    have hae : (fun ω => weightedMass γ ε (modField N hc ω) (ball 0 a) ^ p) =ᵐ[P]
        (fun ω => weightedMass γ ε (hc ω) (ball 0 a) ^ p) := by
      filter_upwards [hNae] with ω hω
      rw [modField_eq_of_not_mem hω]
    exact (lintegral_congr_ae hae).trans_le (hT a ha ε hε)
  have hR' := removed_tail_small_mod P hγ0 hγ2 hp0 hp1 hκ (modField N hc) hT0 hr hr2 hG hy hS0 hreg' hRm'
  have hE' : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ (modField N hc) dA (exitNN z r) ε a x}) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro a ha η hη
    refine Tendsto.congr (fun ε => ?_) (hE a ha η hη)
    refine measure_prod_congr_of_fst_notMem _ hN0 (fun x hx => ?_)
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    unfold clockDistE
    rw [modField_eq_of_not_mem hx]
  have main := regClock_identification P (HarmonicBalls.planarBrownianMotion y) hγ0.ne' (modField N hc) dA
    (exitNN z r) hreg' hνm' hQm hfin hE' hR'
  intro η hη
  refine Tendsto.congr (fun ε => ?_) (main η hη)
  refine measure_prod_congr_of_fst_notMem _ hN0 (fun x hx => ?_) |>.symm
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold clockDistD
  rw [modField_eq_of_not_mem hx]

/-! ### The cone clock identification `S.clock = φ` (hS6) and the cone reduction -/

/-- A disc `B_r(z)` contained in `B_ρ(0)` with `ρ < 1` has `r ≤ 2`: the points `z ± 1` lie in the disc when `r > 2`,
and `2 = |(z+1) - (z-1)| ≤ |z+1| + |z-1| < 2ρ < 2`. -/
lemma radius_le_two_of_ball_subset {z : ℂ} {r ρ : ℝ} (hρ : ρ < 1) (hball : ball z r ⊆ ball 0 ρ) : r ≤ 2 := by
  by_contra hr
  rw [not_le] at hr
  have h1 : z + 1 ∈ ball z r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_one]
    linarith
  have h2 : z - 1 ∈ ball z r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_one]
    linarith
  have h3 := hball h1
  have h4 := hball h2
  rw [mem_ball, dist_zero_right] at h3 h4
  have h5 : ‖(z + 1) - (z - 1)‖ ≤ ‖z + 1‖ + ‖z - 1‖ := norm_sub_le _ _
  rw [show (z + 1) - (z - 1) = (2 : ℂ) by ring] at h5
  have h7 : ‖(2 : ℂ)‖ = 2 := by simp
  linarith

/-- **hS6 for the quantum cone** (identification `φ = Φ` of the killed-occupation chain, tex:370-425). The clock of
`S` is identified with the weighted clock of the base measure `dA` on `[0, σ]`, almost surely, for planar Brownian
paths from `y`. Abstract inputs: the cone's origin tail moment `hT0cone` (lem:occ-tails, appendix tex:296, for the
field `coneShift γ (S.hcirc ω)`), the ordinary Brownian occupation identity `hS0` (Step S0, tex:48-52), the base
identity `hbase` (lem:occ-base, tex:140-151), its measurability `hmeas`, the weight identity `hweight` (eq:occ-weight),
the finiteness `hS3`, and the χ_a-parts convergence `hE` (tex:377-385). The LQG clock property `isLQGClock` is that of
`MatedCRTEnv.IsValid`. -/
theorem hS6_cone (𝒮 : SpaceFillingSLEModel) {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hT0cone : ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (coneShift γ (S.hcirc ω)) (ball 0 a) ^ p ∂S.P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0) [IsSFiniteKernel K] (hK : ∀ x, K x = dA x.1 x.2)
    (ν : Ω → Measure ℂ) (hD : ball z r ⊆ ball (0 : ℂ) 1)
    (hbase : BaseOccupationIdentity S.P (HarmonicBalls.planarBrownianMotion y) (ball z r)
      (HarmonicBalls.greenFunction (ball z r) y) ν dA (exitNN z r))
    (hmeas : ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (exitNN z r b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂S.P, ∀ T : Set ℂ, MeasurableSet T → T ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in T, g x ∂(S.μ ω) = ∫⁻ x in T, g x * gammaWeight γ x ∂(ν ω))
    (hS3 : ∀ᵐ ω ∂S.P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(S.μ ω) < ⊤)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (S.P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ (fun ω => coneShift γ (S.hcirc ω)) dA (exitNN z r) ε a x})
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂HarmonicBalls.planarBrownianMotion y, ∀ s ≤ exitNN z r b,
      S.clock ω b s = (weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (exitNN z r b) s).toReal := by
  have hσ : Measurable (exitNN z r) :=
    ENNReal.measurable_toNNReal.comp (ContinuousPath.measurable_exitTime (ball z r) Metric.isOpen_ball)
  have := hS.isProbabilityMeasure
  have hcone := hS.isQuantumCone
  obtain ⟨N, hN, hN0, hcont⟩ := exists_null_continuous_cone γ hcone
  have hfin := weightedClock_ae_prod_ne_top S.P (HarmonicBalls.planarBrownianMotion y) γ hD S.μ ν dA
    (exitNN z r) K hK hσ hbase hmeas hweight hS3
  have hcv := regClock_identification_cone S.P hγ0 hγ2 hp0 hp1 hκ hcone (fun ω => coneShift γ (S.hcirc ω)) rfl
    hT0cone dA hr hr2 hG hy hS0 K hK S.μ ν hD hbase hmeas hweight hS3 hE
  have hlq : ∀ᵐ ω ∂S.P, ∀ (T : ℝ≥0) (η : ℝ), 0 < η →
      Tendsto (fun k : ℕ => (HarmonicBalls.planarBrownianMotion y)
        {b | ∃ t ≤ T, η ≤ |HarmonicBalls.lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) b t -
          S.clock ω b t|}) atTop (𝓝 0) :=
    hS.isLQGClock.mono fun ω hω => (hω y).1
  exact clock_eq_of_approx_convergence S.P (HarmonicBalls.planarBrownianMotion y) (exitNN z r)
    (fun k ω b s => HarmonicBalls.lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) b s)
    (fun ω b s => (weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (exitNN z r b) s).toReal) S.clock
    (fun η hη => tendsto_approx_cone S.P (HarmonicBalls.planarBrownianMotion y) S.hcirc dA (exitNN z r)
      ⟨N, hN, hN0, hcont⟩ hfin hcv η hη) hlq

/-- **Killed-occupation reduction with the cone identification** (the frozen `frozenLBMGreenOccupationRescaled_of_appendixB`,
OccupationAssembly.lean:178, with its hypothesis `hS6` derived by `hS6_cone`). Its named inputs are those of the frozen
reduction, except `hS6`, together with: `hS0` (Step S0, the ordinary Brownian occupation identity, tex:48-52), `hT0cone`
(lem:occ-tails, appendix tex:296, for the field `coneShift γ (S.hcirc ω)`, for every admissible exponent `p`), `hE`
(the χ_a-parts converge in probability, tex:377-385), and `hKern` (the base clock `dA` is the kernel `K` of its
measurability, implicit in lem:occ-base). -/
theorem frozenLBMGreenOccupationRescaled_of_appendixB_cone (𝒮 : SpaceFillingSLEModel)
    (ν : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → Measure ℂ)
    (dA : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hm0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → 0 < S.m₀)
    (hBase : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      BaseOccupationIdentity S.P (HarmonicBalls.planarBrownianMotion y) (ball z r)
        (HarmonicBalls.greenFunction (ball z r) y) (ν γ Ω S) (dA γ Ω S) (exitNN z r))
    (hWeight : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → OccWeightIdentity S.P S.μ (ν γ Ω S) γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(dA γ Ω S ω b))
    (hS0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ → BrownianOccupationOnBall z r)
    (hT0cone : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ p κ : ℝ, 0 < p → p < min 1 (4 / γ ^ 2 - 1) → κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 →
      ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
        ∫⁻ ω, weightedMass γ ε (coneShift γ (S.hcirc ω)) (ball 0 a) ^ p ∂S.P ≤
          ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p))
    (hE : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
        Tendsto (fun ε => (S.P.prod (HarmonicBalls.planarBrownianMotion y))
          {x | ENNReal.ofReal η < clockDistE γ (fun ω => coneShift γ (S.hcirc ω)) (dA γ Ω S) (exitNN z r) ε a x})
          (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hKern : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0, IsSFiniteKernel K ∧
        ∀ x, K x = dA γ Ω S x.1 x.2)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ e : ℝ, 0 < e ∧ BGMassUpperBoundDyadic S.P S.μ e)
    (hGreen : ∀ ρ : ℝ, ∀ z : ℂ, ∀ r : ℝ, 0 < r → ball z r ⊆ ball 0 ρ → GreenDiskFormula z r)
    (hExit : ∀ (z y : ℂ) (r : ℝ), 0 < r → y ∈ ball z r →
      ∀ᵐ (b : ContinuousPath ℂ) ∂HarmonicBalls.planarBrownianMotion y, HarmonicBalls.pathExitTime (ball z r) ⇑b < ⊤) :
    FrozenLBMGreenOccupationRescaled 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS r z y hr hball hy
  have := hS.isProbabilityMeasure
  obtain ⟨e, he, hBGe⟩ := hBG γ hγ0 hγ2 Ω S hS
  have hS3 : ∀ᵐ ω ∂S.P, ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ∂(S.μ ω) < ⊤ :=
    ae_greenFunction_lintegral_lt_top S.P S.μ he hBGe hρ1 hr hball (hGreen ρ z r hr hball) hy
  have hclock : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂HarmonicBalls.planarBrownianMotion y, HarmonicBalls.IsTimeChangeClock (S.clock ω b) :=
    hS.isLQGClock.mono fun _ hω => (hω y).2
  have hσexit : ∀ᵐ b ∂HarmonicBalls.planarBrownianMotion y,
      (∀ s < exitNN z r b, b s ∈ ball z r) ∧ b (exitNN z r b) ∉ ball z r :=
    (hExit z y r hr hy).mono fun b hb => exitNN_props_of_lt_top hb
  obtain ⟨p, κ, hp0, hp1, hκ⟩ : ∃ p κ : ℝ, 0 < p ∧ p < min 1 (4 / γ ^ 2 - 1) ∧
      κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 := by
    have h4 : 1 < 4 / γ ^ 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)]
      nlinarith [mul_pos hγ0 hγ0]
    have hm : 0 < min 1 (4 / γ ^ 2 - 1) := lt_min one_pos (by linarith)
    exact ⟨min 1 (4 / γ ^ 2 - 1) / 2, (2 - γ ^ 2 / 2) * (min 1 (4 / γ ^ 2 - 1) / 2) -
      γ ^ 2 * (min 1 (4 / γ ^ 2 - 1) / 2) ^ 2 / 2, half_pos hm, by linarith, rfl⟩
  have hr2 : r ≤ 2 := radius_le_two_of_ball_subset hρ1 hball
  have hD : ball z r ⊆ ball (0 : ℂ) 1 := hball.trans (Metric.ball_subset_ball hρ1.le)
  obtain ⟨K, hKs, hK⟩ := hKern γ hγ0 hγ2 Ω S hS
  have := hKs
  have hS6 := hS6_cone 𝒮 hγ0 hγ2 S hS hp0 hp1 hκ (hT0cone γ hγ0 hγ2 Ω S hS p κ hp0 hp1 hκ) (dA γ Ω S) hr hr2
    (hGreen ρ z r hr hball) hy (hS0 ρ hρ0 hρ1 z r hr hball) K hK (ν γ Ω S) hD
    (hBase γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy) (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    (weight_identity_of_occWeight (hWeight γ hγ0 hγ2 Ω S hS)) hS3
    (hE γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
  exact rescaled_occupation_green_identity S γ ρ hγ0 hγ2 hρ0 hρ1 𝒮 hS r z y hr hball hy (ν γ Ω S) (dA γ Ω S)
    (exitNN z r) (hm0 γ hγ0 hγ2 Ω S hS) hclock hσexit (hBase γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    (weight_identity_of_occWeight (hWeight γ hγ0 hγ2 Ω S hS)) hS6 hS3

end MatedCRT.KilledOccupation
