import MatedCRT.Proofs.Sec3.KilledOccupation.ConeGFFTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# Measurable regularized occupation clock (step B1 of the transfer of thm:occ-main)

For a family `ψ` of circle averages indexed by `UnitDiskCircleIndex` and a path `b : ContinuousPath ℂ`, the
regularized occupation clock of eq:occ-clock is
`Ψ_ε(ψ, b)(s) = ∫_0^{s ∧ σ(b)} ε^{γ²/2} exp(γ ψ̃(ε, b_u)) du`,
where `ψ̃(ε, x)` is the circle-average representative: the limit superior along `n` of the values of `ψ` at the
dyadic approximants of `(ε, x)`, the approximant at mesh `2^{-n}` being obtained by dyadic rounding. Off the index
set the value of `ψ` is taken to be `0`, so that every quantity is defined for all arguments.

The lemmas of this file give joint measurability of `(ψ, b) ↦ Ψ_ε(ψ, b)(s)` for a measurable exit time `σ`
(Tonelli, `Measurable.lintegral_prod_right'`). Agreement of `ψ̃` with `ψ` at continuity points, and the identification
of `Ψ_ε` with φ_ε, are later steps and are not stated here.

Measurable structure: `ContinuousPath ℂ` carries its Borel σ-algebra (`MarkovProcess`), and the evaluation
`(t, b) ↦ b t` is jointly measurable by the Carathéodory-type lemma `measurable_uncurry_of_continuous_of_measurable`
(continuous in `t`, measurable in `b`).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open scoped Classical in
/-- The value of a circle-average family `ψ` at a point `q = (r, z)` of `ℝ × ℂ`: the value `ψ (r, z)` on the index
set `UnitDiskCircleIndex`, and `0` off it. -/
noncomputable def circleValueAt (ψ : UnitDiskCircleIndex → ℝ) (q : ℝ × ℂ) : ℝ :=
  if h : q ∈ UnitDiskCircleIndex then ψ ⟨q, h⟩ else 0

/-- Dyadic rounding at mesh `2^{-n}`: the integer triple `(⌊2^n r⌋, ⌊2^n Re z⌋, ⌊2^n Im z⌋)` of `q = (r, z)`. -/
noncomputable def dyadicRound (n : ℕ) (q : ℝ × ℂ) : ℤ × ℤ × ℤ :=
  (⌊(2 : ℝ) ^ n * q.1⌋, ⌊(2 : ℝ) ^ n * q.2.re⌋, ⌊(2 : ℝ) ^ n * q.2.im⌋)

/-- The dyadic grid point of mesh `2^{-n}` with integer coordinates `k = (k₁, k₂, k₃)`:
`(k₁ 2^{-n}, (k₂ + i k₃) 2^{-n})`. -/
noncomputable def dyadicGridPoint (n : ℕ) (k : ℤ × ℤ × ℤ) : ℝ × ℂ :=
  ((k.1 : ℝ) / 2 ^ n, ⟨(k.2.1 : ℝ) / 2 ^ n, (k.2.2 : ℝ) / 2 ^ n⟩)

/-- The circle-average representative `ψ̃(ε, x)`: the limit superior along `n` of the values of `ψ` at the dyadic
approximants `dyadicGridPoint n (dyadicRound n (ε, x))` of `(ε, x)` (B1 of MQ-li-8 (b)). -/
noncomputable def circleAverageRep (ψ : UnitDiskCircleIndex → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  limsup (fun n : ℕ => circleValueAt ψ (dyadicGridPoint n (dyadicRound n (ε, x)))) atTop

/-- The regularized occupation clock `Ψ_ε(ψ, b)(s) = ∫_0^{s ∧ σ(b)} ε^{γ²/2} exp(γ ψ̃(ε, b_u)) du`, with Lebesgue
measure `lebNN` on `ℝ≥0` (B1 of MQ-li-8 (b); eq:occ-clock). -/
noncomputable def regClockFun (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc (0 : ℝ≥0) (min s (σ b)),
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) ∂lebNN

/-- The integrand of `regClockFun` as a function of `((ψ, b), u)`: the summand at time `u`, or `0` when `u` exceeds
`s ∧ σ(b)`. -/
noncomputable def regClockIntegrand (γ ε : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (s : ℝ≥0)
    (q : ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) × ℝ≥0) : ℝ≥0∞ :=
  if q.2 ≤ min s (σ q.1.2) then
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep q.1.1 ε (q.1.2 q.2)))
  else 0

lemma measurable_circleValueAt (q : ℝ × ℂ) :
    Measurable fun ψ : UnitDiskCircleIndex → ℝ => circleValueAt ψ q := by
  by_cases h : q ∈ UnitDiskCircleIndex
  · have hfun : (fun ψ : UnitDiskCircleIndex → ℝ => circleValueAt ψ q) = fun ψ => ψ ⟨q, h⟩ := by
      funext ψ
      simp [circleValueAt, h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun ψ : UnitDiskCircleIndex → ℝ => circleValueAt ψ q) = fun _ => 0 := by
      funext ψ
      simp [circleValueAt, h]
    rw [hfun]
    exact measurable_const

lemma measurable_dyadicRound (n : ℕ) : Measurable (dyadicRound n) := by
  show Measurable fun q : ℝ × ℂ =>
    (⌊(2 : ℝ) ^ n * q.1⌋, ⌊(2 : ℝ) ^ n * q.2.re⌋, ⌊(2 : ℝ) ^ n * q.2.im⌋)
  exact Measurable.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_fst))
    (Measurable.prodMk (Int.measurable_floor.comp (measurable_const.mul (Complex.measurable_re.comp measurable_snd)))
      (Int.measurable_floor.comp (measurable_const.mul (Complex.measurable_im.comp measurable_snd))))

lemma measurable_dyadicGridCircleValue (n : ℕ) :
    Measurable fun q : (UnitDiskCircleIndex → ℝ) × (ℤ × ℤ × ℤ) =>
      circleValueAt q.1 (dyadicGridPoint n q.2) :=
  measurable_from_prod_countable_left fun k => measurable_circleValueAt (dyadicGridPoint n k)

/-- Composition of the grid-value measurability with an index map `k : β → ℤ × ℤ × ℤ`. -/
lemma measurable_gridCircleValue_comp {β : Type*} [MeasurableSpace β] (n : ℕ) (k : β → ℤ × ℤ × ℤ)
    (hk : Measurable k) :
    Measurable fun q : (UnitDiskCircleIndex → ℝ) × β => circleValueAt q.1 (dyadicGridPoint n (k q.2)) :=
  (measurable_dyadicGridCircleValue n).comp (measurable_fst.prodMk (hk.comp measurable_snd))

lemma measurable_circleAverageRep (ε : ℝ) :
    Measurable fun q : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep q.1 ε q.2 := by
  have hn : ∀ n : ℕ, Measurable fun q : (UnitDiskCircleIndex → ℝ) × ℂ =>
      circleValueAt q.1 (dyadicGridPoint n (dyadicRound n (ε, q.2))) := fun n =>
    measurable_gridCircleValue_comp n (fun q : ℂ => dyadicRound n (ε, q))
      ((measurable_dyadicRound n).comp (measurable_const.prodMk measurable_id))
  unfold circleAverageRep
  exact Measurable.limsup hn

/-- Measurability of `b ↦ F (a b, c b)` for a measurable `F` on pairs and measurable `a`, `c`. The function is
passed explicitly, so no unfolding of `F` is needed when the lemma is applied. -/
lemma measurable_comp_pair {β α₁ α₂ γ : Type*} [MeasurableSpace β] [MeasurableSpace α₁] [MeasurableSpace α₂]
    [MeasurableSpace γ] {F : α₁ × α₂ → γ} (hF : Measurable F) {a : β → α₁} {c : β → α₂}
    (ha : Measurable a) (hc : Measurable c) : Measurable fun b => F (a b, c b) :=
  hF.comp (ha.prodMk hc)

/-- Joint measurability of the evaluation `(t, b) ↦ b t` on `ℝ≥0 × ContinuousPath ℂ`. -/
lemma measurable_eval_path : Measurable fun r : ℝ≥0 × ContinuousPath ℂ => r.2 r.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (t : ℝ≥0) (b : ContinuousPath ℂ) => b t)
    (fun b => map_continuous b) (fun t => (continuous_eval_const t).measurable)

/-- The summand `ENNReal.ofReal (c exp(γ f))` of the clock is measurable when `f` is. -/
lemma measurable_ofReal_exp_mul {β : Type*} [MeasurableSpace β] (c γ : ℝ) {f : β → ℝ} (hf : Measurable f) :
    Measurable fun b => ENNReal.ofReal (c * Real.exp (γ * f b)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hf)))

lemma measurable_regIntegrand (γ ε : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (s : ℝ≥0) (hσ : Measurable σ) :
    Measurable (regClockIntegrand γ ε σ s) := by
  have hBu : Measurable fun q : ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) × ℝ≥0 => q.1.2 q.2 :=
    measurable_eval_path.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hRep : Measurable fun q : ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) × ℝ≥0 =>
      circleAverageRep q.1.1 ε (q.1.2 q.2) :=
    measurable_comp_pair (F := fun p : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep p.1 ε p.2)
      (measurable_circleAverageRep ε) (measurable_fst.comp measurable_fst) hBu
  have hval : Measurable fun q : ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) × ℝ≥0 =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep q.1.1 ε (q.1.2 q.2))) :=
    measurable_ofReal_exp_mul (ε ^ (γ ^ 2 / 2)) γ hRep
  have hset : MeasurableSet {q : ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) × ℝ≥0 |
      q.2 ≤ min s (σ q.1.2)} :=
    measurableSet_le measurable_snd (measurable_const.min (hσ.comp (measurable_snd.comp measurable_fst)))
  unfold regClockIntegrand
  exact Measurable.ite hset hval measurable_const

lemma regClock_eq_lintegral (γ ε : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (s : ℝ≥0)
    (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) :
    regClockFun γ ε p.1 σ p.2 s = ∫⁻ u, regClockIntegrand γ ε σ s (p, u) ∂lebNN := by
  rw [regClockFun, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun u => ?_
  by_cases h : u ≤ min s (σ p.2)
  · simp [Set.indicator, regClockIntegrand, h]
  · simp [Set.indicator, regClockIntegrand, h]

/-- **Step B1 (measurability of the regularized clock).** For a measurable exit time `σ`, the map
`(ψ, b) ↦ Ψ_ε(ψ, b)(s)` is measurable for the product of the cylinder σ-algebra on `UnitDiskCircleIndex → ℝ` and the
Borel σ-algebra on `ContinuousPath ℂ`. -/
theorem measurable_regClockFun (γ ε : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) (s : ℝ≥0) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ => regClockFun γ ε p.1 σ p.2 s := by
  have hfun : (fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ => regClockFun γ ε p.1 σ p.2 s) =
      fun p => ∫⁻ u, regClockIntegrand γ ε σ s (p, u) ∂lebNN :=
    funext fun p => regClock_eq_lintegral γ ε σ s p
  rw [hfun]
  exact (measurable_regIntegrand γ ε σ s hσ).lintegral_prod_right'

/-- The exit time of a ball, as an `ℝ≥0`-valued function on paths, is measurable: the hypothesis `Measurable σ` of
`measurable_regClockFun` holds for `σ = (pathExitTime (ball z r) ·).toNNReal`, the exit time of the occupation
identity (`BaseClockBinders`). -/
lemma measurable_toNNReal_pathExitTime_ball (z : ℂ) (r : ℝ) :
    Measurable fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toNNReal :=
  ENNReal.measurable_toNNReal.comp (measurable_pathExitTime_ball z r)

/-- **Step B1 for the exit time of a ball.** Joint measurability of `(ψ, b) ↦ Ψ_ε(ψ, b)(s)` with
`σ(b) = (pathExitTime (ball z r) b).toNNReal`. -/
theorem measurable_regClockFun_ball (γ ε : ℝ) (z : ℂ) (r : ℝ) (s : ℝ≥0) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ =>
      regClockFun γ ε p.1 (fun b => (pathExitTime (ball z r) b).toNNReal) p.2 s :=
  measurable_regClockFun γ ε _ (measurable_toNNReal_pathExitTime_ball z r) s

end MatedCRT.KilledOccupation
