import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementDecomposition

/-!
# The energy identity for occupation functionals of killed planar Brownian motion

For an open set `D`, a Borel rate `f ≥ 0` and a continuous path `b`, the occupation functional of `b` killed at its
exit time `τ_D(b)` is `A^f(b) = ∫_0^{τ_D(b)} f(b_s) ds` (`killedOccupation`): the positive continuous additive
functional of planar Brownian motion killed on exiting `D` whose Revuz measure is `f(y) dy`. Its potential is
`u_f(w) = E_w[A^f]` (`killedPotential`; the `0`-order potential of an additive functional of a transient process,
Fukushima–Oshima–Takeda (2011), §5.1).

By the simple Markov property of planar Brownian motion at a fixed time,
`E_w[A^f A^g] = u_{f u_g}(w) + u_{g u_f}(w)` (`lintegral_killedOccupation_mul`), the energy identity of additive
functionals. Consequently, if `u_f, u_g ≤ M` and `|u_f - u_g| ≤ δ` on `D`, then
`E_w[(A^f - A^g)²] ≤ 2 δ (u_f(w) + u_g(w))` (`lintegral_sq_killedOccupation_sub_le`): additive functionals whose
potentials are uniformly close are close in `L²`. This is the estimate behind the identification of a time change of
killed Brownian motion through the potential of its Revuz measure, as in the conformal invariance of Liouville
Brownian motion (Berestycki (2015), Theorem 1.3).

## Main statements

* `killedTail_eq_killedOccupation_shift`: after a time `s` before the exit time, the rest of the occupation
  functional is the occupation functional of the path shifted by `s`.
* `lintegral_killedRate_mul_killedTail`: the Markov property at a fixed time, integrated in time.
* `killedOccupation_mul_eq_add`: pathwise, `A^f A^g` splits along the diagonal.
* `lintegral_killedOccupation_mul`: `E_w[A^f A^g] = u_{f u_g}(w) + u_{g u_f}(w)`.
* `lintegral_sq_killedOccupation_sub_le`: `E_w[(A^f - A^g)²] ≤ 2 δ (u_f(w) + u_g(w))`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess HarmonicBalls

/-! ### Occupation functionals of the killed path -/

/-- The times `0 < s < τ_D(b)` before the exit time of the path `b` from `D`. -/
def killedTimes (D : Set ℂ) (b : ContinuousPath ℂ) : Set ℝ :=
  {s | 0 < s ∧ ENNReal.ofReal s < ContinuousPath.exitTime D b}

/-- The rate `f` along the path `b` killed at its exit from `D`: `s ↦ 1_{0 < s < τ_D(b)} f(b_s)`. -/
noncomputable def killedRate (D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (s : ℝ) : ℝ≥0∞ :=
  (killedTimes D b).indicator (fun s => f (b s.toNNReal)) s

/-- The occupation functional `A^f(b) = ∫_0^{τ_D(b)} f(b_s) ds` of the path killed at its exit from `D`. -/
noncomputable def killedOccupation (D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s, killedRate D f b s

/-- The part `∫_s^{τ_D(b)} f(b_r) dr` of the occupation functional after the time `s`. -/
noncomputable def killedTail (D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ r, (Ioi s).indicator (killedRate D f b) r

/-- The potential `u_f(w) = E_w[∫_0^{τ_D} f(B_s) ds]` of the occupation functional of planar Brownian motion from
`w` killed on exiting `D`. -/
noncomputable def killedPotential (D : Set ℂ) (f : ℂ → ℝ≥0∞) (w : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, killedOccupation D f b ∂planarBrownianMotion w

variable {D : Set ℂ}

theorem measurable_killedRate (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p : ContinuousPath ℂ × ℝ => killedRate D f p.1 p.2) := by
  have hS : MeasurableSet {p : ContinuousPath ℂ × ℝ |
      0 < p.2 ∧ ENNReal.ofReal p.2 < ContinuousPath.exitTime D p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst))
  have heval : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have hb : Measurable (fun p : ContinuousPath ℂ × ℝ => f (p.1 p.2.toNNReal)) :=
    hf.comp (heval.comp (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd)))
  exact hb.indicator hS

theorem measurable_killedOccupation (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (killedOccupation D f) := by
  show Measurable fun b => ∫⁻ s, killedRate D f b s
  exact (measurable_killedRate hD hf).lintegral_prod_right'

theorem measurable_killedTail (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p : ContinuousPath ℂ × ℝ => killedTail D f p.1 p.2) := by
  have hS : MeasurableSet {q : (ContinuousPath ℂ × ℝ) × ℝ | q.1.2 < q.2} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd
  have hF : Measurable (fun q : (ContinuousPath ℂ × ℝ) × ℝ =>
      (Ioi q.1.2).indicator (killedRate D f q.1.1) q.2) :=
    ((measurable_killedRate hD hf).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hS
  exact hF.lintegral_prod_right'

theorem measurable_killedPotential (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (killedPotential D f) := by
  show Measurable fun w => ∫⁻ b, killedOccupation D f b ∂planarBrownianMotion w
  exact (measurable_killedOccupation hD hf).lintegral_kernel

/-! ### The Markov property for the tail of the occupation functional -/

/-- After a time `s ≥ 0` before the exit time, the tail `∫_s^{τ_D(b)} f(b_r) dr` of the occupation functional is
the occupation functional of the path shifted by `s`. -/
theorem killedTail_eq_killedOccupation_shift (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < ContinuousPath.exitTime D b) :
    killedTail D f b s = killedOccupation D f (ContinuousPath.shift s.toNNReal b) := by
  have hadd := ContinuousPath.exitTime_shift_add D b s.toNNReal hs
  rw [killedTail, killedOccupation, ← lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (killedRate D f (ContinuousPath.shift s.toNNReal b)) (-s)]
  refine lintegral_congr fun r => ?_
  by_cases hr : s < r
  · have hr0 : 0 < r := lt_of_le_of_lt hs0 hr
    have hrs : 0 < r + -s := by linarith
    have hlt : ENNReal.ofReal r < ContinuousPath.exitTime D b ↔
        ENNReal.ofReal (r + -s) < ContinuousPath.exitTime D (ContinuousPath.shift s.toNNReal b) := by
      have hr' : ENNReal.ofReal r = ENNReal.ofReal (r + -s) + ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_add hrs.le hs0]
        congr 1
        ring
      rw [hr', ← hadd]
      exact ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top
    have hpt : s.toNNReal + (r + -s).toNNReal = r.toNNReal := by
      rw [← Real.toNNReal_add hs0 hrs.le]
      congr 1
      ring
    rw [Set.indicator_of_mem (mem_Ioi.2 hr)]
    by_cases hτ : ENNReal.ofReal r < ContinuousPath.exitTime D b
    · simp only [killedRate]
      rw [Set.indicator_of_mem (show r ∈ killedTimes D b from ⟨hr0, hτ⟩),
        Set.indicator_of_mem (show r + -s ∈ killedTimes D (ContinuousPath.shift s.toNNReal b) from
          ⟨hrs, hlt.1 hτ⟩), ContinuousPath.shift_apply, hpt]
    · simp only [killedRate]
      rw [Set.indicator_of_notMem (show r ∉ killedTimes D b from fun h => hτ h.2),
        Set.indicator_of_notMem (show r + -s ∉ killedTimes D (ContinuousPath.shift s.toNNReal b) from
          fun h => hτ (hlt.2 h.2))]
  · have hrs : ¬ 0 < r + -s := fun h => hr (by linarith)
    rw [Set.indicator_of_notMem (show r ∉ Ioi s from hr)]
    simp only [killedRate]
    rw [Set.indicator_of_notMem (show r + -s ∉ killedTimes D (ContinuousPath.shift s.toNNReal b) from
      fun h => hrs h.1)]

/-- **The Markov property integrated in time.** For Borel rates `f, g ≥ 0`,
`E_w[∫_0^{τ_D} f(B_s) (∫_s^{τ_D} g(B_r) dr) ds] = u_{f u_g}(w)`. -/
theorem lintegral_killedRate_mul_killedTail (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (w : ℂ) :
    ∫⁻ b, (∫⁻ s, killedRate D f b s * killedTail D g b s) ∂planarBrownianMotion w =
      killedPotential D (fun y => f y * killedPotential D g y) w := by
  have hfu : Measurable (fun y => f y * killedPotential D g y) :=
    hf.mul (measurable_killedPotential hD hg)
  have hm : Measurable (fun p : ContinuousPath ℂ × ℝ =>
      killedRate D f p.1 p.2 * killedTail D g p.1 p.2) :=
    (measurable_killedRate hD hf).mul (measurable_killedTail hD hg)
  have hocc := measurable_killedOccupation hD hg
  have h0 : Measurable (fun b : ContinuousPath ℂ => b 0) := ContinuousPath.measurable_coordinateProcess _
  have hH : Measurable (fun b : ContinuousPath ℂ => f (b 0) * killedOccupation D g b) := (hf.comp h0).mul hocc
  show ∫⁻ b, (∫⁻ s, killedRate D f b s * killedTail D g b s) ∂planarBrownianMotion w =
    ∫⁻ b, (∫⁻ s, killedRate D (fun y => f y * killedPotential D g y) b s) ∂planarBrownianMotion w
  rw [lintegral_lintegral_swap (f := fun b s => killedRate D f b s * killedTail D g b s) hm.aemeasurable,
    lintegral_lintegral_swap (f := fun b s => killedRate D (fun y => f y * killedPotential D g y) b s)
      (measurable_killedRate hD hfu).aemeasurable]
  refine lintegral_congr fun s => ?_
  by_cases hs : 0 < s
  · let A : Set (ContinuousPath ℂ) := {b | ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}
    have hAc : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) s.toNNReal] A :=
      ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration D hD _
    have hAm : MeasurableSet A := ContinuousPath.measurableSet_lt_exitTime D hD _
    have hL : ∀ b, killedRate D f b s * killedTail D g b s =
        A.indicator (fun b => f ((ContinuousPath.shift s.toNNReal b) 0) *
          killedOccupation D g (ContinuousPath.shift s.toNNReal b)) b := by
      intro b
      by_cases hb : b ∈ A
      · rw [Set.indicator_of_mem hb, killedRate, Set.indicator_of_mem (show s ∈ killedTimes D b from ⟨hs, hb⟩),
          killedTail_eq_killedOccupation_shift g b hs.le hb, ContinuousPath.shift_apply, add_zero]
      · rw [Set.indicator_of_notMem hb, killedRate,
          Set.indicator_of_notMem (show s ∉ killedTimes D b from fun h => hb h.2), zero_mul]
    calc ∫⁻ b, killedRate D f b s * killedTail D g b s ∂planarBrownianMotion w
        = ∫⁻ b in A, f ((ContinuousPath.shift s.toNNReal b) 0) *
            killedOccupation D g (ContinuousPath.shift s.toNNReal b) ∂planarBrownianMotion w := by
          rw [← lintegral_indicator hAm]
          exact lintegral_congr hL
      _ = ∫⁻ b in A, (∫⁻ b', f (b' 0) * killedOccupation D g b'
            ∂planarBrownianMotion (b s.toNNReal)) ∂planarBrownianMotion w :=
          setLIntegral_shift_planarBrownianMotion w s.toNNReal hAc hH
      _ = ∫⁻ b in A, f (b s.toNNReal) * killedPotential D g (b s.toNNReal) ∂planarBrownianMotion w := by
          refine lintegral_congr fun b => ?_
          rw [killedPotential, ← lintegral_const_mul _ hocc]
          refine lintegral_congr_ae ?_
          filter_upwards [ae_planarBrownianMotion_eval_zero (b s.toNNReal)] with b' hb'
          rw [hb']
      _ = ∫⁻ b, killedRate D (fun y => f y * killedPotential D g y) b s ∂planarBrownianMotion w := by
          rw [← lintegral_indicator hAm]
          refine lintegral_congr fun b => ?_
          by_cases hb : b ∈ A
          · rw [Set.indicator_of_mem hb, killedRate,
              Set.indicator_of_mem (show s ∈ killedTimes D b from ⟨hs, hb⟩)]
          · rw [Set.indicator_of_notMem hb, killedRate,
              Set.indicator_of_notMem (show s ∉ killedTimes D b from fun h => hb h.2)]
  · have hz : ∀ (h : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ), killedRate D h b s = 0 := fun h b =>
      Set.indicator_of_notMem (show s ∉ killedTimes D b from fun h' => hs h'.1) _
    simp only [hz, zero_mul, lintegral_zero]

/-! ### The energy identity -/

/-- Splitting a product of two time integrals along the diagonal:
`(∫ F)(∫ G) = ∫ F(s) ∫_{r > s} G(r) dr ds + ∫ G(s) ∫_{r > s} F(r) dr ds`. -/
theorem lintegral_mul_lintegral_eq_add {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ s, F s) * (∫⁻ r, G r) =
      (∫⁻ s, F s * ∫⁻ r, (Ioi s).indicator G r) + ∫⁻ s, G s * ∫⁻ r, (Ioi s).indicator F r := by
  have hIoi : ∀ H : ℝ → ℝ≥0∞, Measurable H →
      Measurable (fun p : ℝ × ℝ => (Ioi p.1).indicator H p.2) := fun H hH =>
    (hH.comp measurable_snd).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hsplit : ∀ s : ℝ, ∫⁻ r, G r = (∫⁻ r, (Ioi s).indicator G r) + ∫⁻ r, (Iio s).indicator G r := by
    intro s
    have hIoi : MeasurableSet (Ioi s) := measurableSet_Ioi
    have hIio : MeasurableSet (Iio s) := measurableSet_Iio
    have hae : (Iio s : Set ℝ) =ᵐ[volume] (Ioi s)ᶜ := by
      rw [compl_Ioi]
      exact Iio_ae_eq_Iic
    rw [lintegral_indicator hIoi, lintegral_indicator hIio, setLIntegral_congr hae,
      lintegral_add_compl G hIoi]
  have hswap : ∫⁻ s, F s * ∫⁻ r, (Iio s).indicator G r = ∫⁻ r, G r * ∫⁻ s, (Ioi r).indicator F s := by
    have hm : Measurable (fun p : ℝ × ℝ => F p.1 * (Iio p.1).indicator G p.2) :=
      (hF.comp measurable_fst).mul
        ((hG.comp measurable_snd).indicator (measurableSet_lt measurable_snd measurable_fst))
    calc ∫⁻ s, F s * ∫⁻ r, (Iio s).indicator G r
        = ∫⁻ s, ∫⁻ r, F s * (Iio s).indicator G r :=
          lintegral_congr fun s => (lintegral_const_mul _ (hG.indicator measurableSet_Iio)).symm
      _ = ∫⁻ r, ∫⁻ s, F s * (Iio s).indicator G r :=
          lintegral_lintegral_swap (f := fun s r => F s * (Iio s).indicator G r) hm.aemeasurable
      _ = ∫⁻ r, G r * ∫⁻ s, (Ioi r).indicator F s := by
          refine lintegral_congr fun r => ?_
          rw [← lintegral_const_mul _ (hF.indicator measurableSet_Ioi)]
          refine lintegral_congr fun s => ?_
          by_cases hrs : r < s
          · rw [Set.indicator_of_mem (show r ∈ Iio s from hrs), Set.indicator_of_mem (show s ∈ Ioi r from hrs),
              mul_comm]
          · rw [Set.indicator_of_notMem (show r ∉ Iio s from hrs),
              Set.indicator_of_notMem (show s ∉ Ioi r from hrs), mul_zero, mul_zero]
  have hm1 : Measurable (fun s => F s * ∫⁻ r, (Ioi s).indicator G r) :=
    hF.mul (hIoi G hG).lintegral_prod_right'
  calc (∫⁻ s, F s) * (∫⁻ r, G r)
      = ∫⁻ s, F s * ∫⁻ r, G r := (lintegral_mul_const _ hF).symm
    _ = ∫⁻ s, (F s * (∫⁻ r, (Ioi s).indicator G r) + F s * ∫⁻ r, (Iio s).indicator G r) := by
        refine lintegral_congr fun s => ?_
        rw [← mul_add, ← hsplit s]
    _ = _ := by rw [lintegral_add_left hm1, hswap]

theorem measurable_killedRate_path (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) (b : ContinuousPath ℂ) :
    Measurable (killedRate D f b) :=
  (measurable_killedRate hD hf).comp measurable_prodMk_left

theorem measurable_lintegral_killedRate_mul_killedTail (hD : IsOpen D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => ∫⁻ s, killedRate D f b s * killedTail D g b s := by
  have hfg : Measurable (fun p : ContinuousPath ℂ × ℝ => killedRate D f p.1 p.2 * killedTail D g p.1 p.2) :=
    (measurable_killedRate hD hf).mul (measurable_killedTail hD hg)
  exact hfg.lintegral_prod_right'

/-- Pathwise, the product of two occupation functionals splits along the diagonal into the integrals of one rate
against the tail of the other. -/
theorem killedOccupation_mul_eq_add (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (b : ContinuousPath ℂ) :
    killedOccupation D f b * killedOccupation D g b =
      (∫⁻ s, killedRate D f b s * killedTail D g b s) + ∫⁻ s, killedRate D g b s * killedTail D f b s :=
  lintegral_mul_lintegral_eq_add (measurable_killedRate_path hD hf b) (measurable_killedRate_path hD hg b)

/-- **The energy identity** for occupation functionals of killed planar Brownian motion:
`E_w[A^f A^g] = u_{f u_g}(w) + u_{g u_f}(w)`. -/
theorem lintegral_killedOccupation_mul (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (w : ℂ) :
    ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w =
      killedPotential D (fun y => f y * killedPotential D g y) w +
        killedPotential D (fun y => g y * killedPotential D f y) w := by
  calc ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w
      = ∫⁻ b, ((∫⁻ s, killedRate D f b s * killedTail D g b s) +
          ∫⁻ s, killedRate D g b s * killedTail D f b s) ∂planarBrownianMotion w :=
        lintegral_congr (killedOccupation_mul_eq_add hD hf hg)
    _ = (∫⁻ b, (∫⁻ s, killedRate D f b s * killedTail D g b s) ∂planarBrownianMotion w) +
          ∫⁻ b, (∫⁻ s, killedRate D g b s * killedTail D f b s) ∂planarBrownianMotion w :=
        lintegral_add_left (measurable_lintegral_killedRate_mul_killedTail hD hf hg) _
    _ = _ := by
        rw [lintegral_killedRate_mul_killedTail hD hf hg, lintegral_killedRate_mul_killedTail hD hg hf]

/-! ### Potentials are monotone and linear in the rate -/

theorem killedPotential_mono {h₁ h₂ : ℂ → ℝ≥0∞} (h : ∀ y ∈ D, h₁ y ≤ h₂ y) (w : ℂ) :
    killedPotential D h₁ w ≤ killedPotential D h₂ w := by
  refine lintegral_mono fun b => lintegral_mono fun s => ?_
  by_cases hs : s ∈ killedTimes D b
  · simp only [killedRate, Set.indicator_of_mem hs]
    exact h _ (ContinuousPath.mem_of_lt_exitTime D b s.toNNReal hs.2)
  · simp only [killedRate, Set.indicator_of_notMem hs, le_refl]

theorem killedPotential_add (hD : IsOpen D) {h₁ h₂ : ℂ → ℝ≥0∞} (hh₁ : Measurable h₁) (w : ℂ) :
    killedPotential D (fun y => h₁ y + h₂ y) w = killedPotential D h₁ w + killedPotential D h₂ w := by
  have hr : ∀ b s, killedRate D (fun y => h₁ y + h₂ y) b s = killedRate D h₁ b s + killedRate D h₂ b s :=
    fun b s => by
      by_cases hs : s ∈ killedTimes D b
      · simp only [killedRate, Set.indicator_of_mem hs]
      · simp only [killedRate, Set.indicator_of_notMem hs, add_zero]
  have hocc : ∀ b, killedOccupation D (fun y => h₁ y + h₂ y) b =
      killedOccupation D h₁ b + killedOccupation D h₂ b := fun b => by
    simp only [killedOccupation, hr]
    exact lintegral_add_left ((measurable_killedRate hD hh₁).comp measurable_prodMk_left) _
  simp only [killedPotential, hocc]
  exact lintegral_add_left (measurable_killedOccupation hD hh₁) _

theorem killedPotential_const_mul (hD : IsOpen D) {h : ℂ → ℝ≥0∞} (hh : Measurable h) (c : ℝ≥0∞) (w : ℂ) :
    killedPotential D (fun y => c * h y) w = c * killedPotential D h w := by
  have hr : ∀ b s, killedRate D (fun y => c * h y) b s = c * killedRate D h b s := fun b s => by
    by_cases hs : s ∈ killedTimes D b
    · simp only [killedRate, Set.indicator_of_mem hs]
    · simp only [killedRate, Set.indicator_of_notMem hs, mul_zero]
  have hocc : ∀ b, killedOccupation D (fun y => c * h y) b = c * killedOccupation D h b := fun b => by
    simp only [killedOccupation, hr]
    exact lintegral_const_mul c ((measurable_killedRate hD hh).comp measurable_prodMk_left)
  simp only [killedPotential, hocc]
  exact lintegral_const_mul c (measurable_killedOccupation hD hh)

/-! ### The `L²` estimate -/

/-- If `x` and `y` differ by at most `δ`, then `a x + b y ≤ a y + b x + δ (a + b)`. -/
theorem mul_add_mul_le_of_le_add {a b x y δ : ℝ≥0∞} (hxy : x ≤ y + δ) (hyx : y ≤ x + δ) :
    a * x + b * y ≤ a * y + b * x + δ * (a + b) := by
  rcases le_total x y with h | h
  · have h1 : a * x ≤ a * y := mul_le_mul_of_nonneg_left h zero_le
    have h2 : b * y ≤ b * x + δ * (a + b) :=
      calc b * y ≤ b * (x + δ) := mul_le_mul_of_nonneg_left hyx zero_le
        _ = b * x + δ * b := by rw [mul_add, mul_comm b δ]
        _ ≤ b * x + δ * (a + b) := add_le_add le_rfl (mul_le_mul_of_nonneg_left le_add_self zero_le)
    calc a * x + b * y ≤ a * y + (b * x + δ * (a + b)) := add_le_add h1 h2
      _ = a * y + b * x + δ * (a + b) := (add_assoc _ _ _).symm
  · have h1 : b * y ≤ b * x := mul_le_mul_of_nonneg_left h zero_le
    have h2 : a * x ≤ a * y + δ * (a + b) :=
      calc a * x ≤ a * (y + δ) := mul_le_mul_of_nonneg_left hxy zero_le
        _ = a * y + δ * a := by rw [mul_add, mul_comm a δ]
        _ ≤ a * y + δ * (a + b) := add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)
    calc a * x + b * y ≤ a * y + δ * (a + b) + b * x := add_le_add h2 h1
      _ = a * y + b * x + δ * (a + b) := add_right_comm _ _ _

/-- `x² + y² = (x - y)² + 2 x y` for nonnegative reals, in `ℝ≥0∞`. -/
theorem ofReal_mul_self_add_mul_self {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal x * ENNReal.ofReal x + ENNReal.ofReal y * ENNReal.ofReal y =
      ENNReal.ofReal ((x - y) ^ 2) + 2 * (ENNReal.ofReal x * ENNReal.ofReal y) := by
  rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul hy, ← ENNReal.ofReal_mul hx,
    ← ENNReal.ofReal_add (mul_self_nonneg x) (mul_self_nonneg y),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hx hy))]
  congr 1
  ring

/-- **Occupation functionals with uniformly close potentials are close in `L²`.** If the potentials of the rates `f`
and `g` are at most `M < ∞` and differ by at most `δ` on `D`, then for every start `w ∈ D`,
`E_w[(A^f - A^g)²] ≤ 2 δ (u_f(w) + u_g(w))`. -/
theorem lintegral_sq_killedOccupation_sub_le (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) {M δ : ℝ≥0∞} (hM : M ≠ ⊤) (hMf : ∀ y ∈ D, killedPotential D f y ≤ M)
    (hMg : ∀ y ∈ D, killedPotential D g y ≤ M)
    (hfg : ∀ y ∈ D, killedPotential D f y ≤ killedPotential D g y + δ)
    (hgf : ∀ y ∈ D, killedPotential D g y ≤ killedPotential D f y + δ) {w : ℂ} (hw : w ∈ D) :
    ∫⁻ b, ENNReal.ofReal (((killedOccupation D f b).toReal - (killedOccupation D g b).toReal) ^ 2)
        ∂planarBrownianMotion w ≤ 2 * δ * (killedPotential D f w + killedPotential D g w) := by
  have huf := measurable_killedPotential hD hf
  have hug := measurable_killedPotential hD hg
  have hof := measurable_killedOccupation hD hf
  have hog := measurable_killedOccupation hD hg
  have hff := lintegral_killedOccupation_mul hD hf hf w
  have hgg := lintegral_killedOccupation_mul hD hg hg w
  have hfg' := lintegral_killedOccupation_mul hD hf hg w
  have m3 : Measurable fun y => f y * killedPotential D g y := hf.mul hug
  have m4 : Measurable fun y => g y * killedPotential D f y := hg.mul huf
  have m5 : Measurable fun y => f y + g y := hf.add hg
  -- the potentials of the products
  have hpot : killedPotential D (fun y => f y * killedPotential D f y) w +
        killedPotential D (fun y => g y * killedPotential D g y) w ≤
      killedPotential D (fun y => f y * killedPotential D g y) w +
        killedPotential D (fun y => g y * killedPotential D f y) w +
        δ * (killedPotential D f w + killedPotential D g w) := by
    calc killedPotential D (fun y => f y * killedPotential D f y) w +
          killedPotential D (fun y => g y * killedPotential D g y) w
        = killedPotential D (fun y => f y * killedPotential D f y + g y * killedPotential D g y) w :=
          (killedPotential_add hD (hf.mul huf) w).symm
      _ ≤ killedPotential D (fun y => (f y * killedPotential D g y + g y * killedPotential D f y) +
            δ * (f y + g y)) w :=
          killedPotential_mono (fun y hy => mul_add_mul_le_of_le_add (hfg y hy) (hgf y hy)) w
      _ = _ := by
          have m34 : Measurable fun y => f y * killedPotential D g y + g y * killedPotential D f y := m3.add m4
          rw [killedPotential_add hD m34 w, killedPotential_add hD m3 w, killedPotential_const_mul hD m5 δ w,
            killedPotential_add hD hf w]
  -- finiteness of the cross moment
  have hufw : killedPotential D f w ≤ M := hMf w hw
  have hugw : killedPotential D g w ≤ M := hMg w hw
  have hcross1 : killedPotential D (fun y => f y * killedPotential D g y) w ≤ M * killedPotential D f w :=
    calc _ ≤ killedPotential D (fun y => M * f y) w :=
          killedPotential_mono (fun y hy =>
            (mul_le_mul_of_nonneg_left (hMg y hy) zero_le).trans_eq (mul_comm _ _)) w
      _ = M * killedPotential D f w := killedPotential_const_mul hD hf M w
  have hcross2 : killedPotential D (fun y => g y * killedPotential D f y) w ≤ M * killedPotential D g w :=
    calc _ ≤ killedPotential D (fun y => M * g y) w :=
          killedPotential_mono (fun y hy =>
            (mul_le_mul_of_nonneg_left (hMf y hy) zero_le).trans_eq (mul_comm _ _)) w
      _ = M * killedPotential D g w := killedPotential_const_mul hD hg M w
  have hac_ne : ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w ≠ ⊤ := by
    rw [hfg']
    refine ne_top_of_le_ne_top ?_ (add_le_add hcross1 hcross2)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hM (ne_top_of_le_ne_top hM hufw),
      ENNReal.mul_ne_top hM (ne_top_of_le_ne_top hM hugw)⟩
  -- the pathwise identity `a² + c² = (a - c)² + 2 a c`
  have hfin_f : ∀ᵐ b ∂planarBrownianMotion w, killedOccupation D f b ≠ ⊤ :=
    (ae_lt_top hof (ne_top_of_le_ne_top hM hufw)).mono fun _ h => h.ne
  have hfin_g : ∀ᵐ b ∂planarBrownianMotion w, killedOccupation D g b ≠ ⊤ :=
    (ae_lt_top hog (ne_top_of_le_ne_top hM hugw)).mono fun _ h => h.ne
  have hpath : ∀ᵐ b ∂planarBrownianMotion w,
      killedOccupation D f b * killedOccupation D f b + killedOccupation D g b * killedOccupation D g b =
        ENNReal.ofReal (((killedOccupation D f b).toReal - (killedOccupation D g b).toReal) ^ 2) +
          2 * (killedOccupation D f b * killedOccupation D g b) := by
    filter_upwards [hfin_f, hfin_g] with b hb1 hb2
    have h := ofReal_mul_self_add_mul_self (ENNReal.toReal_nonneg (a := killedOccupation D f b))
      (ENNReal.toReal_nonneg (a := killedOccupation D g b))
    rwa [ENNReal.ofReal_toReal hb1, ENNReal.ofReal_toReal hb2] at h
  have hsq : Measurable fun b =>
      ENNReal.ofReal (((killedOccupation D f b).toReal - (killedOccupation D g b).toReal) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hof.ennreal_toReal.sub hog.ennreal_toReal).pow_const 2)
  have hsum : ∫⁻ b, ENNReal.ofReal (((killedOccupation D f b).toReal - (killedOccupation D g b).toReal) ^ 2)
        ∂planarBrownianMotion w +
      2 * ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w =
      2 * killedPotential D (fun y => f y * killedPotential D f y) w +
        2 * killedPotential D (fun y => g y * killedPotential D g y) w := by
    have hofg : Measurable fun b => killedOccupation D f b * killedOccupation D g b := hof.mul hog
    have hoff : Measurable fun b => killedOccupation D f b * killedOccupation D f b := hof.mul hof
    rw [← lintegral_const_mul _ hofg, ← lintegral_add_left hsq, ← lintegral_congr_ae hpath,
      lintegral_add_left hoff, hff, hgg, two_mul, two_mul]
  have hkey : ∫⁻ b, ENNReal.ofReal (((killedOccupation D f b).toReal - (killedOccupation D g b).toReal) ^ 2)
        ∂planarBrownianMotion w +
      2 * ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w ≤
      2 * δ * (killedPotential D f w + killedPotential D g w) +
        2 * ∫⁻ b, killedOccupation D f b * killedOccupation D g b ∂planarBrownianMotion w := by
    rw [hsum, hfg']
    calc 2 * killedPotential D (fun y => f y * killedPotential D f y) w +
          2 * killedPotential D (fun y => g y * killedPotential D g y) w
        = 2 * (killedPotential D (fun y => f y * killedPotential D f y) w +
          killedPotential D (fun y => g y * killedPotential D g y) w) := (mul_add _ _ _).symm
      _ ≤ 2 * (killedPotential D (fun y => f y * killedPotential D g y) w +
            killedPotential D (fun y => g y * killedPotential D f y) w +
            δ * (killedPotential D f w + killedPotential D g w)) := mul_le_mul_of_nonneg_left hpot zero_le
      _ = 2 * δ * (killedPotential D f w + killedPotential D g w) +
            2 * (killedPotential D (fun y => f y * killedPotential D g y) w +
              killedPotential D (fun y => g y * killedPotential D f y) w) := by ring
  exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hac_ne) hkey

end MatedCRT
