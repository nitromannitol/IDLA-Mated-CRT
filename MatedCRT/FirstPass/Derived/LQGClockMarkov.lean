import MatedCRT.FirstPass.Derived.OptionalTimePastVariable
import MatedCRT.FirstPass.Derived.RationalPathExtension
import MatedCRT.FirstPass.Derived.MarkovTimeChangeIdentification
import MatedCRT.FirstPass.Derived.RevuzMarkovAgainstClock
import LatticeProb.Prob.MarkovPathKernelDense

/-!
# The Markov property of the time change of planar Brownian motion by a PCAF clock

Let `G` be a positive continuous additive functional of planar Brownian motion with a good clock
(`IsPCAF`, `GoodClock`), adapted to the natural filtration, and `τ_v = inf {t | v < G_t}` its right inverse.
The time-changed path `v ↦ B_{τ_v}` is read at the rational times, through the rational-time regularization
`Ḡ` of `G`, and extended continuously (`lqgTimeChange`): this is a Borel measurable map of the whole path space
which, almost surely under planar Brownian motion from every start, is the time-changed path `v ↦ B_{τ_v}`.

The path laws `K_y` of the time change are those of `lqgTimeChange G` under planar Brownian motion from `y`.
They have the Markov property (Definition 7.1 of Berestycki and Gwynne (2020)): by the strong Markov property of
planar Brownian motion at the optional time `τ_u` (the rational inverse clock at level `u`), applied to the
variable of the past `V = (B_{τ_{u ∧ q}})_q` and the shifted path `θ_{τ_u} B`, whose time change is the shift
of the time-changed path (additivity of the inverse clock, `ae_eval_clockInverse_add_eq_shift`).

* `lqgTimeChange`, `measurable_lqgTimeChange`: the time-changed path as a Borel map.
* `ae_exists_path_lqgTimeChange`: almost surely it is the path `v ↦ B_{τ_v}`.
* `ae_lqgTimeChange_shift`: almost surely `(θ_{τ_u} B)` has time change `θ_u (time change of B)`.
* `markovAt_lqgTimeChange`: the Markov property at every `(z, u)`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT

/-- The time-changed path `v ↦ b_{τ_v}`, `τ = clockInverse (regularize G)`, read at the rational times and
extended continuously (the default path where there is no continuous extension). -/
noncomputable def lqgTimeChange (G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    ContinuousPath ℂ :=
  ratExtend fun q : ℚ => b (clockInverse (regularize G) (AdaptedVersion.ratTime q) b)

theorem measurable_lqgTimeChange {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hGm : ∀ t, Measurable (G t)) :
    Measurable (lqgTimeChange G) :=
  measurable_ratExtend_comp fun _ =>
    measurable_eval_clockInverse (measurable_regularize hGm) (regularize_monotone G) _

/-- The right inverse of a continuous strictly increasing unbounded clock from `0` is continuous. -/
theorem continuous_clockInverse_of_strictMono {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω)
    (hs : StrictMono fun t => A t ω) (hu : Tendsto (fun t => A t ω) atTop atTop) :
    Continuous fun r => clockInverse A r ω := by
  have hAτ : ∀ r, A (clockInverse A r ω) ω = r := fun r =>
    apply_clockInverse_eq h0 hc hs.monotone (hu.eventually_gt_atTop r).exists
  have hmono : Monotone fun r => clockInverse A r ω := fun r s hrs => by
    refine hs.le_iff_le.1 ?_
    show A (clockInverse A r ω) ω ≤ A (clockInverse A s ω) ω
    rw [hAτ, hAτ]
    exact hrs
  have hsurj : Function.Surjective fun r => clockInverse A r ω := fun t =>
    ⟨A t ω, hs.injective (hAτ (A t ω))⟩
  exact hmono.continuous_of_surjective hsurj

/-- **Almost surely the time change is the time-changed path.** Under planar Brownian motion from `z`, almost
surely `lqgTimeChange G b` is the continuous path `v ↦ b_{τ_v}`, `τ_v = clockInverse G v b`. -/
theorem ae_exists_path_lqgTimeChange {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G)
    (hG : GoodClock planarLaw G) (z : ℂ) :
    ∀ᵐ b ∂planarLaw z, ∃ x : ContinuousPath ℂ,
      (∀ v, x v = b (clockInverse G v b)) ∧ lqgTimeChange G b = x := by
  filter_upwards [hA.path z, hG z, ae_clockInverse_regularize_eq hA z] with b hp hgood hreg
  have hc := continuous_clockInverse_of_strictMono hp.1 hp.2.1 hgood.1 hgood.2
  refine ⟨⟨fun v => b (clockInverse G v b), b.continuous.comp hc⟩, fun v => rfl, ?_⟩
  unfold lqgTimeChange
  refine ratExtend_eq_of_forall fun q => ?_
  show b (clockInverse (regularize G) (AdaptedVersion.ratTime q) b) =
    b (clockInverse G (AdaptedVersion.ratTime q) b)
  rw [hreg]

theorem pathShift_eq_shift_apply (x : ContinuousPath ℂ) (u : ℝ≥0) :
    LatticeProb.pathShift x u = ContinuousPath.shift u x :=
  ContinuousMap.ext fun t => by simp [ContinuousPath.shift_apply]

/-- **Additivity of the time change.** Almost surely, the time change of the path shifted by `τ_u` is the shift
by `u` of the time change of the path. -/
theorem ae_lqgTimeChange_shift {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G)
    (hG : GoodClock planarLaw G) (z : ℂ) (u : ℝ≥0) :
    ∀ᵐ b ∂planarLaw z, lqgTimeChange G (ContinuousPath.shift (clockInverse G u b) b) =
      LatticeProb.pathShift (lqgTimeChange G b) u := by
  filter_upwards [ae_exists_path_lqgTimeChange hA hG z, ae_eval_clockInverse_add_eq_shift hA hG z u]
    with b hb hadd
  obtain ⟨x, hx, hxb⟩ := hb
  rw [hxb]
  unfold lqgTimeChange
  refine ratExtend_eq_of_forall fun q => ?_
  show _ = x (u + AdaptedVersion.ratTime q)
  rw [hx, ← hadd]

/-- The rational inverse clock is nondecreasing in the level. -/
theorem rationalClockInverse_mono {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} {r r' : ℝ≥0} (hr : r ≤ r')
    (ω : ContinuousPath ℂ) : rationalClockInverse g r ω ≤ rationalClockInverse g r' ω := by
  unfold rationalClockInverse
  refine iInf_mono fun q => ?_
  exact le_iInf fun h => iInf_le _ (lt_of_le_of_lt hr h)

/-- The rational inverse clock of the functional `G` at rational times. -/
noncomputable def rcInv (G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (r : ℝ≥0) (b : ContinuousPath ℂ) :
    WithTop ℝ≥0 :=
  rationalClockInverse (fun q : ℚ≥0 => G (q : ℝ≥0)) r b

theorem measurableSet_rcInv_lt {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hGa : ∀ t, Measurable[pathFiltration t] (G t)) (r t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {b | rcInv G r b < t} :=
  measurableSet_rationalClockInverse_lt (g := fun q : ℚ≥0 => G (q : ℝ≥0)) (fun q => hGa q) r t

theorem ae_rcInv_eq {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G)
    (hG : GoodClock planarLaw G) (z : ℂ) :
    ∀ᵐ b ∂planarLaw z, ∀ r : ℝ≥0, rcInv G r b = (clockInverse G r b : WithTop ℝ≥0) :=
  ae_rationalClockInverse_eq_clockInverse hA hG z (g := fun q : ℚ≥0 => G (q : ℝ≥0))
    fun _ => EventuallyEq.rfl

/-- The past variable at level `u`: the time-changed path stopped at level `u`, read at the rational times,
`(b_{τ_{q ∧ u}})_q`, with `τ` the rational inverse clock. -/
noncomputable def pastVariable (G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) (b : ContinuousPath ℂ) :
    ℚ → ℂ :=
  fun q => b ((rcInv G (min (AdaptedVersion.ratTime q) u) b).untopD 0)

/-- Almost surely, the past variable is the time-changed path stopped at level `u`. -/
theorem ae_ratExtend_pastVariable {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G)
    (hG : GoodClock planarLaw G) (z : ℂ) (u : ℝ≥0) :
    ∀ᵐ b ∂planarLaw z,
      ratExtend (pastVariable G u b) = LatticeProb.stopPath (lqgTimeChange G b) u := by
  filter_upwards [ae_exists_path_lqgTimeChange hA hG z, ae_rcInv_eq hA hG z] with b hb hrc
  obtain ⟨x, hx, hxb⟩ := hb
  rw [hxb]
  refine ratExtend_eq_of_forall fun q => ?_
  show b ((rcInv G (min (AdaptedVersion.ratTime q) u) b).untopD 0) = x (min (AdaptedVersion.ratTime q) u)
  rw [hrc, WithTop.untopD_coe, hx]

/-- **The Markov property of the time change of planar Brownian motion by a PCAF clock.** Let `G` be a PCAF of
planar Brownian motion with a good clock, adapted to the natural filtration, and `K_y` the law of
`lqgTimeChange G` under planar Brownian motion from `y`, continuous in `y`.  Then `K` has the Markov property at
every `(z, u)` (Berestycki–Gwynne (2020), Definition 7.1): the conditional law of `X_{u+·}` given `X|[0,u]` is
`K_{X_u}` under `K_z`. -/
theorem markovAt_lqgTimeChange {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G)
    (hG : GoodClock planarLaw G) (hGa : ∀ t, Measurable[pathFiltration t] (G t))
    {K : ℂ → ProbabilityMeasure (ContinuousPath ℂ)} (hKc : Continuous K)
    (hK : ∀ y, (K y : Measure (ContinuousPath ℂ)) = (planarLaw y).map (lqgTimeChange G))
    (z : ℂ) (u : ℝ≥0) : LatticeProb.MarkovAt K z u := by
  intro g
  have hXm : Measurable (lqgTimeChange G) := measurable_lqgTimeChange hA.meas
  have hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {b | rcInv G u b < t} := measurableSet_rcInv_lt hGa u
  have hW : ∀ (q : ℚ) (t : ℝ≥0),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        {b | rcInv G (min (AdaptedVersion.ratTime q) u) b < t} :=
    fun q => measurableSet_rcInv_lt hGa _
  have hWT : ∀ (q : ℚ) (b : ContinuousPath ℂ),
      rcInv G (min (AdaptedVersion.ratTime q) u) b ≤ rcInv G u b :=
    fun q b => rationalClockInverse_mono (min_le_right _ _) b
  have hfin : ∀ᵐ b ∂planarLaw z, rcInv G u b < ⊤ := by
    filter_upwards [ae_rcInv_eq hA hG z] with b hb
    rw [hb u]
    exact WithTop.coe_lt_top _
  have hVm : Measurable (pastVariable G u) :=
    measurable_pi_iff.2 fun q => OptionalTime.measurable_eval_untopD (hW q)
  have hV : ∀ B : Set (ℚ → ℂ), MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (pastVariable G u ⁻¹' B ∩ {b | rcInv G u b < t}) :=
    fun B hB t => OptionalTime.measurableSet_pi_eval_untopD_inter_lt
      (W := fun q => rcInv G (min (AdaptedVersion.ratTime q) u)) hW hT hWT hB t
  have hhm : Measurable fun p : (ℚ → ℂ) × ContinuousPath ℂ => g (ratExtend p.1, lqgTimeChange G p.2) :=
    g.continuous.measurable.comp
      ((measurable_ratExtend.comp measurable_fst).prodMk (hXm.comp measurable_snd))
  have key := OptionalTime.integral_pair_shift_optionalTime z (rcInv G u) hT (pastVariable G u) hVm hV
    hfin hhm (C := ‖g‖) fun p => g.norm_coe_le_norm _
  have hstopc : Continuous fun x : ContinuousPath ℂ => LatticeProb.stopPath x u :=
    LatticeProb.continuous_stopPath_uncurry.comp (continuous_id.prodMk continuous_const)
  have hshc : Continuous fun x : ContinuousPath ℂ => LatticeProb.pathShift x u :=
    LatticeProb.continuous_pathShift_uncurry.comp (continuous_id.prodMk continuous_const)
  have hL : ∫ x, g (LatticeProb.stopPath x u, LatticeProb.pathShift x u) ∂(K z : Measure (ContinuousPath ℂ)) =
      ∫ b, g (LatticeProb.stopPath (lqgTimeChange G b) u, LatticeProb.pathShift (lqgTimeChange G b) u)
        ∂planarLaw z := by
    rw [hK z]
    exact integral_map hXm.aemeasurable (g.continuous.comp (hstopc.prodMk hshc)).aestronglyMeasurable
  have hFc : Continuous fun x : ContinuousPath ℂ =>
      ∫ w, g (LatticeProb.stopPath x u, w) ∂(K (x u) : Measure (ContinuousPath ℂ)) := by
    have hμ : Continuous fun x : ContinuousPath ℂ => K (x u) := hKc.comp (continuous_eval_const u)
    exact LatticeProb.continuous_integral_of_continuous_measure (μ := fun x : ContinuousPath ℂ => K (x u)) hμ
      (G := fun p : ContinuousPath ℂ × ContinuousPath ℂ => g (LatticeProb.stopPath p.2 u, p.1))
      (g.continuous.comp ((hstopc.comp continuous_snd).prodMk continuous_fst)) (C := ‖g‖)
      fun p => g.norm_coe_le_norm _
  have hR : ∫ x, ∫ w, g (LatticeProb.stopPath x u, w) ∂(K (x u) : Measure (ContinuousPath ℂ))
        ∂(K z : Measure (ContinuousPath ℂ)) =
      ∫ b, ∫ w, g (LatticeProb.stopPath (lqgTimeChange G b) u, w)
        ∂(K (lqgTimeChange G b u) : Measure (ContinuousPath ℂ)) ∂planarLaw z := by
    rw [hK z]
    exact integral_map hXm.aemeasurable hFc.aestronglyMeasurable
  have hinner : ∀ (y : ℂ) (p : ContinuousPath ℂ), ∫ w, g (p, w) ∂(K y : Measure (ContinuousPath ℂ)) =
      ∫ w', g (p, lqgTimeChange G w') ∂planarLaw y := fun y p => by
    rw [hK y]
    exact integral_map hXm.aemeasurable
      (g.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [hL, hR]
  calc ∫ b, g (LatticeProb.stopPath (lqgTimeChange G b) u, LatticeProb.pathShift (lqgTimeChange G b) u)
        ∂planarLaw z
      = ∫ b, g (ratExtend (pastVariable G u b), lqgTimeChange G
          (ContinuousPath.shift ((rcInv G u b).untopD 0) b)) ∂planarLaw z := by
        refine integral_congr_ae ?_
        filter_upwards [ae_lqgTimeChange_shift hA hG z u, ae_ratExtend_pastVariable hA hG z u,
          ae_rcInv_eq hA hG z] with b hsh hst hrc
        rw [hrc u, WithTop.untopD_coe, hsh, hst]
    _ = ∫ b, ∫ w', g (ratExtend (pastVariable G u b), lqgTimeChange G w')
          ∂planarLaw (b ((rcInv G u b).untopD 0)) ∂planarLaw z := key
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [ae_exists_path_lqgTimeChange hA hG z, ae_ratExtend_pastVariable hA hG z u,
          ae_rcInv_eq hA hG z] with b hb hst hrc
        obtain ⟨x, hx, hxb⟩ := hb
        have hXu : lqgTimeChange G b u = b ((rcInv G u b).untopD 0) := by
          rw [hxb, hx, hrc u, WithTop.untopD_coe]
        rw [hinner, hXu, hst]

end MatedCRT
