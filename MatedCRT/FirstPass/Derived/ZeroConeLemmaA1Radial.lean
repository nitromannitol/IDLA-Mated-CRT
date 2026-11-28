import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterNull
import LatticeProb.Prob.BrownianTailZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TransienceCanon

/-!
# The outer radial process of a cone has a trivial tail

For `v > 0` and a path `b'` let `c(u) = b'_u + v u` and let `ℓ` be the last zero of `c`. The outer
radial process of the cone is `coneOuterProc v b' : s ↦ c(ℓ + s)`
(`coneRadial γ α b b' (-s) = coneOuterProc (Q - α) b' s - Q s` for `s > 0`). Two statements:

* `coneOuterProc_absolutelyContinuous`: for a Brownian motion `B'` the law of
  `(coneOuterProc v B' s)_{s ≥ 1}` on `Set.Ici 1 → ℝ` is absolutely continuous with respect to the
  law of the drifted Brownian motion `(B₀'_s + v s)_{s ≥ 1}`.
* `isTrivialSigma_tailFar_coneOuterProc`: the large-time tail σ-algebra of `coneOuterProc v B'` is
  trivial, because the tail of the drifted Brownian motion is trivial
  (`LatticeProb.isTrivialSigma_tailFar_drift`) and a tail event of the outer process is the preimage
  of one fixed tail event of path space (`isTrivialSigma_tailFar_of_map_absolutelyContinuous`).

Proof of the first statement (a Markov argument at a fixed time, as in
`ConeAnnulusAreaLawEquivalenceOuterMarkov.lean`, but with the window `[ℓ + 1, ∞)`). Almost surely
`ℓ ∈ (q - 1, q]` for a unique integer `q ≥ 1` (or `ℓ = 0`, where the outer process is the drifted
path itself). On `{ℓ ∈ (q - 1, q]}` the last zero is a functional `m` of the path stopped at `q`
(`pathLastZero_stop_of_ne`), and `(coneOuterProc v B' s)_{s ≥ 1}` is a functional of the stopped
path and of the increments after `q` (`tailTheta`). The increments are independent of the
stopped path with the law of Brownian motion (`LatticeProb.map_pair_restart_path`), so it suffices
that, for each fixed stopped path, the set of increments `r` with
`(κ + r(τ + s - 1) + v s)_{s ≥ 1} ∈ A` is null whenever `(r_s + v s)_{s ≥ 1} ∈ A` is null
(`measure_wiener_shift_eq_zero`). This is the Markov property at the times `τ` and `1`: the values
at these times are Gaussian with variances `τ` and `1`, hence mutually absolutely continuous, and
the increments after them are the same Brownian motion.

Source: Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*
(arXiv:1409.7055), Remark 4.4 and Definition 4.10; Gwynne–Miller–Sheffield (arXiv:1705.11161),
Appendix A; the weak Markov property of Brownian motion at a fixed time (for example Le Gall,
*Brownian Motion, Martingales, and Stochastic Calculus*, GTM 274, Chapter 2).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

open LatticeProb

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT in
/-- The radial process of a cone outside the unit circle: `s ↦ c(ℓ + s)` with
`c(u) = b'_u + v u` and `ℓ` the last zero of `c`
(`coneRadial γ α b b' (-s) = coneOuterProc (Q - α) b' s - Q s` for `s > 0`). -/
noncomputable def coneOuterProc (v : ℝ) (b' : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun s => (fun c : ℝ → ℝ => c (lastZeroR c + s)) (fun u => b' u.toNNReal + v * u)

/-- The path after the last zero of a path `x`: `s ↦ x (ℓ + s)`. -/
noncomputable def outerProcOfPath (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun s => x ((pathLastZero x + (s : ℝ)).toNNReal)

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT in
/-- The outer process of the cone is the path after the last zero of the drifted path. -/
theorem coneOuterProc_eq (v : ℝ) (b' : ℝ≥0 → ℝ) :
    coneOuterProc v b' = outerProcOfPath fun t => b' t + v * t := by
  have hz : lastZeroR (fun u : ℝ => b' u.toNNReal + v * u) =
      pathLastZero (fun t => b' t + v * t) := by
    unfold lastZeroR pathLastZero
    congr 1
    ext s
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hs => ?_
    rw [Real.coe_toNNReal _ hs]
  funext s
  have hnn : 0 ≤ pathLastZero (fun t => b' t + v * t) + (s : ℝ) :=
    add_nonneg (pathLastZero_nonneg _) (NNReal.coe_nonneg s)
  simp only [coneOuterProc, outerProcOfPath]
  rw [hz, Real.coe_toNNReal _ hnn]

theorem measurable_outerProcOfPath :
    Measurable fun x : C(ℝ≥0, ℝ) => outerProcOfPath fun t => x t := by
  refine measurable_pi_iff.2 fun s => ?_
  have hev : Measurable fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2 := continuous_eval.measurable
  have hτ : Measurable fun x : C(ℝ≥0, ℝ) => (pathLastZero (fun t => x t) + (s : ℝ)).toNNReal :=
    measurable_real_toNNReal.comp (measurable_pathLastZero.add_const _)
  exact hev.comp (measurable_id.prodMk hτ)

/-- If a path does not vanish from time `N` on, stopping it at `N` does not change its last zero. -/
theorem pathLastZero_stop_of_ne {x : ℝ≥0 → ℝ} {N : ℝ≥0} (hne : ∀ s : ℝ≥0, N ≤ s → x s ≠ 0) :
    pathLastZero (fun t => x (min t N)) = pathLastZero x := by
  unfold pathLastZero MatedCRTHarmonic.MatedCRT.lastZeroR
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  by_cases hsN : s.toNNReal ≤ N
  · rw [min_eq_left hsN]
  · have hlt : N ≤ s.toNNReal := (not_le.1 hsN).le
    constructor
    · intro h
      rw [min_eq_right hlt] at h
      exact absurd h (hne N le_rfl)
    · intro h
      exact absurd h (hne _ hlt)

/-- The path `s ↦ κ + r (τ + (s - 1)) + v s` on `[1, ∞)`. -/
def shiftTail (v κ : ℝ) (τ : ℝ≥0) (r : C(ℝ≥0, ℝ)) : Set.Ici (1 : ℝ≥0) → ℝ :=
  fun s => κ + r (τ + ((s : ℝ≥0) - 1)) + v * ((s : ℝ≥0) : ℝ)

theorem measurable_shiftTail (v κ : ℝ) (τ : ℝ≥0) : Measurable (shiftTail v κ τ) := by
  refine measurable_pi_iff.2 fun s => ?_
  exact (((continuous_eval_const (τ + ((s : ℝ≥0) - 1))).measurable).const_add κ).add_const _

theorem shiftTail_zero_one (v : ℝ) (r : C(ℝ≥0, ℝ)) :
    shiftTail v 0 1 r = fun s : Set.Ici (1 : ℝ≥0) => r s + v * ((s : ℝ≥0) : ℝ) := by
  funext s
  have hs : (1 : ℝ≥0) + ((s : ℝ≥0) - 1) = s := add_tsub_cancel_of_le s.2
  simp only [shiftTail, hs, zero_add]

/-- **The Markov property at a fixed time.** A functional `g` of the path stopped at `t` is
independent of the increments after `t`, which have the law of the Brownian path. -/
theorem map_pair_restart_stop {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) (t : ℝ≥0)
    {α : Type*} [MeasurableSpace α] {g : C(ℝ≥0, ℝ) → α} (hg : Measurable g) :
    P.map (fun ω => (g (stopAt (t : ℝ≥0∞) (pathMap b hc ω)), restartAt t (pathMap b hc ω))) =
      (P.map fun ω => g (stopAt (t : ℝ≥0∞) (pathMap b hc ω))).prod (P.map (pathMap b hc)) := by
  let 𝔽 := natFiltration (liftOne b) (stronglyMeasurable_liftOne hm)
  have hσ : IsStoppingTime 𝔽 fun _ : Ω => (((t : ℝ≥0) : ℝ≥0∞)) := isStoppingTime_const 𝔽 t
  have hY : Measurable[hσ.measurableSpace] fun ω => g (stopAt (t : ℝ≥0∞) (pathMap b hc ω)) :=
    hg.comp (measurable_stopAt_pathMap (stronglyAdapted_natFiltration_real hm) hc hσ)
  have h := map_pair_restart_path hb hm hc (σ := fun _ => t) hσ hY (E := Set.univ)
    MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

/-- The Markov property at a fixed time, for the value `b t + κ`, which is Gaussian. -/
theorem map_pair_restart_eval {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) (t : ℝ≥0) (κ : ℝ) :
    P.map (fun ω => (b t ω + κ, restartAt t (pathMap b hc ω))) =
      (gaussianReal κ t).prod (P.map (pathMap b hc)) := by
  have hg : Measurable fun w : C(ℝ≥0, ℝ) => w t + κ :=
    ((continuous_eval_const t).measurable).add_const κ
  have h := map_pair_restart_stop hb hm hc t hg
  have e : ∀ ω, (fun w : C(ℝ≥0, ℝ) => w t + κ) (stopAt (t : ℝ≥0∞) (pathMap b hc ω)) =
      b t ω + κ := fun ω => by
    show stopAt (t : ℝ≥0∞) (pathMap b hc ω) t + κ = b t ω + κ
    rw [stopAt_coe, min_self]
    rfl
  have hlaw : P.map (fun ω => b t ω + κ) = gaussianReal κ t := by
    have h1 := (hb.toIsPreBrownianReal.hasLaw_eval t).map_eq
    have h2 : (fun ω => b t ω + κ) = (fun x : ℝ => x + κ) ∘ b t := rfl
    rw [h2, ← Measure.map_map (measurable_add_const κ) (hm t), h1, gaussianReal_map_add_const,
      zero_add]
  simp only [e] at h
  rwa [hlaw] at h

/-- The map `(ξ, ρ) ↦ (s ↦ ξ + ρ (s - 1) + v s)` from a starting value and increments to the
path on `[1, ∞)`. -/
theorem measurable_tailOfIncrements (v : ℝ) :
    Measurable fun p : ℝ × C(ℝ≥0, ℝ) =>
      fun s : Set.Ici (1 : ℝ≥0) => p.1 + p.2 ((s : ℝ≥0) - 1) + v * ((s : ℝ≥0) : ℝ) := by
  refine measurable_pi_iff.2 fun s => ?_
  have h1 : Measurable fun p : ℝ × C(ℝ≥0, ℝ) => p.2 ((s : ℝ≥0) - 1) :=
    (continuous_eval_const _).measurable.comp measurable_snd
  exact (measurable_fst.add h1).add_const _

/-- **Equivalence of the tails at different starting times (Markov property and Gaussian laws).** If
the path of a Brownian motion read as `(r_s + v s)_{s ≥ 1}` lies in `A` with probability zero, then
so does the path `(κ + r_{τ + s - 1} + v s)_{s ≥ 1}`, for every `κ` and `τ ≠ 0`. -/
theorem measure_wiener_shift_eq_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) (v : ℝ)
    {A : Set (Set.Ici (1 : ℝ≥0) → ℝ)} (hA : MeasurableSet A)
    (h0 : P.map (pathMap b hc) {r | shiftTail v 0 1 r ∈ A} = 0) (κ : ℝ) {τ : ℝ≥0}
    (hτ : τ ≠ 0) : P.map (pathMap b hc) {r | shiftTail v κ τ r ∈ A} = 0 := by
  have hpm : Measurable (pathMap b hc) := measurable_pathMap b hm hc
  set μ := P.map (pathMap b hc) with hμ
  set Λ : ℝ × C(ℝ≥0, ℝ) → (Set.Ici (1 : ℝ≥0) → ℝ) := fun p s =>
    p.1 + p.2 ((s : ℝ≥0) - 1) + v * ((s : ℝ≥0) : ℝ) with hΛdef
  have hM : MeasurableSet (Λ ⁻¹' A) := measurable_tailOfIncrements v hA
  have hpair : ∀ (t : ℝ≥0) (κ' : ℝ), Measurable fun ω =>
      (b t ω + κ', restartAt t (pathMap b hc ω)) := fun t κ' =>
    ((hm t).add_const κ').prodMk
      (measurable_restartAt_pathMap hm hc (σ := fun _ => t) measurable_const)
  have key : ∀ (t : ℝ≥0) (κ' : ℝ), μ {r | shiftTail v κ' t r ∈ A} =
      ((gaussianReal κ' t).prod μ) (Λ ⁻¹' A) := by
    intro t κ'
    have hSet : MeasurableSet {r : C(ℝ≥0, ℝ) | shiftTail v κ' t r ∈ A} :=
      (measurable_shiftTail v κ' t) hA
    rw [← map_pair_restart_eval hb hm hc t κ', Measure.map_apply (hpair t κ') hM,
      hμ, Measure.map_apply hpm hSet]
    congr 1
    ext ω
    show shiftTail v κ' t (pathMap b hc ω) ∈ A ↔ _
    have : shiftTail v κ' t (pathMap b hc ω) =
        Λ (b t ω + κ', restartAt t (pathMap b hc ω)) := by
      funext s
      show κ' + b (t + ((s : ℝ≥0) - 1)) ω + v * ((s : ℝ≥0) : ℝ) =
        b t ω + κ' + (b (t + ((s : ℝ≥0) - 1)) ω - b t ω) + v * ((s : ℝ≥0) : ℝ)
      ring
    rw [this]
    rfl
  have hone := key 1 0
  have hac : (gaussianReal κ τ).prod μ ≪ (gaussianReal 0 1).prod μ :=
    Measure.AbsolutelyContinuous.prod
      ((gaussianReal_absolutelyContinuous κ hτ).trans
        (gaussianReal_absolutelyContinuous' 0 one_ne_zero))
      Measure.AbsolutelyContinuous.rfl
  rw [key τ κ]
  refine hac ?_
  rw [← hone]
  exact h0

/-- The last zero of the path `y` drifted by `v` and stopped at `q`. -/
noncomputable def lastZeroStop (v : ℝ) (q : ℝ≥0) (y : C(ℝ≥0, ℝ)) : ℝ :=
  pathLastZero fun t => driftStop v q y t

theorem measurable_lastZeroStop (v : ℝ) (q : ℝ≥0) : Measurable (lastZeroStop v q) :=
  measurable_pathLastZero.comp (measurable_driftStop v q)

/-- The path on `[1, ∞)` after the last zero of the drifted path, read from the path `p.1` stopped
at `q` and the increments `p.2` after `q`, when the last zero lies in `(q - 1, q]`. -/
noncomputable def tailTheta (v : ℝ) (q : ℝ≥0) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :
    Set.Ici (1 : ℝ≥0) → ℝ := fun s =>
  p.1 q + p.2 ((lastZeroStop v q p.1 + 1 - q).toNNReal + ((s : ℝ≥0) - 1)) +
    v * (lastZeroStop v q p.1 + ((s : ℝ≥0) : ℝ))

/-- The event that the last zero lies in `(q - 1, q]` and the outer path lies in `A`, as a set of
pairs (stopped path, increments after `q`). -/
def stopTailSet (v : ℝ) (q : ℝ≥0) (A : Set (Set.Ici (1 : ℝ≥0) → ℝ)) :
    Set (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :=
  {p | lastZeroStop v q p.1 ∈ Set.Ioc ((q : ℝ) - 1) q ∧ tailTheta v q p ∈ A}

theorem measurableSet_stopTailSet (v : ℝ) (q : ℝ≥0) {A : Set (Set.Ici (1 : ℝ≥0) → ℝ)}
    (hA : MeasurableSet A) : MeasurableSet (stopTailSet v q A) := by
  have hmq : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => lastZeroStop v q p.1 :=
    (measurable_lastZeroStop v q).comp measurable_fst
  have hθ : Measurable (tailTheta v q) := by
    refine measurable_pi_iff.2 fun s => ?_
    have hev : Measurable fun z : C(ℝ≥0, ℝ) × ℝ≥0 => z.1 z.2 := continuous_eval.measurable
    have h1 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => p.1 q :=
      (continuous_eval_const q).measurable.comp measurable_fst
    have harg : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        (lastZeroStop v q p.1 + 1 - q).toNNReal + ((s : ℝ≥0) - 1) :=
      (measurable_real_toNNReal.comp ((hmq.add_const 1).sub_const (q : ℝ))).add_const _
    have h2 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        p.2 ((lastZeroStop v q p.1 + 1 - q).toNNReal + ((s : ℝ≥0) - 1)) :=
      hev.comp (measurable_snd.prodMk harg)
    exact (h1.add h2).add ((hmq.add_const _).const_mul v)
  exact (hmq measurableSet_Ioc).inter (hθ hA)

/-- The last zero of a drifted path stopped at `q` is the last zero of the drifted path, when the
path has a good drift, does not vanish at `q` and its last zero is at most `q`. -/
theorem lastZeroStop_stopAt {v : ℝ} {w : C(ℝ≥0, ℝ)} {q : ℝ≥0}
    (hgd : MatedCRTHarmonic.CellScaling.GoodDrift
      (fun u : ℝ => w u.toNNReal + v * (u.toNNReal : ℝ)) v)
    (hq : driftMap v w q ≠ 0) (hℓ : pathLastZero (fun t => driftMap v w t) ≤ q) :
    lastZeroStop v q (stopAt (q : ℝ≥0∞) w) = pathLastZero fun t => driftMap v w t := by
  have hne : ∀ s : ℝ≥0, q ≤ s → driftMap v w s ≠ 0 := by
    intro s hs
    rcases hs.eq_or_lt with h | h
    · rw [← h]
      exact hq
    · have hlt : MatedCRTHarmonic.CellScaling.lastZeroR
          (fun u : ℝ => w u.toNNReal + v * (u.toNNReal : ℝ)) < (s : ℝ) := by
        change pathLastZero (fun t => driftMap v w t) < s
        exact lt_of_le_of_lt hℓ (by exact_mod_cast h)
      have := hgd.pos_of_lastZeroR_lt hlt
      simpa using this.ne'
  have e : (fun t => driftStop v q (stopAt (q : ℝ≥0∞) w) t) =
      fun t => driftMap v w (min t q) := by
    funext t
    have := congrArg (fun z : C(ℝ≥0, ℝ) => z t) (stopAt_driftMap v q w)
    simp only [stopAt_coe] at this
    exact this.symm
  unfold lastZeroStop
  rw [e]
  exact pathLastZero_stop_of_ne hne

/-- The outer path of the drifted path is `tailTheta` of the stopped path and the increments after
`q`, when the last zero lies in `(q - 1, q]`. -/
theorem tailTheta_stopAt {v : ℝ} {w : C(ℝ≥0, ℝ)} {q : ℝ≥0}
    (hℓ : lastZeroStop v q (stopAt (q : ℝ≥0∞) w) = pathLastZero fun t => driftMap v w t)
    (hI : pathLastZero (fun t => driftMap v w t) ∈ Set.Ioc ((q : ℝ) - 1) q) :
    tailTheta v q (stopAt (q : ℝ≥0∞) w, restartAt q w) =
      fun s : Set.Ici (1 : ℝ≥0) => outerProcOfPath (fun t => driftMap v w t) s := by
  funext s
  set ℓ := pathLastZero fun t => driftMap v w t with hℓdef
  have h1 : 0 ≤ ℓ + 1 - q := by linarith [hI.1]
  have h2 : (1 : ℝ) ≤ ((s : ℝ≥0) : ℝ) := by exact_mod_cast s.2
  have h3 : 0 ≤ ℓ + ((s : ℝ≥0) : ℝ) := by linarith [pathLastZero_nonneg (fun t => driftMap v w t)]
  have e : q + ((ℓ + 1 - q).toNNReal + ((s : ℝ≥0) - 1)) = (ℓ + ((s : ℝ≥0) : ℝ)).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ h1, NNReal.coe_sub s.2,
      Real.coe_toNNReal _ h3]
    simp only [NNReal.coe_one]
    ring
  simp only [tailTheta]
  rw [hℓ]
  show (stopAt (q : ℝ≥0∞) w) q + (w (q + ((ℓ + 1 - q).toNNReal + ((s : ℝ≥0) - 1))) - w q) +
      v * (ℓ + ((s : ℝ≥0) : ℝ)) = _
  rw [e, stopAt_coe, min_self]
  unfold outerProcOfPath
  rw [← hℓdef]
  simp only [driftMap_apply, Real.coe_toNNReal _ h3]
  ring

/-- **The Markov step at the fixed time `q`.** Let `Y` be the Brownian path stopped at `q` and `R`
its increments after `q`. If the path `(b_s + v s)_{s ≥ 1}` lies in `A` with probability zero, then
`(Y, R)` lies in `stopTailSet v q A` with probability zero. -/
theorem measure_stopTailSet_eq_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) (v : ℝ)
    {A : Set (Set.Ici (1 : ℝ≥0) → ℝ)} (hA : MeasurableSet A)
    (h0 : P.map (pathMap b hc) {r | shiftTail v 0 1 r ∈ A} = 0) (q : ℝ≥0) :
    P {ω | (stopAt (q : ℝ≥0∞) (pathMap b hc ω), restartAt q (pathMap b hc ω)) ∈
      stopTailSet v q A} = 0 := by
  set μ := P.map (pathMap b hc) with hμ
  have hYm := measurable_stopAt_pathMap_const hm hc q
  have hRm : Measurable fun ω => restartAt q (pathMap b hc ω) :=
    measurable_restartAt_pathMap hm hc (σ := fun _ => q) measurable_const
  have hSm := measurableSet_stopTailSet v q hA
  have hpair := map_pair_restart_stop hb hm hc q (g := fun w => w) measurable_id
  change P ((fun ω => (stopAt (q : ℝ≥0∞) (pathMap b hc ω), restartAt q (pathMap b hc ω))) ⁻¹'
    stopTailSet v q A) = 0
  rw [← Measure.map_apply (hYm.prodMk hRm) hSm, hpair, Measure.prod_apply hSm]
  have hfib : ∀ y : C(ℝ≥0, ℝ), μ (Prod.mk y ⁻¹' stopTailSet v q A) = 0 := by
    intro y
    by_cases hy : lastZeroStop v q y ∈ Set.Ioc ((q : ℝ) - 1) q
    · have hτ : (lastZeroStop v q y + 1 - q).toNNReal ≠ 0 :=
        (Real.toNNReal_pos.2 (by linarith [hy.1])).ne'
      have hset : Prod.mk y ⁻¹' stopTailSet v q A =
          {r | shiftTail v (y q + v * lastZeroStop v q y)
            (lastZeroStop v q y + 1 - q).toNNReal r ∈ A} := by
        ext r
        have : tailTheta v q (y, r) = shiftTail v (y q + v * lastZeroStop v q y)
            (lastZeroStop v q y + 1 - q).toNNReal r := by
          funext s
          simp only [tailTheta, shiftTail]
          ring
        simp only [Set.mem_preimage, stopTailSet, Set.mem_ofPred_eq]
        rw [this]
        exact and_iff_right hy
      rw [hset]
      exact measure_wiener_shift_eq_zero hb hm hc v hA h0 _ hτ
    · have : Prod.mk y ⁻¹' stopTailSet v q A = ∅ := by
        ext r
        simp only [Set.mem_preimage, stopTailSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        exact fun h => hy h.1
      rw [this]
      exact measure_empty
  exact (lintegral_congr hfib).trans lintegral_zero

/-- **The outer process after the last zero is null when the drifted path is.** For a Brownian
motion `b` with continuous paths and a drift `v > 0`, if `(b_s + v s)_{s ≥ 1}` lies in `A` with
probability zero, then so does `(coneOuterProc v b s)_{s ≥ 1}`. -/
theorem measure_coneOuterProc_eq_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) {v : ℝ} (hv : 0 < v)
    {A : Set (Set.Ici (1 : ℝ≥0) → ℝ)} (hA : MeasurableSet A)
    (h0 : P {ω | (fun s : Set.Ici (1 : ℝ≥0) => b s ω + v * ((s : ℝ≥0) : ℝ)) ∈ A} = 0) :
    P {ω | (fun s : Set.Ici (1 : ℝ≥0) => coneOuterProc v (fun t => b t ω) s) ∈ A} = 0 := by
  have hpm : Measurable (pathMap b hc) := measurable_pathMap b hm hc
  have hμ0 : P.map (pathMap b hc) {r | shiftTail v 0 1 r ∈ A} = 0 := by
    have hSet : MeasurableSet {r : C(ℝ≥0, ℝ) | shiftTail v 0 1 r ∈ A} :=
      (measurable_shiftTail v 0 1) hA
    rw [Measure.map_apply hpm hSet]
    have e : pathMap b hc ⁻¹' {r | shiftTail v 0 1 r ∈ A} =
        {ω | (fun s : Set.Ici (1 : ℝ≥0) => b s ω + v * ((s : ℝ≥0) : ℝ)) ∈ A} := by
      ext ω
      show shiftTail v 0 1 (pathMap b hc ω) ∈ A ↔ _
      rw [shiftTail_zero_one]
      rfl
    rw [e]
    exact h0
  have hgood := ae_goodDrift_path hb hv
  have hne : ∀ᵐ ω ∂P, ∀ k : ℕ, (k : ℝ≥0) ≠ 0 → driftMap v (pathMap b hc ω) (k : ℝ≥0) ≠ 0 := by
    rw [ae_all_iff]
    intro k
    by_cases hk : (k : ℝ≥0) = 0
    · exact ae_of_all _ fun ω h => absurd hk h
    · have hlaw := (hb.toIsPreBrownianReal.hasLaw_eval (k : ℝ≥0)).map_eq
      have hz : P {ω | b (k : ℝ≥0) ω = -(v * ((k : ℝ≥0) : ℝ))} = 0 := by
        have h1 : P (b (k : ℝ≥0) ⁻¹' {-(v * ((k : ℝ≥0) : ℝ))}) =
            (P.map (b (k : ℝ≥0))) {-(v * ((k : ℝ≥0) : ℝ))} :=
          (Measure.map_apply (hm _) (measurableSet_singleton _)).symm
        rw [show {ω | b (k : ℝ≥0) ω = -(v * ((k : ℝ≥0) : ℝ))} =
          b (k : ℝ≥0) ⁻¹' {-(v * ((k : ℝ≥0) : ℝ))} from rfl, h1, hlaw]
        exact gaussianReal_absolutelyContinuous 0 hk (Real.volume_singleton)
      refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) hz)
      simp only [Set.mem_ofPred_eq, not_imp, not_not] at hω
      have h2 : b (k : ℝ≥0) ω + v * ((k : ℝ≥0) : ℝ) = 0 := hω.2
      show b (k : ℝ≥0) ω = -(v * ((k : ℝ≥0) : ℝ))
      linarith
  have hnull : P (({ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
      (fun u : ℝ => b u.toNNReal ω + v * (u.toNNReal : ℝ)) v} ∪
      {ω | ¬ ∀ k : ℕ, (k : ℝ≥0) ≠ 0 → driftMap v (pathMap b hc ω) (k : ℝ≥0) ≠ 0}) ∪
      ({ω | (fun s : Set.Ici (1 : ℝ≥0) => b s ω + v * ((s : ℝ≥0) : ℝ)) ∈ A} ∪
      ⋃ k : ℕ, {ω | (k : ℝ≥0) ≠ 0 ∧ (stopAt ((k : ℝ≥0) : ℝ≥0∞) (pathMap b hc ω),
        restartAt (k : ℝ≥0) (pathMap b hc ω)) ∈ stopTailSet v (k : ℝ≥0) A})) = 0 := by
    refine measure_union_null (measure_union_null (ae_iff.1 hgood) (ae_iff.1 hne))
      (measure_union_null h0 (measure_iUnion_null fun k => ?_))
    by_cases hk : (k : ℝ≥0) = 0
    · exact measure_mono_null (fun ω hω => absurd hk hω.1) measure_empty
    · exact measure_mono_null (fun ω hω => hω.2)
        (measure_stopTailSet_eq_zero hb hm hc v hA hμ0 (k : ℝ≥0))
  refine measure_mono_null (fun ω hω => ?_) hnull
  by_contra hcon
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_not, not_exists,
    not_and] at hcon
  obtain ⟨⟨hgd, hnz⟩, hN3, hN4⟩ := hcon
  have hω' : (fun s : Set.Ici (1 : ℝ≥0) =>
      outerProcOfPath (fun t => driftMap v (pathMap b hc ω) t) s) ∈ A := by
    have e : (fun s : Set.Ici (1 : ℝ≥0) => coneOuterProc v (fun t => b t ω) s) =
        fun s : Set.Ici (1 : ℝ≥0) =>
          outerProcOfPath (fun t => driftMap v (pathMap b hc ω) t) s := by
      funext s
      rw [coneOuterProc_eq]
      rfl
    rw [← e]
    exact hω
  set w := pathMap b hc ω with hw
  set ℓ := pathLastZero (fun t => driftMap v w t) with hℓ
  have hℓ0 : 0 ≤ ℓ := pathLastZero_nonneg _
  rcases hℓ0.eq_or_lt with h | h
  · refine hN3 ?_
    have e : (fun s : Set.Ici (1 : ℝ≥0) => b s ω + v * ((s : ℝ≥0) : ℝ)) =
        fun s : Set.Ici (1 : ℝ≥0) => outerProcOfPath (fun t => driftMap v w t) s := by
      funext s
      unfold outerProcOfPath
      rw [← hℓ, ← h, zero_add, Real.toNNReal_coe]
      rfl
    rw [e]
    exact hω'
  · set k : ℕ := ⌈ℓ⌉₊ with hk
    have hk0 : (k : ℝ≥0) ≠ 0 := by
      have : 0 < k := Nat.ceil_pos.2 h
      exact_mod_cast this.ne'
    have hkℓ : ℓ ≤ ((k : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_natCast]
      exact Nat.le_ceil ℓ
    have hkℓ' : ((k : ℝ≥0) : ℝ) - 1 < ℓ := by
      rw [NNReal.coe_natCast]
      linarith [Nat.ceil_lt_add_one hℓ0]
    have hz := lastZeroStop_stopAt hgd (hnz k hk0) hkℓ
    exact hN4 k hk0 ⟨by rw [hz]; exact ⟨hkℓ', hkℓ⟩, by
      rw [tailTheta_stopAt hz ⟨hkℓ', hkℓ⟩]; exact hω'⟩

/-- **Tail triviality transfers along absolute continuity of the law on `[1, ∞)`.** Let `Y'` be a
measurable version of `Y` (almost surely equal as a whole path), and `Z` a process with measurable
coordinates and trivial tail. If the law of `(Y'_s)_{s ≥ 1}` is absolutely continuous with respect
to the law of `(Z_s)_{s ≥ 1}`, then the tail σ-algebra of `Y` is trivial. A tail event of `Y` is the
preimage of the `limsup` of cylinder sets over `[n, ∞)`, a tail event of path space. -/
theorem isTrivialSigma_tailFar_of_map_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y Y' Z : ℝ≥0 → Ω → ℝ}
    (hY'm : ∀ t, Measurable (Y' t)) (hZm : ∀ t, Measurable (Z t))
    (hae : ∀ᵐ ω ∂P, ∀ t, Y t ω = Y' t ω)
    (hac : P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => Y' s ω) ≪
      P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω))
    (hZ : IsTrivialSigma (tailFar Z) P) : IsTrivialSigma (tailFar Y) P := by
  intro E hE
  have hEn : ∀ n : ℕ, ∃ G : Set (Set.Ici ((n : ℝ≥0) + 1) → ℝ), MeasurableSet G ∧
      (fun ω (u : Set.Ici ((n : ℝ≥0) + 1)) => Y u ω) ⁻¹' G = E := fun n =>
    MeasurableSpace.measurableSet_comap.1
      (MeasurableSpace.measurableSet_iInf.1 hE ((n : ℝ≥0) + 1))
  choose G hG hGE using hEn
  let r : ∀ n : ℕ, (Set.Ici (1 : ℝ≥0) → ℝ) → (Set.Ici ((n : ℝ≥0) + 1) → ℝ) :=
    fun n x u => x ⟨u, Set.mem_Ici.2 (le_trans le_add_self (Set.mem_Ici.1 u.2))⟩
  have hr : ∀ n, Measurable (r n) := fun n =>
    measurable_pi_iff.2 fun u => measurable_pi_apply _
  set H : ℕ → Set (Set.Ici (1 : ℝ≥0) → ℝ) := fun n => r n ⁻¹' G n with hH
  have hHm : ∀ n, MeasurableSet (H n) := fun n => hr n (hG n)
  set Hl : Set (Set.Ici (1 : ℝ≥0) → ℝ) := ⋂ N : ℕ, ⋃ n : ℕ, H (n + N) with hHl
  have hHlm : MeasurableSet Hl := MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => hHm _
  have hYn : ∀ (n : ℕ) (ω : Ω), (fun s : Set.Ici (1 : ℝ≥0) => Y s ω) ∈ H n ↔ ω ∈ E :=
    fun n ω => by
      rw [← hGE n]
      exact Iff.rfl
  have hYE : (fun ω (s : Set.Ici (1 : ℝ≥0)) => Y s ω) ⁻¹' Hl = E := by
    ext ω
    constructor
    · intro h
      have h' : (fun s : Set.Ici (1 : ℝ≥0) => Y s ω) ∈ Hl := h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 h' 0)
      exact (hYn (n + 0) ω).1 hn
    · intro h
      exact Set.mem_iInter.2 fun N => Set.mem_iUnion.2 ⟨0, (hYn _ ω).2 h⟩
  have hZ1 : MeasurableSet[tailFar Z] ((fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) ⁻¹' Hl) := by
    refine MeasurableSpace.measurableSet_iInf.2 fun t => ?_
    obtain ⟨K, hK⟩ := exists_nat_ge t
    have hcyl : ∀ m : ℕ, K ≤ m →
        MeasurableSet[MeasurableSpace.comap (fun ω (u : Set.Ici t) => Z u ω) inferInstance]
          ((fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) ⁻¹' H m) := by
      intro m hm
      have ht : t ≤ (m : ℝ≥0) + 1 := hK.trans ((Nat.cast_le.2 hm).trans le_self_add)
      let ρ : (Set.Ici t → ℝ) → (Set.Ici ((m : ℝ≥0) + 1) → ℝ) := fun x u =>
        x ⟨u, Set.mem_Ici.2 (ht.trans (Set.mem_Ici.1 u.2))⟩
      have hρ : Measurable ρ := measurable_pi_iff.2 fun u => measurable_pi_apply _
      exact MeasurableSpace.measurableSet_comap.2 ⟨ρ ⁻¹' G m, hρ (hG m), rfl⟩
    have heq : (fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) ⁻¹' Hl =
        ⋂ N : ℕ, ⋃ n : ℕ, (fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) ⁻¹' H (n + (N + K)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_iUnion, hHl]
      constructor
      · intro h N
        exact h (N + K)
      · intro h N
        obtain ⟨n, hn⟩ := h N
        exact ⟨n + K, by rwa [show n + K + N = n + (N + K) by omega]⟩
    rw [heq]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => hcyl _ (by omega)
  have hY'meas : Measurable fun ω (s : Set.Ici (1 : ℝ≥0)) => Y' s ω :=
    measurable_pi_iff.2 fun s => hY'm s
  have hZmeas : Measurable fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω :=
    measurable_pi_iff.2 fun s => hZm s
  have : IsProbabilityMeasure (P.map fun ω (s : Set.Ici (1 : ℝ≥0)) => Y' s ω) :=
    (Measure.isProbabilityMeasure_map_iff hY'meas.aemeasurable).2 inferInstance
  have hEeq : P E = (P.map fun ω (s : Set.Ici (1 : ℝ≥0)) => Y' s ω) Hl := by
    rw [Measure.map_apply hY'meas hHlm, ← hYE]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 (hae.mono fun ω h => ?_))
    have e : (fun s : Set.Ici (1 : ℝ≥0) => Y s ω) = fun s : Set.Ici (1 : ℝ≥0) => Y' s ω :=
      funext fun s => h s
    show (fun s : Set.Ici (1 : ℝ≥0) => Y s ω) ∈ Hl ↔ (fun s : Set.Ici (1 : ℝ≥0) => Y' s ω) ∈ Hl
    rw [e]
  have hZeq : P ((fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) ⁻¹' Hl) =
      (P.map fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) Hl :=
    (Measure.map_apply hZmeas hHlm).symm
  rcases hZ _ hZ1 with h | h
  · left
    rw [hEeq]
    exact hac (by rw [← hZeq]; exact h)
  · right
    rw [hEeq]
    have : IsProbabilityMeasure (P.map fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) :=
      (Measure.isProbabilityMeasure_map_iff hZmeas.aemeasurable).2 inferInstance
    have hcz : (P.map fun ω (s : Set.Ici (1 : ℝ≥0)) => Z s ω) Hlᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hHlm, ← hZeq]
      exact h
    exact (prob_compl_eq_zero_iff hHlm).1 (hac hcz)

/-- The map `x ↦ (s ↦ outerProcOfPath (x + v ·) s)` on `[1, ∞)` is measurable. -/
theorem measurable_outerTail (v : ℝ) :
    Measurable fun x : C(ℝ≥0, ℝ) =>
      fun s : Set.Ici (1 : ℝ≥0) => outerProcOfPath (fun t => driftMap v x t) s :=
  measurable_pi_iff.2 fun s => (measurable_pi_apply (s : ℝ≥0)).comp
    (measurable_outerProcOfPath.comp (measurable_driftMap v))

/-- For a Brownian motion `b` with continuous paths, the outer process on `[1, ∞)` is measurable and
its law is absolutely continuous with respect to the law of the drifted Brownian motion. -/
theorem map_coneOuterProc_absolutelyContinuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) {v : ℝ} (hv : 0 < v) :
    Measurable (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => b t ω) s) ∧
      P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => b t ω) s) ≪
        P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => b s ω + v * ((s : ℝ≥0) : ℝ)) := by
  have hpm : Measurable (pathMap b hc) := measurable_pathMap b hm hc
  have hfun : (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => b t ω) s) =
      (fun x : C(ℝ≥0, ℝ) => fun s : Set.Ici (1 : ℝ≥0) =>
        outerProcOfPath (fun t => driftMap v x t) s) ∘ pathMap b hc := by
    funext ω s
    rw [coneOuterProc_eq]
    rfl
  have hmeas :
      Measurable (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => b t ω) s) := by
    rw [hfun]
    exact (measurable_outerTail v).comp hpm
  have hZmeas : Measurable fun ω (s : Set.Ici (1 : ℝ≥0)) => b s ω + v * ((s : ℝ≥0) : ℝ) :=
    measurable_pi_iff.2 fun s => ((hm s).add_const _)
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk fun A hA h2 => ?_⟩
  rw [Measure.map_apply hmeas hA]
  rw [Measure.map_apply hZmeas hA] at h2
  exact measure_coneOuterProc_eq_zero hb hm hc hv hA h2

/-- **The outer radial process of a cone on `[1, ∞)` is absolutely continuous with respect to
drifted Brownian motion.** The path `(coneOuterProc v B' s)_{s ≥ 1}` is almost everywhere
measurable and its law is absolutely continuous with respect to the law of `(B₀'_s + v s)_{s ≥ 1}`
for Brownian motions `B', B₀'` and `v > 0`. -/
theorem coneOuterProc_absolutelyContinuous {v : ℝ} (hv : 0 < v) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B' B₀' : ℝ≥0 → Ω → ℝ) (hB' : IsBrownianReal B' P)
    (hB₀' : IsBrownianReal B₀' P) :
    AEMeasurable (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => B' t ω) s) P ∧
      P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => B' t ω) s) ≪
        P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => B₀' s ω + v * ((s : ℝ≥0) : ℝ)) := by
  obtain ⟨b, hbm, hbc, -, hb, hbB⟩ := QuantumZipper.RS.exists_good_version0 hB'
  obtain ⟨b₀, hb₀m, hb₀c, -, hb₀, hb₀B⟩ := QuantumZipper.RS.exists_good_version0 hB₀'
  obtain ⟨hmeas, hac⟩ := map_coneOuterProc_absolutelyContinuous hb hbm hbc hv
  have haeY : (fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => B' t ω) s) =ᵐ[P]
      fun ω (s : Set.Ici (1 : ℝ≥0)) => coneOuterProc v (fun t => b t ω) s := by
    filter_upwards [hbB] with ω h
    have e : (fun t => B' t ω) = fun t => b t ω := funext fun t => (h t).symm
    funext s
    rw [e]
  have haeZ : (fun ω (s : Set.Ici (1 : ℝ≥0)) => B₀' s ω + v * ((s : ℝ≥0) : ℝ)) =ᵐ[P]
      fun ω (s : Set.Ici (1 : ℝ≥0)) => b₀ s ω + v * ((s : ℝ≥0) : ℝ) := by
    filter_upwards [hb₀B] with ω h
    funext s
    rw [h]
  refine ⟨hmeas.aemeasurable.congr haeY.symm, ?_⟩
  rw [Measure.map_congr haeY, Measure.map_congr haeZ]
  have hpm : Measurable (pathMap b hbc) := measurable_pathMap b hbm hbc
  have hpm₀ : Measurable (pathMap b₀ hb₀c) := measurable_pathMap b₀ hb₀m hb₀c
  have hΨ : Measurable fun x : C(ℝ≥0, ℝ) =>
      fun s : Set.Ici (1 : ℝ≥0) => x s + v * ((s : ℝ≥0) : ℝ) :=
    measurable_pi_iff.2 fun s => ((continuous_eval_const (s : ℝ≥0)).measurable).add_const _
  have hlaw := map_pathMap_eq_of_isBrownianReal hb hbm hbc hb₀ hb₀m hb₀c
  have e : P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => b₀ s ω + v * ((s : ℝ≥0) : ℝ)) =
      P.map (fun ω (s : Set.Ici (1 : ℝ≥0)) => b s ω + v * ((s : ℝ≥0) : ℝ)) := by
    have h1 := Measure.map_map hΨ hpm₀ (μ := P)
    have h2 := Measure.map_map hΨ hpm (μ := P)
    rw [← hlaw] at h1
    exact h1.symm.trans h2
  rw [e]
  exact hac

/-- **The outer radial process of a cone has a trivial tail.** For `v > 0` and a Brownian motion
`B'`, the large-time tail σ-algebra of `s ↦ coneOuterProc v B' s` is trivial. -/
theorem isTrivialSigma_tailFar_coneOuterProc {v : ℝ} (hv : 0 < v) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B' : ℝ≥0 → Ω → ℝ) (hB' : IsBrownianReal B' P) :
    IsTrivialSigma (tailFar fun s ω => coneOuterProc v (fun t => B' t ω) s) P := by
  obtain ⟨b, hbm, hbc, -, hb, hbB⟩ := QuantumZipper.RS.exists_good_version0 hB'
  obtain ⟨-, hac⟩ := map_coneOuterProc_absolutelyContinuous hb hbm hbc hv
  refine isTrivialSigma_tailFar_of_map_absolutelyContinuous
    (Y' := fun s ω => coneOuterProc v (fun t => b t ω) s)
    (Z := fun t ω => 1 * b t ω + v * (t : ℝ)) ?_ (fun t => ?_) ?_ ?_
    (isTrivialSigma_tailFar_drift hb.toIsPreBrownianReal hbm 1 v)
  · intro s
    have hpm : Measurable (pathMap b hbc) := measurable_pathMap b hbm hbc
    have : (fun ω => coneOuterProc v (fun t => b t ω) s) =
        (fun x : C(ℝ≥0, ℝ) => outerProcOfPath (fun t => driftMap v x t) s) ∘ pathMap b hbc := by
      funext ω
      rw [Function.comp_apply, coneOuterProc_eq]
      rfl
    rw [this]
    exact ((measurable_pi_apply s).comp
      (measurable_outerProcOfPath.comp (measurable_driftMap v))).comp hpm
  · exact ((hbm t).const_mul 1).add_const _
  · filter_upwards [hbB] with ω h t
    have e : (fun t => B' t ω) = fun t => b t ω := funext fun t => (h t).symm
    rw [e]
  · simpa only [one_mul] using hac

end MatedCRT
