import MatedCRT.FirstPass.Derived.WalkMarkovStep
import MatedCRT.FirstPass.Derived.InterpolatedWalkPrefix
import LatticeProb.Prob.EnvironmentMarkovShift
import LatticeProb.Prob.MarkovPathKernelAE
import LatticeProb.Prob.CondExpComapMap
import LatticeProb.Prob.ProbabilityMeasureBorel
import LatticeProb.Prob.PathSpaceDUnif

/-!
# The Markov step of the interpolated embedded walk, for a sequence of scales (BG20 Lemma 7.4)

For a valid environment `S`, scales `εₙ`, start vertices `kₙ` and time scalings `mₙ`, the annealed law of
the embedded walk at scale `εₙ` is `S.P ⊗ₘ walkKernel hS εₙ kₙ` on `Ω × (ℕ → ℤ)`.  This file proves the
Markov step of the interpolated walk in the form required by the Markov-step criterion of
Lattice-Probability (`ae_markovAt_of_markov_step_pathShift`): conditional expectation of a bounded
continuous functional of the walk shifted by `jₙ / mₙ` given the environment and the first `jₙ + 1`
steps is the integral against the quenched path law started at the present vertex.

* `MatedCRT.condExp_walkShift_interp`: one scale, on `Ω × (ℕ → ℤ)`.
* `MatedCRT.annealedWalks`: independent product over scales of the annealed laws (a common probability
  space for the sequence; the law of each coordinate is the annealed law at that scale).
* `MatedCRT.condExp_walkShift_interp_pi`: the same identity on the product space for the `n`-th scale.
-/

open MeasureTheory ProbabilityTheory Set Preorder MarkovProcess LatticeProb
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Markov step of the interpolated embedded walk at one scale**, conditional expectation form: for a
bounded continuous functional `f` of paths, the conditional expectation of `f` of the interpolated walk
shifted by `n / m` given the environment and the first `n + 1` steps is `∫ f dQ`, with `Q` the quenched
law of the interpolated walk started at the present vertex. -/
theorem condExp_walkShift_interp {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ} (hm : 0 < m) (ε : ℝ) (k₀ : ℤ)
    (n : ℕ) (f : ContinuousPath ℂ →ᵇ ℝ) :
    (S.P ⊗ₘ walkKernel hS ε k₀)[fun p : Ω × (ℕ → ℤ) =>
        f (pathShift (interpPathCM (v p.1) hm.le p.2) ((n / m : ℝ).toNNReal)) |
      MeasurableSpace.comap (fun p : Ω × (ℕ → ℤ) => (p.1, frestrictLe n p.2)) inferInstance]
      =ᵐ[S.P ⊗ₘ walkKernel hS ε k₀] fun p : Ω × (ℕ → ℤ) =>
        ∫ g, f g ∂(walkPathLaw S v hm.le ε (lastState n (frestrictLe n p.2)) p.1 :
          Measure (ContinuousPath ℂ)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hmain := condExp_comp_eq_integral_kernel (μ := S.P) (walkKernel hS ε k₀)
    (π := frestrictLe n) (measurable_frestrictLe n) (τ := lastState n) (measurable_lastState n)
    (θ := MatedCRTHarmonic.Markov.walkShift n) (MatedCRTHarmonic.Markov.measurable_walkShift n)
    (walkStartKernel hS ε) (F := walkIntegrand v hm.le f)
    (measurable_walkIntegrand hv hm.le f.continuous.measurable) (C := ‖f‖)
    (fun p => by simpa [walkIntegrand, Real.norm_eq_abs] using f.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun ω E hE B hB => walkKernel_markov_step hS ε k₀ n ω hE hB)
  have e1 : (fun p : Ω × (ℕ → ℤ) =>
      f (pathShift (interpPathCM (v p.1) hm.le p.2) ((n / m : ℝ).toNNReal))) =
      fun p : Ω × (ℕ → ℤ) => walkIntegrand v hm.le f (p.1, MatedCRTHarmonic.Markov.walkShift n p.2) :=
    funext fun p => (walkIntegrand_walkShift v hm f p.1 p.2 n).symm
  rw [e1]
  refine hmain.trans (Filter.Eventually.of_forall fun p => ?_)
  exact integral_walkStartKernel hS v hm.le ε p.1 _ f.continuous.measurable


section Annealed

variable {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}

/-- The independent product over the scales `n` of the annealed laws `S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)`:
a common probability space carrying, for every scale, an environment and an embedded walk with the
annealed law of that scale. -/
noncomputable def annealedWalks (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    (k₀ : ℕ → ℤ) : Measure ((_ : ℕ) → Ω × (ℕ → ℤ)) :=
  Measure.infinitePi fun n => S.P ⊗ₘ walkKernel hS (ε n) (k₀ n)

instance (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) (k₀ : ℕ → ℤ) :
    IsProbabilityMeasure (annealedWalks hS ε k₀) := by
  unfold annealedWalks
  infer_instance

/-- The `n`-th coordinate of the product space has the annealed law of the `n`-th scale. -/
theorem annealedWalks_map_eval (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    (k₀ : ℕ → ℤ) (n : ℕ) :
    (annealedWalks hS ε k₀).map (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) =
      S.P ⊗ₘ walkKernel hS (ε n) (k₀ n) :=
  Measure.infinitePi_map_eval _ n

/-- **Markov step of the interpolated embedded walk at the `n`-th scale, on the product space.**  The
conditional expectation of a bounded continuous functional `f` of the `n`-th interpolated walk, shifted by
`jₙ / mₙ`, given the environment and the first `jₙ + 1` steps of the `n`-th walk, is the integral of `f`
against the quenched path law started at the present vertex. -/
theorem condExp_walkShift_interp_pi (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    (k₀ : ℕ → ℤ) {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n) (j : ℕ → ℕ) (n : ℕ) (f : ContinuousPath ℂ →ᵇ ℝ) :
    (annealedWalks hS ε k₀)[fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
        f (pathShift (interpPathCM (v n (p n).1) (hm n).le (p n).2) ((j n / m n : ℝ).toNNReal)) |
      MeasurableSpace.comap
        (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => ((p n).1, frestrictLe (j n) (p n).2)) inferInstance]
      =ᵐ[annealedWalks hS ε k₀] fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
        ∫ g, f g ∂(walkPathLaw S (v n) (hm n).le (ε n)
          (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 : Measure (ContinuousPath ℂ)) := by
  have hπ : Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply n
  have hgm : Measurable fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe (j n) q.2) :=
    measurable_fst.prodMk ((measurable_frestrictLe (j n)).comp measurable_snd)
  have hFeq : (fun q : Ω × (ℕ → ℤ) =>
      f (pathShift (interpPathCM (v n q.1) (hm n).le q.2) ((j n / m n : ℝ).toNNReal))) =
      fun q => walkIntegrand (v n) (hm n).le f
        (q.1, MatedCRTHarmonic.Markov.walkShift (j n) q.2) :=
    funext fun q => (walkIntegrand_walkShift (v n) (hm n) f q.1 q.2 (j n)).symm
  have hFm : Measurable fun q : Ω × (ℕ → ℤ) =>
      f (pathShift (interpPathCM (v n q.1) (hm n).le q.2) ((j n / m n : ℝ).toNNReal)) := by
    rw [hFeq]
    exact (measurable_walkIntegrand (hv n) (hm n).le f.continuous.measurable).comp
      (measurable_fst.prodMk ((MatedCRTHarmonic.Markov.measurable_walkShift (j n)).comp
        measurable_snd))
  have h1 := condExp_comp_comap_ae_eq (μ := annealedWalks hS ε k₀) hπ
    (G := MeasurableSpace.comap (fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe (j n) q.2)) inferInstance)
    hgm.comap_le hFm (C := ‖f‖) (fun q => by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _)
  rw [MeasurableSpace.comap_comp] at h1
  have h2 := condExp_walkShift_interp hS (hv n) (hm n) (ε n) (k₀ n) (j n) f
  rw [← annealedWalks_map_eval hS ε k₀ n] at h2
  exact h1.trans (ae_eq_comp (μ := annealedWalks hS ε k₀) hπ.aemeasurable h2)

/-- The quenched path law started at the present vertex is a measurable function of the environment and
the walk. -/
theorem measurable_walkPathLaw_present (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v)
    {m : ℝ} (hm : 0 ≤ m) (ε : ℝ) (j : ℕ) :
    Measurable fun q : Ω × (ℕ → ℤ) => walkPathLaw S v hm ε (lastState j (frestrictLe j q.2)) q.1 := by
  have h1 : Measurable fun r : Ω × ℤ => walkPathLaw S v hm ε r.2 r.1 :=
    measurable_from_prod_countable_left fun k => measurable_walkPathLaw hS hv hm ε k
  have h2 : Measurable fun q : Ω × (ℕ → ℤ) => (q.1, lastState j (frestrictLe j q.2)) :=
    measurable_fst.prodMk ((measurable_lastState j).comp ((measurable_frestrictLe j).comp measurable_snd))
  exact h1.comp h2

/-- The environment datum and the stopped interpolated walk at time `j / m` generate a σ-algebra
contained in the one generated by the environment and the first `j + 1` steps. -/
theorem comap_pair_stopPath_le {S₀ : Type*} [MeasurableSpace S₀] {d : Ω → S₀} (hd : Measurable d)
    {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ} (hm : 0 < m) (j : ℕ) (n : ℕ) :
    MeasurableSpace.comap (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
        (d (p n).1, stopPath (interpPathCM (v (p n).1) hm.le (p n).2) ((j / m : ℝ).toNNReal)))
      inferInstance ≤
      MeasurableSpace.comap
        (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => ((p n).1, frestrictLe j (p n).2)) inferInstance := by
  have hpair : Measurable[MeasurableSpace.comap
      (fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe j q.2)) inferInstance]
      (fun q : Ω × (ℕ → ℤ) =>
        (d q.1, stopPath (interpPathCM (v q.1) hm.le q.2) ((j / m : ℝ).toNNReal))) :=
    (hd.comp (measurable_fst.comp (comap_measurable _))).prodMk
      (measurable_stopPath_interpPathCM_prefix hv hm j)
  have hle := (measurable_iff_comap_le.1 hpair)
  have e1 : MeasurableSpace.comap (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
        (d (p n).1, stopPath (interpPathCM (v (p n).1) hm.le (p n).2) ((j / m : ℝ).toNNReal)))
      inferInstance = (MeasurableSpace.comap (fun q : Ω × (ℕ → ℤ) =>
        (d q.1, stopPath (interpPathCM (v q.1) hm.le q.2) ((j / m : ℝ).toNNReal)))
        inferInstance).comap (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) :=
    (MeasurableSpace.comap_comp (f := fun q : Ω × (ℕ → ℤ) =>
      (d q.1, stopPath (interpPathCM (v q.1) hm.le q.2) ((j / m : ℝ).toNNReal)))
      (g := fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n)).symm
  have e2 : MeasurableSpace.comap
        (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => ((p n).1, frestrictLe j (p n).2)) inferInstance =
      (MeasurableSpace.comap (fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe j q.2))
        inferInstance).comap (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) :=
    (MeasurableSpace.comap_comp (f := fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe j q.2))
      (g := fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n)).symm
  rw [e1, e2]
  exact MeasurableSpace.comap_mono hle

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **The quenched Markov property of the limit kernel from the Markov step of the embedded walks**
(BG20 Lemma 7.4, Markov part).  Let `(Dₙ, Xₙ)` be the environment datum and the interpolated embedded walk
of the `n`-th scale on the product space `annealedWalks`.  If they converge in law to `ν = νD ⊗ₘ κ₀`, with
`κ₀ d = K d z₀` for a continuous `K : S₀ → C(ℂ, Prob(ℂ-valued paths))`, and the quenched path law started at
the present vertex is close in Lévy–Prokhorov distance to `K (Dₙ) (Xₙ (jₙ / mₙ))` in probability, with
`jₙ / mₙ → t`, then `MarkovAt (K d) z₀ t` holds for `νD`-almost every `d`.  The Markov step of the walk
itself is `condExp_walkShift_interp_pi`; the law convergence and the closeness are the hypotheses. -/
theorem ae_markovAt_of_walk_markov_step
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) (k₀ : ℕ → ℤ)
    {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ} (hm : ∀ n, 0 < m n) (j : ℕ → ℕ)
    {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    {ν : Measure (S₀ × C(ℝ≥0, ℂ))} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ,
      Filter.Tendsto (fun n => ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
          ∂annealedWalks hS ε k₀) Filter.atTop (nhds (∫ q, g q ∂ν)))
    {t T : ℝ≥0}
    (hs : Filter.Tendsto (fun n => ((j n / m n : ℝ).toNNReal)) Filter.atTop (nhds t))
    (hsT : ∀ n, ((j n / m n : ℝ).toNNReal) ≤ T)
    {K : S₀ → C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))} (hK : Continuous K)
    (hclose : TendstoInMeasure (annealedWalks hS ε k₀)
      (fun n (p : (_ : ℕ) → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (v n) (hm n).le (ε n) (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 :
          Measure C(ℝ≥0, ℂ))
        (K (d n (p n).1) (interpPathCM (v n (p n).1) (hm n).le (p n).2 ((j n / m n : ℝ).toNNReal)) :
          Measure C(ℝ≥0, ℂ))) Filter.atTop 0)
    {νD : Measure S₀} [IsProbabilityMeasure νD] {κ₀ : Kernel S₀ C(ℝ≥0, ℂ)} {z₀ : ℂ}
    (hν : ν = νD ⊗ₘ κ₀) (hκ₀ : ∀ d, κ₀ d = (K d z₀ : Measure C(ℝ≥0, ℂ))) :
    ∀ᵐ d ∂νD, MarkovAt (K d) z₀ t := by
  have hev : ∀ n, Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply
  refine ae_markovAt_of_markov_step_pathShift (μ := annealedWalks hS ε k₀)
    (D := fun n p => d n (p n).1)
    (X := fun n p => interpPathCM (v n (p n).1) (hm n).le (p n).2)
    (fun n => (hd n).comp (measurable_fst.comp (hev n)))
    (fun n => (measurable_interpPathCM_uncurry (hm n).le).comp
      (((hv n).comp (measurable_fst.comp (hev n))).prodMk (measurable_snd.comp (hev n))))
    hlaw hs hsT hK
    (G := fun n => MeasurableSpace.comap
      (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => ((p n).1, frestrictLe (j n) (p n).2)) inferInstance)
    (fun n => comap_pair_stopPath_le (hd n) (hv n) (hm n) (j n) n)
    (fun n => ((measurable_fst.comp (hev n)).prodMk
      ((measurable_frestrictLe (j n)).comp (measurable_snd.comp (hev n)))).comap_le)
    (κ := fun n p => walkPathLaw S (v n) (hm n).le (ε n)
      (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1)
    (fun n => ?_)
    (fun n f => condExp_walkShift_interp_pi hS ε k₀ hv hm j n f)
    hclose hν hκ₀
  exact (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp
    ((measurable_walkPathLaw_present hS (hv n) (hm n).le (ε n) (j n)).comp
      ((hev n)))).aemeasurable

end Annealed

end MatedCRT
