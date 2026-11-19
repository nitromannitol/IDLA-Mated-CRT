import MatedCRT.FirstPass.Derived.MarkovStepInstance

/-!
# The Markov step of the interpolated embedded walk started at a random vertex (BG20 Lemma 7.4)

`MarkovStepInstance` treats walks started at a deterministic vertex `kₙ`.  The embedded walk of Theorem 2.11
starts at the vertex of a cell containing a fixed point `z₀ ∈ ℂ`, which depends on the environment, so the Markov
step is needed for a start vertex `kₙ : Ω → ℤ` that is a measurable function of the environment.  The proofs are
those of `MarkovStepInstance`, with the kernel `walkKernel hS ε k` replaced by
`walkKernelAt hS ε hk : ω ↦ srwLaw (S.mult ε ω) (k ω)`.

* `MatedCRT.walkKernelAt`, `MatedCRT.annealedWalksAt`: the annealed law with a random start vertex.
* `MatedCRT.condExp_walkShift_interp_pi_at`: the Markov step on the product space.
* `MatedCRT.ae_markovAt_of_walk_markov_step_at`: the quenched Markov property of the limit kernel
  (Lemma 7.4, Markov part) for walks started at the random vertices `kₙ`.
* `MatedCRT.integral_annealedWalksAt_eq_integral_walkPathLaw`: the kernel representation of the annealed integral.
-/

open MeasureTheory ProbabilityTheory Set Preorder MarkovProcess LatticeProb
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

section RandomStart

variable {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}

/-- The quenched walk law as a kernel in the environment, started at the vertex `k ω`. -/
noncomputable def walkKernelAt (hS : S.IsValid 𝒮 γ) (ε : ℝ) {k : Ω → ℤ} (hk : Measurable k) :
    Kernel Ω (ℕ → ℤ) :=
  (walkStartKernel hS ε).comap (fun ω => (ω, k ω)) (measurable_id.prodMk hk)

instance (hS : S.IsValid 𝒮 γ) (ε : ℝ) {k : Ω → ℤ} (hk : Measurable k) :
    IsMarkovKernel (walkKernelAt hS ε hk) := by
  unfold walkKernelAt
  infer_instance

theorem walkKernelAt_apply (hS : S.IsValid 𝒮 γ) (ε : ℝ) {k : Ω → ℤ} (hk : Measurable k) (ω : Ω) :
    walkKernelAt hS ε hk ω = srwLaw (S.mult ε ω) (k ω) := rfl

/-- **Markov step of the interpolated embedded walk at one scale, started at a random vertex**,
conditional expectation form. -/
theorem condExp_walkShift_interp_at (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ}
    (hm : 0 < m) (ε : ℝ) {k : Ω → ℤ} (hk : Measurable k) (n : ℕ) (f : ContinuousPath ℂ →ᵇ ℝ) :
    (S.P ⊗ₘ walkKernelAt hS ε hk)[fun p : Ω × (ℕ → ℤ) =>
        f (pathShift (interpPathCM (v p.1) hm.le p.2) ((n / m : ℝ).toNNReal)) |
      MeasurableSpace.comap (fun p : Ω × (ℕ → ℤ) => (p.1, frestrictLe n p.2)) inferInstance]
      =ᵐ[S.P ⊗ₘ walkKernelAt hS ε hk] fun p : Ω × (ℕ → ℤ) =>
        ∫ g, f g ∂(walkPathLaw S v hm.le ε (lastState n (frestrictLe n p.2)) p.1 :
          Measure (ContinuousPath ℂ)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hmain := condExp_comp_eq_integral_kernel (μ := S.P) (walkKernelAt hS ε hk)
    (π := frestrictLe n) (measurable_frestrictLe n) (τ := lastState n) (measurable_lastState n)
    (θ := MatedCRTHarmonic.Markov.walkShift n) (MatedCRTHarmonic.Markov.measurable_walkShift n)
    (walkStartKernel hS ε) (F := walkIntegrand v hm.le f)
    (measurable_walkIntegrand hv hm.le f.continuous.measurable) (C := ‖f‖)
    (fun p => by simpa [walkIntegrand, Real.norm_eq_abs] using f.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun ω E hE B hB => walkKernel_markov_step hS ε (k ω) n ω hE hB)
  have e1 : (fun p : Ω × (ℕ → ℤ) =>
      f (pathShift (interpPathCM (v p.1) hm.le p.2) ((n / m : ℝ).toNNReal))) =
      fun p : Ω × (ℕ → ℤ) => walkIntegrand v hm.le f (p.1, MatedCRTHarmonic.Markov.walkShift n p.2) :=
    funext fun p => (walkIntegrand_walkShift v hm f p.1 p.2 n).symm
  rw [e1]
  refine hmain.trans (Filter.Eventually.of_forall fun p => ?_)
  exact integral_walkStartKernel hS v hm.le ε p.1 _ f.continuous.measurable

/-- The independent product over the scales `n` of the annealed laws `S.P ⊗ₘ walkKernelAt hS (ε n) (hk n)`
of the walks started at the random vertices `k n`. -/
noncomputable def annealedWalksAt (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n)) : Measure ((_ : ℕ) → Ω × (ℕ → ℤ)) :=
  Measure.infinitePi fun n => S.P ⊗ₘ walkKernelAt hS (ε n) (hk n)

instance (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) : IsProbabilityMeasure (annealedWalksAt hS ε hk) := by
  unfold annealedWalksAt
  infer_instance

/-- The `n`-th coordinate of the product space has the annealed law of the `n`-th scale. -/
theorem annealedWalksAt_map_eval (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n)) (n : ℕ) :
    (annealedWalksAt hS ε hk).map (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n) =
      S.P ⊗ₘ walkKernelAt hS (ε n) (hk n) :=
  Measure.infinitePi_map_eval _ n

/-- **Markov step of the interpolated embedded walk at the `n`-th scale, on the product space, for walks
started at random vertices.** -/
theorem condExp_walkShift_interp_pi_at (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ)
    {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n)) {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n))
    {m : ℕ → ℝ} (hm : ∀ n, 0 < m n) (j : ℕ → ℕ) (n : ℕ) (f : ContinuousPath ℂ →ᵇ ℝ) :
    (annealedWalksAt hS ε hk)[fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
        f (pathShift (interpPathCM (v n (p n).1) (hm n).le (p n).2) ((j n / m n : ℝ).toNNReal)) |
      MeasurableSpace.comap
        (fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => ((p n).1, frestrictLe (j n) (p n).2)) inferInstance]
      =ᵐ[annealedWalksAt hS ε hk] fun p : (_ : ℕ) → Ω × (ℕ → ℤ) =>
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
  have h1 := condExp_comp_comap_ae_eq (μ := annealedWalksAt hS ε hk) hπ
    (G := MeasurableSpace.comap (fun q : Ω × (ℕ → ℤ) => (q.1, frestrictLe (j n) q.2)) inferInstance)
    hgm.comap_le hFm (C := ‖f‖) (fun q => by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _)
  rw [MeasurableSpace.comap_comp] at h1
  have h2 := condExp_walkShift_interp_at hS (hv n) (hm n) (ε n) (hk n) (j n) f
  rw [← annealedWalksAt_map_eval hS ε hk n] at h2
  exact h1.trans (ae_eq_comp (μ := annealedWalksAt hS ε hk) hπ.aemeasurable h2)

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Kernel representation of the annealed integral at the `n`-th scale, random start vertex.**  For a
bounded continuous `g` on the product of the datum space and the path space, the annealed expectation of
`g (Dₙ, Xₙ)` over `annealedWalksAt` is the environment average of the integral of `g (Dₙ ω, ·)` against the
quenched path law of the walk started at `kₙ ω`. -/
theorem integral_annealedWalksAt_eq_integral_walkPathLaw
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀]
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n) {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    (g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ) (n : ℕ) :
    ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2) ∂annealedWalksAt hS ε hk =
      ∫ ω, ∫ x, g (d n ω, x)
        ∂(walkPathLaw S (v n) (hm n).le (ε n) (k n ω) ω : Measure C(ℝ≥0, ℂ)) ∂S.P := by
  have hev : Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply n
  have hF : Measurable fun q : Ω × (ℕ → ℤ) =>
      g (d n q.1, interpPathCM (v n q.1) (hm n).le q.2) :=
    g.continuous.measurable.comp (((hd n).comp measurable_fst).prodMk
      ((measurable_interpPathCM_uncurry (hm n).le).comp
        (((hv n).comp measurable_fst).prodMk measurable_snd)))
  have h1 : ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
      ∂annealedWalksAt hS ε hk = ∫ q, g (d n q.1, interpPathCM (v n q.1) (hm n).le q.2)
        ∂(S.P ⊗ₘ walkKernelAt hS (ε n) (hk n)) := by
    rw [← annealedWalksAt_map_eval hS ε hk n]
    exact (integral_map hev.aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, Measure.integral_compProd]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hfm : Measurable fun y : C(ℝ≥0, ℂ) => g (d n ω, y) :=
      g.continuous.measurable.comp (measurable_const.prodMk measurable_id)
    exact integral_walkStartKernel hS (v n) (hm n).le (ε n) ω (k n ω) hfm
  · exact Integrable.of_bound hF.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall fun q => by simpa using g.norm_coe_le_norm _)

/-- **The quenched Markov property of the limit kernel from the Markov step of the embedded walks started
at random vertices** (BG20 Lemma 7.4, Markov part): the statement of `ae_markovAt_of_walk_markov_step`
for the product `annealedWalksAt` of the annealed laws of walks started at the vertices `kₙ ω`. -/
theorem ae_markovAt_of_walk_markov_step_at
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n))
    {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ} (hm : ∀ n, 0 < m n) (j : ℕ → ℕ)
    {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    {ν : Measure (S₀ × C(ℝ≥0, ℂ))} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ,
      Filter.Tendsto (fun n => ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
          ∂annealedWalksAt hS ε hk) Filter.atTop (nhds (∫ q, g q ∂ν)))
    {t T : ℝ≥0}
    (hs : Filter.Tendsto (fun n => ((j n / m n : ℝ).toNNReal)) Filter.atTop (nhds t))
    (hsT : ∀ n, ((j n / m n : ℝ).toNNReal) ≤ T)
    {K : S₀ → C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))} (hK : Continuous K)
    (hclose : TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : (_ : ℕ) → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (v n) (hm n).le (ε n) (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 :
          Measure C(ℝ≥0, ℂ))
        (K (d n (p n).1) (interpPathCM (v n (p n).1) (hm n).le (p n).2 ((j n / m n : ℝ).toNNReal)) :
          Measure C(ℝ≥0, ℂ))) Filter.atTop 0)
    {νD : Measure S₀} [IsProbabilityMeasure νD] {κ₀ : Kernel S₀ C(ℝ≥0, ℂ)} {z₀ : ℂ}
    (hν : ν = νD ⊗ₘ κ₀) (hκ₀ : ∀ d, κ₀ d = (K d z₀ : Measure C(ℝ≥0, ℂ))) :
    ∀ᵐ d ∂νD, MarkovAt (K d) z₀ t := by
  have hev : ∀ n, Measurable fun p : (_ : ℕ) → Ω × (ℕ → ℤ) => p n := measurable_pi_apply
  refine ae_markovAt_of_markov_step_pathShift (μ := annealedWalksAt hS ε hk)
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
    (fun n f => condExp_walkShift_interp_pi_at hS ε hk hv hm j n f)
    hclose hν hκ₀
  exact (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp
    ((measurable_walkPathLaw_present hS (hv n) (hm n).le (ε n) (j n)).comp
      ((hev n)))).aemeasurable

end RandomStart

end MatedCRT
