import MatedCRT.FirstPass.LPBridge.ExitRestartCanonical
import LatticeProb.Prob.BrownianOutwardExcursion

/-!
# Post-exit increments of planar Brownian motion are planar Brownian motion

For a planar Brownian motion `𝓑` started at `x` and an open set `U`, let `τ` be the first exit time
of `U`, as an `ℝ≥0`-valued random time. The post-`τ` increments `t ↦ 𝓑(τ + t) - 𝓑(τ)` form a planar
Brownian motion, independent of `𝓑(τ)` (strong Markov property at the exit time; Mörters–Peres,
*Brownian Motion*, Theorem 2.16).

The proof truncates `τ` at `K` (a stopping time, MarkovProcess), applies the restart identity of
`ExitRestartCanonical`, and lets `K → ∞`. The truncated and true quantities agree on
`{exitTime ≤ K}`, whose complement has probability tending to `0`, so the identities pass to the
limit for events; the Brownian properties are identities between laws, which pass along the path map.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.ExitRestart

section Transfer

variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]

/-- A law of a composite with a measurable path map is the law of the outer map under the image. -/
lemma hasLaw_comp_iff {P : Measure Ω} {Φ : Ω → E} {G : E → F} {ν : Measure F}
    (hΦ : Measurable Φ) (hG : Measurable G) :
    HasLaw (G ∘ Φ) ν P ↔ HasLaw G ν (P.map Φ) := by
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hG.aemeasurable, by rw [Measure.map_map hG hΦ]; exact h⟩
  · rintro ⟨-, h⟩
    exact ⟨(hG.comp hΦ).aemeasurable, by rw [← Measure.map_map hG hΦ]; exact h⟩

/-- The pre-Brownian property is a property of the law of the path. -/
lemma isPreBrownianReal_iff_map {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {Φ : Ω → ℝ≥0 → ℝ}
    (hΦ : Measurable Φ) (hX : ∀ t ω, X t ω = Φ ω t) :
    ProbabilityTheory.IsPreBrownianReal X P ↔
      ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (f : ℝ≥0 → ℝ) => f t) (P.map Φ) := by
  have hcomp : ∀ I : Finset ℝ≥0, (fun ω => I.restrict (fun t => X t ω)) =
      (fun f : ℝ≥0 → ℝ => I.restrict (fun t => f t)) ∘ Φ := by
    intro I
    funext ω
    simp only [Function.comp_apply, hX]
  have hG : ∀ I : Finset ℝ≥0, Measurable (fun f : ℝ≥0 → ℝ => I.restrict (fun t => f t)) :=
    fun I => Finset.measurable_restrict I
  constructor
  · intro h
    refine ProbabilityTheory.IsPreBrownianReal.mk' fun I => ?_
    have h' := h.hasLaw I
    rw [hcomp I] at h'
    exact (hasLaw_comp_iff hΦ (hG I)).1 h'
  · intro h
    refine ProbabilityTheory.IsPreBrownianReal.mk' fun I => ?_
    rw [hcomp I]
    exact (hasLaw_comp_iff hΦ (hG I)).2 (h.hasLaw I)

end Transfer

/-! ### Planar coordinates of laws -/

/-- Real part of a complex path. -/
def reProj (f : ℝ≥0 → ℂ) : ℝ≥0 → ℝ := fun t => (f t).re

/-- Imaginary part of a complex path. -/
def imProj (f : ℝ≥0 → ℂ) : ℝ≥0 → ℝ := fun t => (f t).im

lemma measurable_reProj : Measurable reProj :=
  Measurable.of_eval fun t => Complex.measurable_re.comp (measurable_pi_apply t)

lemma measurable_imProj : Measurable imProj :=
  Measurable.of_eval fun t => Complex.measurable_im.comp (measurable_pi_apply t)

instance isProbabilityMeasure_muOne : IsProbabilityMeasure muOne := by
  unfold muOne
  exact (Measure.isProbabilityMeasure_map_iff (measurable_c1 0).aemeasurable).2 inferInstance

instance isProbabilityMeasure_muPlanar : IsProbabilityMeasure muPlanar := by
  unfold muPlanar
  exact (Measure.isProbabilityMeasure_map_iff measurable_psi.aemeasurable).2 inferInstance

lemma isPreBrownianReal_muOne :
    ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (f : ℝ≥0 → ℝ) => f t) muOne :=
  (isPreBrownianReal_iff_map (P := brownianMotion 0) (X := fun t ω => ω t - 0) (Φ := c1 0)
    (measurable_c1 0) (fun _ _ => rfl)).1 (brownianMotion_isPreBrownianReal 0)

lemma muPlanar_map_reProj : muPlanar.map reProj = muOne := by
  unfold muPlanar
  rw [Measure.map_map measurable_reProj measurable_psi]
  have h : reProj ∘ (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => psi p.1 p.2) = Prod.fst := by
    funext p
    funext t
    simp [reProj, psi]
  rw [h, Measure.map_fst_prod]
  simp

lemma muPlanar_map_imProj : muPlanar.map imProj = muOne := by
  unfold muPlanar
  rw [Measure.map_map measurable_imProj measurable_psi]
  have h : imProj ∘ (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => psi p.1 p.2) = Prod.snd := by
    funext p
    funext t
    simp [imProj, psi]
  rw [h, Measure.map_snd_prod]
  simp

lemma muPlanar_map_pair :
    muPlanar.map (fun f => (reProj f, imProj f)) = muOne.prod muOne := by
  unfold muPlanar
  rw [Measure.map_map (measurable_reProj.prodMk measurable_imProj) measurable_psi]
  have h : (fun f : ℝ≥0 → ℂ => (reProj f, imProj f)) ∘
      (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => psi p.1 p.2) = id := by
    funext p
    exact Prod.ext (funext fun t => by simp [reProj, psi]) (funext fun t => by simp [imProj, psi])
  rw [h, Measure.map_id]

/-! ### Limits of events along an increasing sequence of good sets -/

/-- Events that agree with `E` on the increasing good sets `G K` have probabilities converging to
`μ E`, provided the good sets exhaust the space almost surely. -/
lemma tendsto_measure_of_agree_on_good {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : ℕ → Set Ω} (hGm : ∀ K, MeasurableSet (G K))
    (hG : Monotone G) (hfull : ∀ᵐ ω ∂μ, ∃ K, ω ∈ G K)
    {E : Set Ω} {E' : ℕ → Set Ω} (hagree : ∀ K, E ∩ G K = E' K ∩ G K) :
    Tendsto (fun K => μ (E' K)) atTop (𝓝 (μ E)) := by
  have hmono : Monotone fun K => E ∩ G K := fun a b hab => inter_subset_inter_right E (hG hab)
  have hnull : μ (E \ ⋃ K, G K) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hfull)
    intro ω hω hex
    obtain ⟨K, hK⟩ := hex
    exact hω.2 (mem_iUnion.2 ⟨K, hK⟩)
  have hEU : μ (⋃ K, E ∩ G K) = μ E := by
    have h1 : (⋃ K, E ∩ G K) = E ∩ ⋃ K, G K := by rw [inter_iUnion]
    rw [h1]
    have h2 := measure_inter_add_sdiff (μ := μ) E (MeasurableSet.iUnion hGm)
    rw [hnull, add_zero] at h2
    exact h2
  have hlow : Tendsto (fun K => μ (E ∩ G K)) atTop (𝓝 (μ E)) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hEU] at this
    exact this
  have htail : Tendsto (fun K => μ (G K)ᶜ) atTop (𝓝 0) := by
    have hae : ∀ᵐ ω ∂μ, ω ∈ ⋃ K, G K := hfull.mono fun ω hω => mem_iUnion.2 hω
    have hnull' : μ (⋂ K, (G K)ᶜ) = 0 := by
      rw [← compl_iUnion]
      exact ae_iff.1 hae
    have := tendsto_measure_iInter_atTop (μ := μ) (s := fun K => (G K)ᶜ)
      (fun K => (hGm K).compl.nullMeasurableSet) (fun a b hab => compl_subset_compl.2 (hG hab))
      ⟨0, measure_ne_top μ _⟩
    rw [hnull'] at this
    exact this
  have hup := hlow.add htail
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun K => ?_) (fun K => ?_)
  · refine measure_mono ?_
    rw [hagree K]
    exact inter_subset_left
  · calc μ (E' K) ≤ μ ((E' K ∩ G K) ∪ (G K)ᶜ) := by
          refine measure_mono fun ω hω => ?_
          by_cases h : ω ∈ G K
          · exact Or.inl ⟨hω, h⟩
          · exact Or.inr h
      _ ≤ μ (E' K ∩ G K) + μ (G K)ᶜ := measure_union_le _ _
      _ = μ (E ∩ G K) + μ (G K)ᶜ := by rw [hagree K]

/-! ### Exit times and post-exit increments -/

/-- The exit time of `U` as an `ℝ≥0`-valued random time (the time `τ` of the bridge). -/
noncomputable def exitNN (U : Set ℂ) (η : ContinuousPath ℂ) : ℝ≥0 :=
  (ContinuousPath.exitTime U η).toNNReal

/-- The path after a random time `τ`, centred at its value there: `t ↦ η (τ + t) - η τ`. -/
def postIncr (τ : ContinuousPath ℂ → ℝ≥0) (η : ContinuousPath ℂ) : ℝ≥0 → ℂ :=
  fun t => η (τ η + t) - η (τ η)

lemma postIncr_eq_cStart (τ : ContinuousPath ℂ → ℝ≥0) (η : ContinuousPath ℂ) :
    postIncr τ η = cStart (ContinuousPath.shift (τ η) η) := by
  funext t
  simp [postIncr, cStart, ContinuousPath.shift_apply]

lemma measurable_eval_at {τ : ContinuousPath ℂ → ℝ≥0} (hτ : Measurable τ) :
    Measurable (fun η : ContinuousPath ℂ => η (τ η)) := by
  have hc := (ContinuousPath.measurable_coordinateProcess (0 : ℝ≥0)).comp
    (ContinuousPath.measurable_shift_of_measurable τ hτ)
  convert hc using 1
  funext η
  simp [ContinuousPath.shift_apply, ContinuousPath.coordinateProcess_apply]

lemma measurable_postIncr {τ : ContinuousPath ℂ → ℝ≥0} (hτ : Measurable τ) :
    Measurable (postIncr τ) := by
  refine Measurable.of_eval fun t => ?_
  have hc := (ContinuousPath.measurable_coordinateProcess t).comp
    (ContinuousPath.measurable_shift_of_measurable τ hτ)
  convert hc.sub (measurable_eval_at hτ) using 1
  funext η
  simp [postIncr, ContinuousPath.shift_apply, ContinuousPath.coordinateProcess_apply]

lemma exitTimeTrunc_eq_toNNReal_min (U : Set ℂ) (K : ℝ≥0) (η : ContinuousPath ℂ) :
    ContinuousPath.exitTimeTrunc U K η =
      (min (ContinuousPath.exitTime U η) (K : ℝ≥0∞)).toNNReal := by
  rw [← ENNReal.toNNReal_coe (ContinuousPath.exitTimeTrunc U K η)]
  congr 1
  exact ContinuousPath.coe_exitTimeTrunc U K η

lemma exitTimeTrunc_eq_exitNN {U : Set ℂ} {K : ℝ≥0} {η : ContinuousPath ℂ}
    (h : ContinuousPath.exitTime U η ≤ (K : ℝ≥0∞)) :
    ContinuousPath.exitTimeTrunc U K η = exitNN U η := by
  rw [exitTimeTrunc_eq_toNNReal_min, min_eq_left h]
  rfl

/-- The truncated exit time is measurable. -/
lemma measurable_exitTimeTrunc {U : Set ℂ} (hU : IsOpen U) (K : ℝ≥0) :
    Measurable (fun η : ContinuousPath ℂ => ContinuousPath.exitTimeTrunc U K η) := by
  have h : (fun η : ContinuousPath ℂ => ContinuousPath.exitTimeTrunc U K η) =
      fun η => (min (ContinuousPath.exitTime U η) (K : ℝ≥0∞)).toNNReal :=
    funext fun η => exitTimeTrunc_eq_toNNReal_min U K η
  rw [h]
  exact ((ContinuousPath.measurable_exitTime U hU).min measurable_const).ennreal_toNNReal

/-- The good sets `{exitTime ≤ K}`, increasing in `K ∈ ℕ`. -/
def exitGood (U : Set ℂ) (K : ℕ) : Set (ContinuousPath ℂ) :=
  {η | ContinuousPath.exitTime U η ≤ ((K : ℝ≥0) : ℝ≥0∞)}

lemma measurableSet_exitGood {U : Set ℂ} (hU : IsOpen U) (K : ℕ) :
    MeasurableSet (exitGood U K) :=
  measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const

lemma monotone_exitGood (U : Set ℂ) : Monotone (exitGood U) := fun a b hab η hη =>
  show ContinuousPath.exitTime U η ≤ ((b : ℝ≥0) : ℝ≥0∞) from
    (show ContinuousPath.exitTime U η ≤ ((a : ℝ≥0) : ℝ≥0∞) from hη).trans (by exact_mod_cast hab)

lemma ae_exists_exitGood {U : Set ℂ} {μ : Measure (ContinuousPath ℂ)}
    (hfin : ∀ᵐ η ∂μ, ContinuousPath.exitTime U η ≠ ⊤) : ∀ᵐ η ∂μ, ∃ K : ℕ, η ∈ exitGood U K :=
  hfin.mono fun η hη => by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hη
    exact ⟨n, show ContinuousPath.exitTime U η ≤ ((n : ℝ≥0) : ℝ≥0∞) by simpa using hn.le⟩

/-- The event that the truncated exit position lies in `S`. -/
def truncA (S : Set ℂ) (U : Set ℂ) (K : ℕ) : Set (ContinuousPath ℂ) :=
  (fun η => η (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η)) ⁻¹' S

/-- The event that the truncated exit position lies in `S` and the truncated post-exit path lies in
`Γ`. -/
def truncE (S : Set ℂ) (Γ : Set (ℝ≥0 → ℂ)) (U : Set ℂ) (K : ℕ) : Set (ContinuousPath ℂ) :=
  truncA S U K ∩ postIncr (fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ⁻¹' Γ

lemma truncA_agree {U : Set ℂ} (S : Set ℂ) (K : ℕ) :
    (fun η : ContinuousPath ℂ => η (exitNN U η)) ⁻¹' S ∩ exitGood U K = truncA S U K ∩ exitGood U K := by
  ext η
  constructor
  · rintro ⟨h1, h2⟩
    have h4 : ContinuousPath.exitTime U η ≤ ((K : ℝ≥0) : ℝ≥0∞) := h2
    refine ⟨?_, h2⟩
    show η (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ∈ S
    rw [exitTimeTrunc_eq_exitNN h4]
    exact h1
  · rintro ⟨h1, h2⟩
    have h4 : ContinuousPath.exitTime U η ≤ ((K : ℝ≥0) : ℝ≥0∞) := h2
    refine ⟨?_, h2⟩
    have h5 : η (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ∈ S := h1
    rw [exitTimeTrunc_eq_exitNN h4] at h5
    exact h5

lemma postIncr_congr_of_eq {τ τ' : ContinuousPath ℂ → ℝ≥0} {η : ContinuousPath ℂ}
    (h : τ η = τ' η) : postIncr τ η = postIncr τ' η := by
  unfold postIncr
  rw [h]

lemma truncE_agree {U : Set ℂ} (S : Set ℂ) (Γ : Set (ℝ≥0 → ℂ)) (K : ℕ) :
    (fun η : ContinuousPath ℂ => η (exitNN U η)) ⁻¹' S ∩ postIncr (exitNN U) ⁻¹' Γ ∩ exitGood U K =
      truncE S Γ U K ∩ exitGood U K := by
  ext η
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : ContinuousPath.exitTime U η ≤ ((K : ℝ≥0) : ℝ≥0∞) := h3
    have hp := postIncr_congr_of_eq (τ := fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η)
      (τ' := exitNN U) (η := η) (exitTimeTrunc_eq_exitNN h4)
    refine ⟨⟨?_, ?_⟩, h3⟩
    · show η (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ∈ S
      rw [exitTimeTrunc_eq_exitNN h4]
      exact h1
    · show postIncr (fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) η ∈ Γ
      rw [hp]
      exact h2
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : ContinuousPath.exitTime U η ≤ ((K : ℝ≥0) : ℝ≥0∞) := h3
    have hp := postIncr_congr_of_eq (τ := fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η)
      (τ' := exitNN U) (η := η) (exitTimeTrunc_eq_exitNN h4)
    refine ⟨⟨?_, ?_⟩, h3⟩
    · have h5 : η (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ∈ S := h1
      rw [exitTimeTrunc_eq_exitNN h4] at h5
      exact h5
    · have h6 : postIncr (fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) η ∈ Γ := h2
      rw [hp] at h6
      exact h6

/-- **Joint law of the exit position and the post-exit increments of planar Brownian motion.**
`P(A ∩ {post-τ increments ∈ Γ}) = P(A) · μ(Γ)`, for `A` the event that the exit position lies in
`S`, and `μ = muPlanar` the centred planar Brownian law. -/
theorem planar_exit_joint {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤)
    {S : Set ℂ} (hS : MeasurableSet S) {Γ : Set (ℝ≥0 → ℂ)} (hΓ : MeasurableSet Γ) :
    planarBrownianMotion x ((fun η => η (exitNN U η)) ⁻¹' S ∩ postIncr (exitNN U) ⁻¹' Γ)
      = planarBrownianMotion x ((fun η => η (exitNN U η)) ⁻¹' S) * muPlanar Γ := by
  have hA : ∀ K : ℕ, MeasurableSet[(ContinuousPath.isStoppingTime_exitTimeTrunc U hU (K : ℝ≥0)).measurableSpace]
      (truncA S U K) := fun K =>
    (ContinuousPath.measurable_eval_stoppingTime
      (fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η)
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU (K : ℝ≥0))) hS
  have hval : ∀ K : ℕ, planarBrownianMotion x (truncE S Γ U K) =
      planarBrownianMotion x (truncA S U K) * muPlanar Γ := by
    intro K
    have hset : postIncr (fun η => ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) ⁻¹' Γ =
        (fun η => ContinuousPath.shift (ContinuousPath.exitTimeTrunc U (K : ℝ≥0) η) η) ⁻¹'
          (cStart ⁻¹' Γ) := by
      ext η
      simp only [Set.mem_preimage, postIncr_eq_cStart]
    rw [truncE, hset]
    exact restart_exitTimeTrunc hU (K : ℝ≥0) x (hA K) hΓ
  have hlim1 := tendsto_measure_of_agree_on_good (μ := planarBrownianMotion x)
    (G := exitGood U) (fun K => measurableSet_exitGood hU K) (monotone_exitGood U)
    (ae_exists_exitGood hfin) (truncE_agree S Γ)
  have hlim2 := tendsto_measure_of_agree_on_good (μ := planarBrownianMotion x)
    (G := exitGood U) (fun K => measurableSet_exitGood hU K) (monotone_exitGood U)
    (ae_exists_exitGood hfin) (truncA_agree S)
  have hlim3 := ENNReal.Tendsto.mul_const hlim2 (Or.inr (measure_ne_top _ _) : _ ∨ muPlanar Γ ≠ ⊤)
  have heq : (fun K : ℕ => planarBrownianMotion x (truncE S Γ U K)) =
      (fun K : ℕ => planarBrownianMotion x (truncA S U K) * muPlanar Γ) := funext hval
  rw [heq] at hlim1
  exact tendsto_nhds_unique hlim1 hlim3

/-- The post-exit increments have the centred planar Brownian law. -/
theorem planar_postIncr_law {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤)
    {Γ : Set (ℝ≥0 → ℂ)} (hΓ : MeasurableSet Γ) :
    planarBrownianMotion x (postIncr (exitNN U) ⁻¹' Γ) = muPlanar Γ := by
  have h := planar_exit_joint hU x hfin MeasurableSet.univ hΓ
  simpa only [Set.preimage_univ, Set.univ_inter, measure_univ, one_mul] using h

/-- The exit position and the post-exit increments are independent. -/
theorem planar_exit_indepFun {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤) :
    IndepFun (fun η => η (exitNN U η)) (postIncr (exitNN U)) (planarBrownianMotion x) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S Γ hS hΓ
  rw [planar_exit_joint hU x hfin hS hΓ, planar_postIncr_law hU x hfin hΓ]

/-- Planar Brownian motion, centred at its start, as a path-space law (laws of the Brownian
conditions transfer along the path map). -/
lemma isPlanarBrownian_of_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {I : Ω → ℝ≥0 → ℂ} (hI : Measurable I)
    (hcont : ∀ ω, Continuous fun t => I ω t) (hlaw : P.map I = muPlanar) :
    LatticeProb.PlanarBrownian.IsPlanarBrownian (fun t ω => I ω t) P := by
  have hre : P.map (fun ω t => (I ω t).re) = muOne := by
    have h : (fun ω t => (I ω t).re) = reProj ∘ I := rfl
    rw [h, ← Measure.map_map measurable_reProj hI, hlaw, muPlanar_map_reProj]
  have him : P.map (fun ω t => (I ω t).im) = muOne := by
    have h : (fun ω t => (I ω t).im) = imProj ∘ I := rfl
    rw [h, ← Measure.map_map measurable_imProj hI, hlaw, muPlanar_map_imProj]
  have hpair : P.map (fun ω => ((fun t => (I ω t).re), (fun t => (I ω t).im))) =
      muOne.prod muOne := by
    have h : (fun ω => ((fun t => (I ω t).re), (fun t => (I ω t).im))) =
        (fun f : ℝ≥0 → ℂ => (reProj f, imProj f)) ∘ I := rfl
    rw [h, ← Measure.map_map (measurable_reProj.prodMk measurable_imProj) hI, hlaw,
      muPlanar_map_pair]
  have hΦre : Measurable (fun ω t => (I ω t).re) := measurable_reProj.comp hI
  have hΦim : Measurable (fun ω t => (I ω t).im) := measurable_imProj.comp hI
  have hreP : ProbabilityTheory.IsPreBrownianReal (fun t ω => (I ω t).re) P :=
    (isPreBrownianReal_iff_map hΦre (fun _ _ => rfl)).2 (by rw [hre]; exact isPreBrownianReal_muOne)
  have himP : ProbabilityTheory.IsPreBrownianReal (fun t ω => (I ω t).im) P :=
    (isPreBrownianReal_iff_map hΦim (fun _ _ => rfl)).2 (by rw [him]; exact isPreBrownianReal_muOne)
  have hindep : IndepFun (fun ω t => (I ω t).re) (fun ω t => (I ω t).im) P := by
    refine (indepFun_iff_map_prod_eq_prod_map_map hΦre.aemeasurable hΦim.aemeasurable).2 ?_
    rw [hpair, hre, him]
  refine ⟨fun t => (measurable_pi_apply t).comp hI, ⟨hreP, ?_⟩, ⟨himP, ?_⟩, hindep⟩
  · exact Filter.Eventually.of_forall fun ω => Complex.continuous_re.comp (hcont ω)
  · exact Filter.Eventually.of_forall fun ω => Complex.continuous_im.comp (hcont ω)

/-- **The post-exit increments of planar Brownian motion form a planar Brownian motion.** -/
theorem planar_postIncr_isPlanarBrownian {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤) :
    LatticeProb.PlanarBrownian.IsPlanarBrownian
      (fun t η => postIncr (exitNN U) η t) (planarBrownianMotion x) := by
  have hτm : Measurable (exitNN U) := (ContinuousPath.measurable_exitTime U hU).ennreal_toNNReal
  refine isPlanarBrownian_of_law (measurable_postIncr hτm) (fun η => ?_) ?_
  · unfold postIncr
    exact ((η.continuous.comp (continuous_const.add continuous_id)).sub continuous_const)
  · refine Measure.ext fun Γ hΓ => ?_
    rw [Measure.map_apply (measurable_postIncr hτm) hΓ]
    exact planar_postIncr_law hU x hfin hΓ

/-- **Exit restart for planar Brownian motion** (the content of `hRestart` in the bridge): the
post-exit increments form a planar Brownian motion, independent of the exit position, and the exit
position is a.e. measurable. -/
theorem exit_restart_planar {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤) :
    LatticeProb.PlanarBrownian.IsPlanarBrownian
        (fun (s : ℝ≥0) (b : ContinuousPath ℂ) => b (exitNN U b + s) - b (exitNN U b))
        (planarBrownianMotion x) ∧
      IndepFun (fun b : ContinuousPath ℂ => b (exitNN U b))
        (fun (b : ContinuousPath ℂ) (s : ℝ≥0) => b (exitNN U b + s) - b (exitNN U b))
        (planarBrownianMotion x) ∧
      AEMeasurable (fun b : ContinuousPath ℂ => b (exitNN U b)) (planarBrownianMotion x) :=
  ⟨planar_postIncr_isPlanarBrownian hU x hfin, planar_exit_indepFun hU x hfin,
    (measurable_eval_at ((ContinuousPath.measurable_exitTime U hU).ennreal_toNNReal)).aemeasurable⟩

end MatedCRT.ExitRestart
