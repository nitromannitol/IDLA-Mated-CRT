import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.JointMeasureLaw

/-! # Joint laws of circle averages and LQG measures on two probability spaces

If the circle-average processes of two fields, realized on possibly different probability spaces, have the same
law, then so do the pairs (circle-average process, limiting `γ`-LQG measure). This is the two-space form of
`MatedCRT.identDistrib_circleProcess_lqgMeasure` (MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/JointMeasureLaw.lean),
with the same proof: the masses of open sets are a Borel function of the circle-average process
(through the dyadic approximations `lqgApprox`), and a locally finite measure on `ℂ` is determined by its open masses. The
single-space comparison of finite-dimensional laws is replaced by the uniqueness of projective limits
(`MeasureTheory.IsProjectiveLimit.unique`).

Use: the law of `(circle averages, μ_h)` is the same in every realization of the quantum cone, which is the first
step in showing that the law of the LQG-area parametrized space-filling curve does not depend on the realization. -/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- **Circle averages and countably many open masses, two spaces.** If the circle-average processes of `c` under
`P` and of `d` under `Q` have the same law, and `μ`, `ν` are a.s. the `γ`-LQG limits, then for every family of
open sets `U i`, `(circle averages, (μ (U i))_i)` and `(circle averages, (ν (U i))_i)` have the same law. -/
theorem identDistrib_circleProcess_openMasses_of_identDistrib
    {Ω Ω' ι : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {γ : ℝ}
    {c : Ω → ℝ → ℂ → ℝ} {d : Ω' → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {ν : Ω' → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ᵐ ω ∂Q, ContinuousOn (fun p : ℝ × ℂ => d ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (c ω) (μ ω))
    (hν : ∀ᵐ ω ∂Q, IsLQGLimit γ (d ω) (ν ω))
    (hlaw : IdentDistrib (fun ω => circleProcess (c ω)) (fun ω => circleProcess (d ω)) P Q)
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) :
    IdentDistrib (fun ω => (circleProcess (c ω), fun i => μ ω (U i)))
      (fun ω => (circleProcess (d ω), fun i => ν ω (U i))) P Q := by
  classical
  choose f hf hfc hmass using fun i : ι => exists_open_mass_test_functions (hU i)
  choose A hA hAeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  let profile (n : ℕ) (v : Ioi (0 : ℝ) × ℂ → ℝ) (z : ℂ) :=
    v (⟨dyadicScale n, dyadicScale_pos n⟩, z)
  have hp (n : ℕ) : Measurable (profile n) := by
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply _
  let F : (Ioi (0 : ℝ) × ℂ → ℝ) → ι → ℝ≥0∞ := fun v i =>
    ⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal (∫ z, f i j z ∂(A n (profile n v)))) atTop
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    apply Measurable.iSup
    intro j
    apply Measurable.liminf
    intro n
    exact (((hf i j).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp
      ((hA n).comp (hp n))).ennreal_ofReal
  have hFeq : ∀ (x : ℝ → ℂ → ℝ) (m : Measure ℂ),
      ContinuousOn (fun p : ℝ × ℂ => x p.1 p.2) (Ioi 0 ×ˢ univ) → IsLQGLimit γ x m →
        F (circleProcess x) = fun i => m (U i) := by
    intro x m hxω hmω
    funext i
    rw [hmass i m hmω.isLocallyFiniteMeasure]
    change (⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal
      (∫ z, f i j z ∂(A n (profile n (circleProcess x))))) atTop) = _
    apply iSup_congr
    intro j
    apply Filter.Tendsto.liminf_eq
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    convert hmω.tendsto_integral (f i j) (hf i j) (hfc i j) using 1
    funext n
    have hcont : Continuous (fun z => x (dyadicScale n) z) :=
      hxω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨dyadicScale_pos n, mem_univ z⟩)
    have heq : A n (profile n (circleProcess x)) = lqgApprox γ x (dyadicScale n) := by
      simpa only [profile, circleProcess, lqgApprox] using hAeq n (fun z => x (dyadicScale n) z) hcont
    rw [heq]
  have hD := hlaw.comp (measurable_id.prodMk hF)
  have hleft : ∀ᵐ ω ∂P, (circleProcess (c ω), F (circleProcess (c ω))) =
      (circleProcess (c ω), fun i => μ ω (U i)) := by
    filter_upwards [hc, hμ] with ω h1 h2
    rw [hFeq _ _ h1 h2]
  have hright : ∀ᵐ ω ∂Q, (circleProcess (d ω), F (circleProcess (d ω))) =
      (circleProcess (d ω), fun i => ν ω (U i)) := by
    filter_upwards [hd, hν] with ω h1 h2
    rw [hFeq _ _ h1 h2]
  exact ((IdentDistrib.of_ae_eq hD.aemeasurable_fst hleft).symm.trans hD).trans
    (IdentDistrib.of_ae_eq hD.aemeasurable_snd hright)

/-- **Circle averages and the LQG measure, two spaces.** If the circle-average processes of `c` under `P` and of
`d` under `Q` have the same law, and `μ`, `ν` are a.s. measurable `γ`-LQG limits of `c`, `d`, then the pairs
`(circle averages, μ)` and `(circle averages, ν)` have the same law. -/
theorem identDistrib_circleProcess_lqgMeasure_of_identDistrib
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsFiniteMeasure Q] {γ : ℝ}
    {c : Ω → ℝ → ℂ → ℝ} {d : Ω' → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {ν : Ω' → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ᵐ ω ∂Q, ContinuousOn (fun p : ℝ × ℂ => d ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (c ω) (μ ω))
    (hν : ∀ᵐ ω ∂Q, IsLQGLimit γ (d ω) (ν ω))
    (hmμ : AEMeasurable μ P) (hmν : AEMeasurable ν Q)
    (hlaw : IdentDistrib (fun ω => circleProcess (c ω)) (fun ω => circleProcess (d ω)) P Q) :
    IdentDistrib (fun ω => (circleProcess (c ω), μ ω))
      (fun ω => (circleProcess (d ω), ν ω)) P Q := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  let I := Ioi (0 : ℝ) × ℂ
  let J := O ⊕ I
  let enc : ((I → ℝ) × Measure ℂ) → J → ℝ≥0∞ := fun p j =>
    match j with
    | .inl U => p.2 U.1
    | .inr i => ENNReal.ofReal (Real.exp (p.1 i))
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro j
    cases j with
    | inl U => exact (Measure.measurable_coe U.2.measurableSet).comp measurable_snd
    | inr i => exact (((measurable_pi_apply i).comp measurable_fst).exp).ennreal_ofReal
  let X : Ω → (I → ℝ) × Measure ℂ := fun ω => (circleProcess (c ω), μ ω)
  let Y : Ω' → (I → ℝ) × Measure ℂ := fun ω => (circleProcess (d ω), ν ω)
  have hXm : AEMeasurable X P := hlaw.aemeasurable_fst.prodMk hmμ
  have hYm : AEMeasurable Y Q := hlaw.aemeasurable_snd.prodMk hmν
  have hfin : ∀ F : Finset J, IdentDistrib (fun ω => F.restrict (enc (X ω)))
      (fun ω => F.restrict (enc (Y ω))) P Q := by
    intro F
    let U : F → Set ℂ := fun i => match i.1 with | .inl u => u.1 | .inr _ => ∅
    have hU : ∀ i, IsOpen (U i) := by
      intro i
      rcases i with ⟨j, hj⟩
      cases j with
      | inl u => exact u.2
      | inr i => exact isOpen_empty
    let decode : ((I → ℝ) × (F → ℝ≥0∞)) → F → ℝ≥0∞ := fun p i =>
      match i.1 with | .inl _ => p.2 i | .inr j => ENNReal.ofReal (Real.exp (p.1 j))
    have hdecode : Measurable decode := by
      apply Measurable.of_eval
      intro i
      rcases i with ⟨j, hj⟩
      cases j with
      | inl u => exact (measurable_pi_apply (⟨Sum.inl u, hj⟩ : F)).comp measurable_snd
      | inr i => exact (((measurable_pi_apply i).comp measurable_fst).exp).ennreal_ofReal
    have h := (identDistrib_circleProcess_openMasses_of_identDistrib hc hd hμ hν hlaw U hU).comp
      hdecode
    convert h using 1 <;> funext ω i <;> cases i with | mk j hj => cases j <;> rfl
  have hcode : IdentDistrib (enc ∘ X) (enc ∘ Y) P Q := by
    refine ⟨henc.comp_aemeasurable hXm, henc.comp_aemeasurable hYm, ?_⟩
    refine IsProjectiveLimit.unique
      (P := fun F : Finset J => Q.map (fun ω => F.restrict (enc (Y ω)))) ?_ ?_
    · intro F
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable
        (henc.comp_aemeasurable hXm)]
      exact (hfin F).map_eq
    · intro F
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable
        (henc.comp_aemeasurable hYm)]
      rfl
  let L := (I → ℝ) × {m : Measure ℂ // IsLocallyFiniteMeasure m}
  let e : L → J → ℝ≥0∞ := fun p => enc (p.1, p.2.1)
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hread : Measurable (fun p : L => (p.1, p.2.1)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      have hv := ((measurable_pi_apply (Sum.inr i : J)).comp (comap_measurable e)).ennreal_toReal
      have hv := hv.log
      simpa [e, enc, ENNReal.toReal_ofReal, (Real.exp_pos _).le] using hv
    · apply measurable_measure_of_isOpen (fun p : L => p.2.2)
      intro U hU
      exact (measurable_pi_apply (Sum.inl (⟨U, hU⟩ : O))).comp (comap_measurable e)
  refine ⟨hXm, hYm, ?_⟩
  apply Measure.ext
  intro S hS
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hread hS)
  have hpreX : X ⁻¹' S =ᵐ[P] (enc ∘ X) ⁻¹' T := by
    filter_upwards [hμ] with ω hω
    change (X ω ∈ S) = (enc (X ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨(X ω).1, ⟨μ ω, hω.isLocallyFiniteMeasure⟩⟩ : L)
    exact propext hh.symm
  have hpreY : Y ⁻¹' S =ᵐ[Q] (enc ∘ Y) ⁻¹' T := by
    filter_upwards [hν] with ω hω
    change (Y ω ∈ S) = (enc (Y ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨(Y ω).1, ⟨ν ω, hω.isLocallyFiniteMeasure⟩⟩ : L)
    exact propext hh.symm
  rw [Measure.map_apply_of_aemeasurable hXm hS,
    Measure.map_apply_of_aemeasurable hYm hS,
    measure_congr hpreX, measure_congr hpreY,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_fst hT,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_snd hT, hcode.map_eq]

end MatedCRT.FirstPass.Derived
