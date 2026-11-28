import HarmonicBalls.Proofs.GFF.CoordinateModification
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.MarkedRootingFunction
import LatticeProb.LQG.MarkedRootingCov
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# Rooting the whole-plane GFF at a point sampled from its LQG measure

For the whole-plane Gaussian free field `h` and its `γ`-LQG measure `μ`, `0 < γ < 2`, the rooted law
`μ(dz) P(dh)` restricted to the unit disc has root marginal Lebesgue measure and, given the root `z`, field law the
original law shifted by `γ Cov(h(·), h(z))` (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
arXiv:0808.1560v2, §3.3, and the paragraph after Proposition 3.4; the conditional field is "the original GFF plus the
deterministic function" `γ ξ_0^z`). This is the rooting step in the proof that the coordinate change of the LQG
measure holds through the cone point.

* `lintegral_lqgMeasure_marked_countable_eq`: the marked rooting identity
  `E ∫_{𝔻} f(z, X) dμ(z) = ∫_{𝔻} E f(z, X + γ c(z)) dz` for countably many (indeed any family of) marks
  `X = ((h, φ_i))_i`, `c_i(z) = ∫ φ_i(x) Cov(h(x), h(z)) dx`; it extends the identity for finitely many marks
  (`LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasure_marked_fun_eq`) by the `π`-`λ` theorem on the products of
  measurable sets of roots with measurable cylinders of marks.
* `covDist x`: the distribution `T_x` of `y ↦ Cov(h(y), h(x))` (the kernel `wholePlaneCov`).
* `ae_measure_add_covDist_mem`: on the space of distributions with the law `ν` of a normalized whole-plane GFF,
  every measurable set `E` of full `ν`-measure satisfies `ν {g | g + γ T_x ∈ E} = 1` for Lebesgue-almost every `x` in
  the unit disc (rooting with the countably many coordinates that determine a distribution).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace LQGMeasureChart

open LatticeProb.Gauss in
/-- **The marked rooting identity for an arbitrary family of marks.** For a whole-plane GFF `h`, its `γ`-LQG measure
`μ` (`0 < γ < 2`), test functions `φ_i` (`i ∈ ι`) and a measurable `f : ℂ × ℝ^ι → [0, ∞]`,
`E ∫_{𝔻} f(z, X) dμ(z) = ∫_{𝔻} E f(z, X + γ c(z)) dz` with `X = ((h, φ_i))_i` and
`c_i(z) = ∫ φ_i(x) Cov(h(x), h(z)) dx` (Duplantier–Sheffield (2011), §3.3); the left integrand is almost everywhere
measurable. -/
theorem lintegral_lqgMeasure_marked_countable_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LatticeProb.LQG.IsLQGMeasure P γ hcirc μ)
    {ι : Type*} {φ : ι → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    {f : ℂ × (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in ball (0 : ℂ) 1, f (z, fun i => hC ω (φ i)) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, f (z, fun i => hC ω (φ i)) ∂(μ ω) ∂P =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
        f (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- the root shift
  set Y : ℂ × Ω → (ι → ℝ) := fun q i => hC q.2 (φ i) + γ * ∫ x, φ i x * wholePlaneCov x q.1 with hY
  have hYm : Measurable Y := measurable_pi_iff.2 fun i =>
    ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ)
  set F : ℂ × Ω → ℂ × (ι → ℝ) := fun q => (q.1, Y q) with hF
  have hFm : Measurable F := measurable_fst.prodMk hYm
  -- the two families of measures on `ℂ × ℝ^ι`
  let ν : Ω → Measure (ℂ × (ι → ℝ)) := fun ω =>
    ((μ ω).restrict (ball (0 : ℂ) 1)).map (fun z => (z, fun i => hC ω (φ i)))
  let ρ : Measure (ℂ × (ι → ℝ)) := ((volume.restrict (ball (0 : ℂ) 1)).prod P).map F
  have hνS : ∀ ω, ∀ T : Set (ℂ × (ι → ℝ)), MeasurableSet T → ν ω T =
      ∫⁻ z in ball (0 : ℂ) 1, T.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (φ i)) ∂(μ ω) := by
    intro ω T hT
    have hmk : Measurable fun z : ℂ => (z, fun i => hC ω (φ i)) := measurable_id.prodMk measurable_const
    simp only [ν]
    rw [Measure.map_apply hmk hT, ← lintegral_indicator_one (hmk hT)]
    refine lintegral_congr fun z => ?_
    by_cases hz : (z, fun i => hC ω (φ i)) ∈ T <;> simp [Set.indicator, hz]
  have hρS : ∀ T : Set (ℂ × (ι → ℝ)), MeasurableSet T → ρ T =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, T.indicator (fun _ => (1 : ℝ≥0∞))
        (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
    intro T hT
    simp only [ρ]
    rw [Measure.map_apply hFm hT, ← lintegral_indicator_one (hFm hT),
      lintegral_prod _ ((measurable_one.indicator (hFm hT)).aemeasurable)]
    refine lintegral_congr fun z => lintegral_congr fun ω => ?_
    by_cases hz : (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∈ T
    · have hz' : (z, ω) ∈ F ⁻¹' T := hz
      simp [Set.indicator, hz, hz']
    · have hz' : (z, ω) ∉ F ⁻¹' T := hz
      simp [Set.indicator, hz, hz']
  -- the `π`-system of products of measurable sets of roots with measurable cylinders of marks
  let Sys : Set (Set (ℂ × (ι → ℝ))) :=
    Set.image2 (· ×ˢ ·) {A : Set ℂ | MeasurableSet A} (measurableCylinders fun _ : ι => ℝ)
  have hpi : IsPiSystem Sys := IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet isPiSystem_measurableCylinders
  have huniv : (Set.univ : Set (ℂ × (ι → ℝ))) ∈ Sys :=
    ⟨(Set.univ : Set ℂ), (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℂ)), (Set.univ : Set (ι → ℝ)),
      univ_mem_measurableCylinders _, Set.univ_prod_univ⟩
  have hgen : (inferInstance : MeasurableSpace (ℂ × (ι → ℝ))) = MeasurableSpace.generateFrom Sys := by
    have h := generateFrom_prod_eq (C := {s : Set ℂ | MeasurableSet s})
      (D := measurableCylinders fun _ : ι => ℝ) isCountablySpanning_measurableSet
      ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩
    rw [MeasurableSpace.generateFrom_measurableSet, generateFrom_measurableCylinders] at h
    exact h
  -- the base case: a cylinder over a finite set of marks reduces to finitely many marks
  have hbase : ∀ s ∈ Sys, AEMeasurable (fun ω => ν ω s) P ∧ ∫⁻ ω, ν ω s ∂P = ρ s := by
    rintro s ⟨A, hA, C, hC', rfl⟩
    obtain ⟨t, B, hB, hCeq⟩ := (mem_measurableCylinders C).1 hC'
    replace hA : MeasurableSet A := hA
    set e : t ≃ Fin t.card := t.equivFin with he
    set R : (Fin t.card → ℝ) → (t → ℝ) := fun w i => w (e i) with hR
    have hRm : Measurable R := measurable_pi_iff.2 fun i => measurable_pi_apply _
    set S' : Set (ℂ × (Fin t.card → ℝ)) := A ×ˢ (R ⁻¹' B) with hS'
    have hS'm : MeasurableSet S' := hA.prod (hRm hB)
    have hs : MeasurableSet (A ×ˢ C) := hA.prod (MeasurableSet.of_mem_measurableCylinders hC')
    have hind : ∀ (z : ℂ) (v : ι → ℝ), (A ×ˢ C).indicator (fun _ => (1 : ℝ≥0∞)) (z, v) =
        S'.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun k => v (e.symm k)) := by
      intro z v
      have hRv : R (fun k => v (e.symm k)) = t.restrict v :=
        funext fun i => congrArg v (congrArg Subtype.val (e.symm_apply_apply i))
      have hmem : (z, v) ∈ A ×ˢ C ↔ (z, fun k => v (e.symm k)) ∈ S' := by
        simp only [hS', Set.mem_prod, hCeq, mem_cylinder, Set.mem_preimage, hRv]
      by_cases h : (z, v) ∈ A ×ˢ C
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (hmem.2 h')]
    have h5 := hh.lintegral_lqgMeasure_marked_eq_of_measurableSet hγ0 hγ2 hμ
      (φ := fun k => φ (e.symm k)) (fun k => hφ _) hS'm
    refine ⟨h5.1.congr (Filter.Eventually.of_forall fun ω =>
      ((hνS ω _ hs).trans (lintegral_congr fun z => hind z (fun i => hC ω (φ i)))).symm), ?_⟩
    calc ∫⁻ ω, ν ω (A ×ˢ C) ∂P
        = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, S'.indicator (fun _ => (1 : ℝ≥0∞))
            (z, fun k => hC ω (φ (e.symm k))) ∂(μ ω) ∂P :=
          lintegral_congr fun ω =>
            (hνS ω _ hs).trans (lintegral_congr fun z => hind z (fun i => hC ω (φ i)))
      _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, S'.indicator (fun _ => (1 : ℝ≥0∞))
            (z, fun k => hC ω (φ (e.symm k)) + γ * ∫ x, φ (e.symm k) x * wholePlaneCov x z) ∂P := h5.2
      _ = ρ (A ×ˢ C) := by
          rw [hρS _ hs]
          exact lintegral_congr fun z => lintegral_congr fun ω =>
            (hind z (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)).symm
  have hsets := LatticeProb.aemeasurable_and_lintegral_eq_of_isPiSystem (P := P) ν ρ hgen hpi huniv hbase
  have key := LatticeProb.aemeasurable_and_lintegral_eq_of_forall_measurableSet (P := P) ν ρ hsets f hf
  have hνg : ∀ ω, ∫⁻ y, f y ∂(ν ω) = ∫⁻ z in ball (0 : ℂ) 1, f (z, fun i => hC ω (φ i)) ∂(μ ω) := fun ω => by
    simp only [ν]
    exact lintegral_map hf (measurable_id.prodMk measurable_const)
  have hρg : ∫⁻ y, f y ∂ρ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
      f (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
    simp only [ρ]
    rw [lintegral_map hf hFm]
    exact lintegral_prod (fun q => f (F q)) (hf.comp hFm).aemeasurable
  refine ⟨key.1.congr (Filter.Eventually.of_forall fun ω => hνg ω), ?_⟩
  rw [← hρg, ← key.2]
  exact lintegral_congr fun ω => (hνg ω).symm

/-- The distribution `φ ↦ ∫ φ f` of a function `f` on `ℂ` (the zero distribution if `f` is not locally integrable). -/
def distOfFun (f : ℂ → ℝ) : LQGMetric.DistC :=
  Distribution.ofFun ⊤ f volume ⊤

theorem distOfFun_apply {f : ℂ → ℝ} (hf : LocallyIntegrable f) (φ : LQGMetric.TestC) :
    distOfFun f φ = ∫ y, φ y * f y := by
  rw [distOfFun, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  simp only [smul_eq_mul]

/-- `T_x`: the distribution of the covariance kernel `y ↦ Cov(h(y), h(x)) = wholePlaneCov y x` of the whole-plane
GFF normalized to have vanishing unit-circle average. -/
def covDist (x : ℂ) : LQGMetric.DistC :=
  distOfFun fun y => LatticeProb.Gauss.wholePlaneCov y x

/-- The covariance kernel `y ↦ wholePlaneCov y x = log⁺|y| + log⁺|x| - log|y - x|` is locally integrable. -/
theorem locallyIntegrable_wholePlaneCov_left (x : ℂ) :
    LocallyIntegrable fun y => LatticeProb.Gauss.wholePlaneCov y x := by
  have h1 : LocallyIntegrable (fun y : ℂ => Real.log ‖y - x‖) :=
    LatticeProb.LQG.AffineDerived.locallyIntegrable_comp_sub_of_integrableOn_ball
      (f := fun y : ℂ => Real.log ‖y‖) LatticeProb.LQG.AffineDerived.integrableOn_ball_log_norm x
  have h2 : LocallyIntegrable (fun y => LatticeProb.Gauss.wholePlaneNormalization y +
      LatticeProb.Gauss.wholePlaneNormalization x - Real.log ‖y - x‖) :=
    ((LatticeProb.Gauss.continuous_wholePlaneNormalization.add continuous_const).locallyIntegrable).sub h1
  refine h2.congr ?_
  have hne : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with y hy
  rw [LatticeProb.Gauss.wholePlaneCov_eq_normalization_add hy, norm_sub_rev]

theorem covDist_apply (x : ℂ) (φ : LQGMetric.TestC) :
    covDist x φ = ∫ y, φ y * LatticeProb.Gauss.wholePlaneCov y x :=
  distOfFun_apply (locallyIntegrable_wholePlaneCov_left x) φ

open LatticeProb.Gauss in
/-- **Rooting on the canonical space.** Let `ν` be the law, on the space of distributions on `ℂ`, of a normalized
whole-plane GFF (`IsNormalizedWPGFF id ν`), and `0 < γ < 2`. If a measurable set `E` of distributions has full
`ν`-measure, then for Lebesgue-almost every `x` in the unit disc the shifted field `g + γ T_x` lies in `E` for
`ν`-almost every `g` (Duplantier–Sheffield (2011), §3.3: the field seen from a root sampled from its LQG measure is the
original field plus `γ Cov(h(·), h(x))`). -/
theorem ae_measure_add_covDist_mem {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν]
    (hν : LQGMetric.IsNormalizedWPGFF id ν) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {E : Set LQGMetric.DistC} (hE : MeasurableSet E) (hE1 : ν E = 1) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) 1)), ν {g | g + γ • covDist x ∈ E} = 1 := by
  obtain ⟨hC, hcirc, hg, hp, -⟩ := HarmonicBalls.normalizedGFF_exists_projectGFF hν
  have hgff := (HarmonicBalls.LPBridge.isWholePlaneGFF_iff ν hC hcirc).1 hg
  obtain ⟨μ, hμ⟩ := hgff.exists_isLQGMeasure hγ0 hγ2
  have hJ : MeasurableEmbedding (LQGMetric.pairJ (⊤ : TopologicalSpace.Opens ℂ)) :=
    LQGMetric.measurableEmbedding_pairJ ⊤
  set Fs : Set (LQGMetric.CoordJ → ℝ) := LQGMetric.pairJ ⊤ '' E with hFs
  have hFm : MeasurableSet Fs := hJ.measurableSet_image' hE
  set φ : LQGMetric.CoordJ → ℂ → ℝ := fun c => ⇑(LQGMetric.comb ⊤ c) with hφdef
  have hφ : ∀ c, IsTestFunction Set.univ (φ c) := fun c =>
    ⟨(LQGMetric.comb ⊤ c).contDiff, (LQGMetric.comb ⊤ c).hasCompactSupport, Set.subset_univ _⟩
  set f : ℂ × (LQGMetric.CoordJ → ℝ) → ℝ≥0∞ := fun p => Fsᶜ.indicator (fun _ => 1) p.2 with hfdef
  have hf : Measurable f := (measurable_const.indicator hFm.compl).comp measurable_snd
  obtain ⟨-, hrt⟩ := lintegral_lqgMeasure_marked_countable_eq hgff hγ0 hγ2 hμ hφ hf
  -- the marks are the coordinates `pairJ` of the field and of the shifted field
  have hX : ∀ g : LQGMetric.DistC, (fun c => hC g (φ c)) = LQGMetric.pairJ ⊤ g := fun g =>
    funext fun c => hp g (LQGMetric.comb ⊤ c)
  have hshift : ∀ (g : LQGMetric.DistC) (z : ℂ),
      (fun c => hC g (φ c) + γ * ∫ x, φ c x * wholePlaneCov x z) = LQGMetric.pairJ ⊤ (g + γ • covDist z) :=
    fun g z => funext fun c => by
      have h1 : hC g (φ c) = g (LQGMetric.comb ⊤ c) := hp g (LQGMetric.comb ⊤ c)
      have h2 : covDist z (LQGMetric.comb ⊤ c) = ∫ x, φ c x * wholePlaneCov x z := covDist_apply z _
      show hC g (φ c) + γ * ∫ x, φ c x * wholePlaneCov x z =
        g (LQGMetric.comb ⊤ c) + γ • covDist z (LQGMetric.comb ⊤ c)
      rw [h1, h2, smul_eq_mul]
  have hmeasT : ∀ z, Measurable fun g : LQGMetric.DistC => g + γ • covDist z := fun z =>
    LQGMetric.measurable_distOn_iff.2 fun ψ => by
      show Measurable fun g : LQGMetric.DistC => g ψ + (γ • covDist z) ψ
      exact (LQGMetric.measurable_distOn_apply ψ).add measurable_const
  have hmeas : ∀ z, MeasurableSet {g : LQGMetric.DistC | g + γ • covDist z ∈ E} := fun z => hmeasT z hE
  -- the left side vanishes, since the field lies in `E` almost surely
  have hEc : ν Eᶜ = 0 := (prob_compl_eq_zero_iff hE).2 hE1
  have hae : ∀ᵐ g ∂ν, g ∈ E := ae_iff.2 hEc
  have hlhs : ∫⁻ g, ∫⁻ z in ball (0 : ℂ) 1, f (z, fun c => hC g (φ c)) ∂(μ g) ∂ν = 0 := by
    refine (lintegral_congr_ae ?_).trans (lintegral_zero (μ := ν))
    filter_upwards [hae] with g hg
    have h0 : ∀ z, f (z, fun c => hC g (φ c)) = 0 := fun z => by
      simp only [hfdef, hX g]
      exact Set.indicator_of_notMem (fun (h : LQGMetric.pairJ ⊤ g ∈ Fsᶜ) => h ⟨g, hg, rfl⟩) _
    simp [h0]
  -- the right side is the integral of the probability that the shifted field leaves `E`
  have hpt : ∀ z, ∫⁻ g, f (z, fun c => hC g (φ c) + γ * ∫ x, φ c x * wholePlaneCov x z) ∂ν =
      ν {g | g + γ • covDist z ∈ E}ᶜ := fun z => by
    rw [← lintegral_indicator_one (hmeas z).compl]
    refine lintegral_congr fun g => ?_
    simp only [hfdef, hshift g z]
    by_cases hg : g + γ • covDist z ∈ E
    · have h1 : LQGMetric.pairJ ⊤ (g + γ • covDist z) ∈ Fs := ⟨_, hg, rfl⟩
      have h2 : g ∉ {g | g + γ • covDist z ∈ E}ᶜ := fun h => h hg
      rw [Set.indicator_of_notMem (fun (h : LQGMetric.pairJ ⊤ (g + γ • covDist z) ∈ Fsᶜ) => h h1),
        Set.indicator_of_notMem h2]
    · have h1 : LQGMetric.pairJ ⊤ (g + γ • covDist z) ∉ Fs := by
        rintro ⟨g', hg', he⟩
        exact hg (by rw [← hJ.injective he]; exact hg')
      have h2 : g ∈ {g | g + γ • covDist z ∈ E}ᶜ := hg
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
  have h0 : ∫⁻ z in ball (0 : ℂ) 1, ν {g | g + γ • covDist z ∈ E}ᶜ = 0 :=
    calc ∫⁻ z in ball (0 : ℂ) 1, ν {g | g + γ • covDist z ∈ E}ᶜ
        = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ g,
            f (z, fun c => hC g (φ c) + γ * ∫ x, φ c x * wholePlaneCov x z) ∂ν :=
          lintegral_congr fun z => (hpt z).symm
      _ = ∫⁻ g, ∫⁻ z in ball (0 : ℂ) 1, f (z, fun c => hC g (φ c)) ∂(μ g) ∂ν := hrt.symm
      _ = 0 := hlhs
  have hGm : Measurable fun q : ℂ × LQGMetric.DistC =>
      f (q.1, fun c => hC q.2 (φ c) + γ * ∫ x, φ c x * wholePlaneCov x q.1) :=
    hf.comp (measurable_fst.prodMk (measurable_pi_iff.2 fun c =>
      ((hgff.measurable_pairing _ (hφ c)).comp measurable_snd).add
        (((measurable_integral_mul_wholePlaneCov (hφ c)).comp measurable_fst).const_mul γ)))
  have hAm : AEMeasurable (fun z => ν {g | g + γ • covDist z ∈ E}ᶜ) (volume.restrict (ball (0 : ℂ) 1)) :=
    (hGm.lintegral_prod_right' (ν := ν)).aemeasurable.congr (Filter.Eventually.of_forall hpt)
  filter_upwards [(lintegral_eq_zero_iff' hAm).1 h0] with z hz
  exact (prob_compl_eq_zero_iff (hmeas z)).1 hz

end LQGMeasureChart

end MatedCRT
