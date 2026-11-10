import MatedCRT.FirstPass.S5c.MarginIndex
import MatedCRT.FirstPass.S5c.MarginPositive
import MatedCRT.FirstPass.S5c.VersionField
import MatedCRT.FirstPass.S5c.IndexExact
import MatedCRT.FirstPass.S5c.EntranceScale
import MatedCRT.FirstPass.S5c.ClusterOpen
import MatedCRT.FirstPass.S5c.SuperBelow
import MatedCRT.FirstPass.S1c.TestDense

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), steps M5/M6): the exact positive margin `c` with `c ≤ w_t - 2 w_{t/2}`

Route (three-inputs section 2.4, M2 and the countable infimum over the Gaussian rationals):

* `exists_version_of_field` (M3): for each point `e`, the least supersolution `ω ↦ leastSupersolution (μ ω) ρ 0 u e` has an
  `S.fieldSigma`-measurable version, equal almost surely (`exists_measurable_leastSupersolution`, frozen input
  `FrozenUniversalMeasurabilityOfAnalytic` and the field measurability `FrozenLQGMeasureFieldMeasurable`).
* `idx_ae_eq_stopped`: a.s. on `{t < T}`, the exact closure index `idxSet` equals `closureIndex` of the open cluster.
* `exists_measurable_marginFn` (M5, MarginPositive.lean) gives the measurable positive modification `c` of the margin over the
  countable index `ratComplexNZ`; `margin_pathwise_closureIndex` (M4c) gives `c ω = marginInf ... ≤ w_t - 2 w_{t/2}` on `K_δ`.

Frozen inputs (hypotheses only): `FrozenLQGMeasureFieldMeasurable`, `FrozenUniversalMeasurabilityOfAnalytic`,
`FrozenDiskGreenNonnegCont`, `FrozenGreenDiscPole`, `FPStrongMinimumPrinciple`, and the cone-scaling inputs of EntranceScale.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric

/-- **Exact version, one point** (M3 for the field): for `e` in the closed ball of radius `R`, `e ≠ 0`, the value
`leastSupersolution (μ ω) R 0 u e` has an `m`-measurable version a.s.; for other `e` any measurable function will do. -/
theorem exists_version_of_field {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {P : Measure Ω} [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    {μ g : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hu : 0 < u)
    (hg : Measurable[m] g) (hμg : ∀ᵐ ω ∂P, μ ω = g ω) (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x) (e : ℂ) :
    ∃ v' : Ω → ℝ, Measurable[m] v' ∧
      (e ∈ closedBall (0 : ℂ) R → e ≠ 0 → ∀ᵐ ω ∂P, v' ω = leastSupersolution (μ ω) R 0 u e) := by
  by_cases he : e ∈ closedBall (0 : ℂ) R ∧ e ≠ 0
  · obtain ⟨v', hv', hae⟩ := exists_measurable_leastSupersolution hm hF1 hR hu hg hμg hμ φs hφs hdense hG he.1
      (ae_of_all _ fun ω => bddBelow_supersolution_values_of_ne_zero he.1 he.2)
    exact ⟨v', hv', fun _ _ => hae⟩
  · exact ⟨fun _ => 0, measurable_const, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩

/-- **A.s. identity of the exact index with the closure index** on the event `Q` (stopped case): the version of
`idx_ae_eq` (IndexExact.lean) where the openness of the cluster is only available on `Q` (`{t < T}`). -/
theorem idx_ae_eq_stopped {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ : Ω → Measure ℂ} {ρ t δ : ℝ}
    (hρ : 0 < ρ) {v : ℂ → Ω → ℝ} {Q : Ω → Prop}
    (hv : ∀ᵐ ω ∂P, ∀ e ∈ ratComplexNZ, e ∈ ball (0 : ℂ) ρ → v e ω = leastSupersolution (μ ω) ρ 0 t e)
    (hopen : ∀ᵐ ω ∂P, Q ω → IsOpen (cluster (μ ω) ρ 0 t)) :
    ∀ᵐ ω ∂P, Q ω → ∀ q : ℂ, ω ∈ idxSet ρ t δ v q ↔ q ∈ closureIndex (cluster (μ ω) ρ 0 t) ρ δ := by
  filter_upwards [hv, hopen] with ω hvω hopenω
  intro hQ q
  have hopenω := hopenω hQ
  have hpt : ∀ e ∈ ratComplex, ω ∈ ptSet ρ t v e ↔ e ∈ cluster (μ ω) ρ 0 t := fun e he =>
    ptSet_iff hρ (fun h0 hb => hvω e (Set.mem_sdiff_of_mem he (fun h => h0 (Set.mem_singleton_iff.1 h))) hb)
  have hdcl : ∀ d : ℂ, ω ∈ dclSet ρ t v d ↔ d ∈ closure (cluster (μ ω) ρ 0 t) := by
    intro d
    rw [mem_closure_iff_ratComplex hopenω d]
    simp only [dclSet, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · intro h n
      obtain ⟨e, he, hωe⟩ := h n
      exact ⟨e, he, (hpt e he.1).1 hωe⟩
    · intro h n
      obtain ⟨e, he, heC⟩ := h n
      exact ⟨e, he, (hpt e he.1).2 heC⟩
  constructor
  · rintro ⟨hq, r, hr, h⟩
    exact ⟨hq, r, hr, fun d hd hdr => (hdcl d).1 (h d hd hdr)⟩
  · rintro ⟨hq, r, hr, h⟩
    exact ⟨hq, r, hr, fun d hd hdr => (hdcl d).2 (h d hd hdr)⟩

/-- **Exact positive margin** (three-inputs (b), M5/M6, almost surely): under the hypotheses of `fixedIndexMargin_proved`
(the cone family, the field measurability, the frozen inputs), there is an `S.envSigma`-measurable `c > 0` such that,
almost surely on `{t < T}`, `c ω ≤ w_t x - 2 w_{t/2} x` for every `x` in the margin core `K_δ(ω)`. -/
theorem marginExact_proved {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple)
    (hL : ConeScaleInvarianceCodedStmt) (hpos : ConeScaleRadiusPosStep)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (ht : 0 < t) :
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x (Λ ω t)ᶜ →
        c ω ≤ leastSupersolution (S.μ ω) ρ 0 t x - 2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x := by
  have := hS.isProbabilityMeasure
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hscale : ∀ b t : ℝ, 0 < b → 0 < t → S.P (newEntranceEvent Λ (b * t)) = S.P (newEntranceEvent Λ t) :=
    fun b t hb ht => newEntrance_scale hγ0 hγ2 S.P S.hC S.hcirc S.μ hcone hL hpos Λ hΛ hb ht
  have hcover := cover_ae_all_of_scale S.P Λ (env_ae_open_monotone hΛ)
    (env_hmeas_ratDisc hF1 hF3 hG S hS (env_aemeasurable_test hF hγ0 hγ2 S hS) hΛ) hscale t ht
  obtain ⟨g, hg, hμg⟩ := hF γ hγ0 hγ2 Ω S hS
  obtain ⟨φs, hφs, hdense⟩ := exists_dense_nonnegTest_family ρ
  have hG0 := (hF3 ρ hρ).1
  have hμ := env_ae_mass_finite S hS ρ
  have hm := env_fieldSigma_le S hS
  have hvt := fun e : ℂ => exists_version_of_field (m := S.fieldSigma) hm hF1 hρ.le ht hg hμg hμ φs hφs hdense hG0 e
  have hvh := fun e : ℂ => exists_version_of_field (m := S.fieldSigma) hm hF1 hρ.le (half_pos ht) hg hμg hμ φs hφs
    hdense hG0 e
  choose vt hvtm hvtae using hvt
  choose vh hvhm hvhae using hvh
  have hDc : ratComplexNZ.Countable := ratComplex_countable.mono sdiff_subset
  have : Countable ratComplexNZ := hDc.to_subtype
  -- a.s. identities at the countably many Gaussian rationals `q ≠ 0`
  have hpt : ∀ (v : ℂ → Ω → ℝ) (u : ℝ) (hvae : ∀ e : ℂ, e ∈ closedBall (0 : ℂ) ρ → e ≠ 0 →
      ∀ᵐ ω ∂S.P, v e ω = leastSupersolution (S.μ ω) ρ 0 u e), ∀ e ∈ ratComplexNZ,
      ∀ᵐ ω ∂S.P, e ∈ ball (0 : ℂ) ρ → v e ω = leastSupersolution (S.μ ω) ρ 0 u e := by
    intro v u hvae e he
    by_cases hb : e ∈ ball (0 : ℂ) ρ
    · exact (hvae e (ball_subset_closedBall hb) (fun h0 => he.2 (Set.mem_singleton_iff.2 h0))).mono
        fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hb
  have hae_t : ∀ᵐ ω ∂S.P, ∀ e ∈ ratComplexNZ, e ∈ ball (0 : ℂ) ρ → vt e ω = leastSupersolution (S.μ ω) ρ 0 t e :=
    (ae_all_iff.2 fun e : ratComplexNZ => hpt vt t hvtae e e.2).mono fun ω hω e he hb => hω ⟨e, he⟩ hb
  have hae_h : ∀ᵐ ω ∂S.P, ∀ e ∈ ratComplexNZ, e ∈ ball (0 : ℂ) ρ →
      vh e ω = leastSupersolution (S.μ ω) ρ 0 (t / 2) e :=
    (ae_all_iff.2 fun e : ratComplexNZ => hpt vh (t / 2) hvhae e e.2).mono fun ω hω e he hb => hω ⟨e, he⟩ hb
  have hopen := ae_isOpen_cluster_of_stopped hG S.μ Λ hΛ hρ ht
  have hidx := idx_ae_eq_stopped (δ := δ) S.P hρ hae_t (Q := fun ω => t < clusterExitTime (Λ ω) ρ) hopen
  -- the margin and its positive measurable modification
  have hF_meas : ∀ q : ℂ, MeasurableSet[S.fieldSigma] (idxSet ρ t δ vt q) :=
    fun q => measurableSet_idxSet (fun e _ => hvtm e) q
  have hA_meas : ∀ q : ℂ, Measurable[S.fieldSigma] (fun ω => vt q ω - 2 * vh q ω) :=
    fun q => (hvtm q).sub ((hvhm q).const_mul 2)
  obtain ⟨c, hc, hcpos, hceq⟩ := exists_measurable_marginFn (m := S.fieldSigma) hDc
    (fun q => idxSet ρ t δ vt q) (fun q ω => vt q ω - 2 * vh q ω) hF_meas hA_meas
  refine ⟨c, hc.mono le_sup_left le_rfl, hcpos, ?_⟩
  have hcover' := hcover
  filter_upwards [hΛ, hcover', hae_t, hae_h, hidx] with ω hfam hcov hat hah hid hT x hx hxd
  obtain ⟨β, hβ, hmin1, hbound⟩ := margin_pathwise_closureIndex hmin hfam hρ hδ hT ht hcov
  have hmarg : marginFn ratComplexNZ (fun q => idxSet ρ t δ vt q) (fun q ω => vt q ω - 2 * vh q ω) ω =
      marginInf ratComplexNZ (closureIndex (HarmonicBalls.cluster (S.μ ω) ρ 0 t) ρ δ)
        (fun x => leastSupersolution (S.μ ω) ρ 0 t x - 2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x) := by
    refine marginFn_eq (fun q _ => hid hT q) (fun q hq hω => ?_)
    have hcl := (hid hT q).1 hω
    have hball : q ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.2 hcl.1
    rw [hat q hq hball, hah q hq hball]
  have hpos : 0 < marginFn ratComplexNZ (fun q => idxSet ρ t δ vt q) (fun q ω => vt q ω - 2 * vh q ω) ω := by
    rw [hmarg]
    exact lt_of_lt_of_le (lt_min one_pos hβ) hmin1
  rw [hceq ω hpos, hmarg]
  exact hbound x hx hxd

end MatedCRT.S5c
