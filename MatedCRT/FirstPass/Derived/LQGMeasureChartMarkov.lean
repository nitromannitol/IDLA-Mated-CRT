import MatedCRT.FirstPass.Derived.LQGMeasureChartMarkovCircle
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal

/-!
# The field on a disc: a zero-boundary GFF plus a continuous function

The first localization step of the coordinate change of the LQG measure for all inverse charts: on a disc `D`,
the field is a zero-boundary GFF on `D` plus a continuous function, and the circle averages of the field are those
of the zero-boundary GFF (a continuous circle-average process in the sense of Sheffield–Wang, arXiv:1605.06171v2,
Proposition 2.4 and p. 10) plus the circle averages of the continuous function. This is what allows the
Sheffield–Wang theorems, stated for a zero-boundary GFF on a disc, to be applied to the field of a valid
environment (Duplantier–Sheffield, arXiv:0808.1560v2, §3.1 for the circle averages).

* `MatedCRT.LQGMeasureChart.exists_discMarkovDecomposition_wholePlane`: for a whole-plane GFF `X` and **any** disc
  `B(c, r)`, there are a zero-boundary GFF `X_B` on the disc, a random function `u_B` continuous on the disc and a
  continuous circle-average process `h_B` of `X_B` (`IsCircleProcess`) such that almost surely `X = X_B + u_B` on the
  disc and `X_s(z) = h_B(s, z) + ⨍_{∂B(z,s)} u_B` for every closed disc `B̄(z, s)` inside `B(c, r)`. The
  decomposition is the Markov property of the whole-plane GFF (Gwynne–Miller–Sheffield, arXiv:1807.07511, Lemma 2.2,
  `LQGMetric.DFGPS.markov_normAt` with `LQGMetric.MarkovFinal.lmLem2_1`), applied with the normalization circle
  `∂B(c, 2r)`; the circle-average identity is the radial identity of
  `MatedCRT.LQGMeasureChart.pairFun_sub_eq_intervalIntegral`.
* `MatedCRT.MatedCRTEnv.IsValid.exists_discMarkovDecomposition`: for a valid environment with `0 < γ < 2`, a
  measurable version `H` of its field and a disc avoiding the cone point `0`, the same decomposition of `H`, with the
  circle averages `S.hcirc` of the environment. The field is the circle-average embedding of the `γ`-quantum cone,
  `X − X_{|·|}(0) + A_{-log |·|}` (Duplantier–Miller–Sheffield, arXiv:1409.7055, Definition 4.10), and its two radial
  profiles are continuous off `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Real NNReal

namespace MatedCRT

namespace LQGMeasureChart

open LQGMetric MatedCRTHarmonic.LQGCoord MatedCRT.ConeAreaCovariance

/-- `∫ (f − g + h) φ = ∫ f φ − ∫ g φ + ∫ h φ` for integrable products. -/
theorem integral_sub_add_mul {f g h φ : ℂ → ℝ} (hf : Integrable fun x => f x * φ x)
    (hg : Integrable fun x => g x * φ x) (hh : Integrable fun x => h x * φ x) :
    ∫ x, (f x - g x + h x) * φ x = (∫ x, f x * φ x) - (∫ x, g x * φ x) + ∫ x, h x * φ x := by
  have e : (fun x => (f x - g x + h x) * φ x) = fun x => (f x * φ x - g x * φ x) + h x * φ x :=
    funext fun x => by ring
  rw [e, integral_add (f := fun x => f x * φ x - g x * φ x) (hf.sub hg) hh]
  congr 1
  exact integral_sub hf hg

/-- **The field of a whole-plane GFF on a disc** (Markov property; Gwynne–Miller–Sheffield, arXiv:1807.07511,
Lemma 2.2). For a whole-plane GFF `X` and a disc `B(c, r)` there are a zero-boundary GFF `Xz` on the disc, a random
function `u`, almost surely continuous on the disc, and a process `hc` such that almost surely `X = Xz + u` on the
disc, `hc` is a continuous circle-average process of `Xz` (`IsCircleProcess`), and
`X_s(z) = hc(s, z) + ⨍_{∂B(z,s)} u` for every closed disc `B̄(z, s) ⊆ B(c, r)`. -/
theorem exists_discMarkovDecomposition_wholePlane {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ (Xz : Ω → DistOn (disc c r)) (u : Ω → ℂ → ℝ) (hc : Ω → ℝ → ℂ → ℝ),
      LQGMetric.IsZeroBoundaryGFF (disc c r) Xz P ∧
      (∀ᵐ ω ∂P, ContinuousOn (u ω) (ball c r)) ∧
      (∀ᵐ ω ∂P, ∀ φ : TestOn (disc c r),
        restrictTo (disc c r) (X ω) φ = Xz ω φ + ∫ x, u ω x * φ x) ∧
      (∀ᵐ ω ∂P, IsCircleProcess c r (Xz ω) (hc ω)) ∧
      (∀ᵐ ω ∂P, ∀ (s : ℝ) (z : ℂ), 0 < s → closedBall z s ⊆ ball c r →
        circleAvg (X ω) s z = hc ω s z + Real.circleAverage (u ω) z s) := by
  classical
  have : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have h2r : (0 : ℝ) < 2 * r := by positivity
  obtain ⟨hX', hn⟩ := LQGMetric.DFGPS.isNormalizedAt_recenter hX h2r c
  have hV : Disjoint ((disc c r : TopologicalSpace.Opens ℂ) : Set ℂ) (sphere c (2 * r)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : dist x c < r := hx
    have h2 : dist x c = 2 * r := hx'
    linarith
  obtain ⟨hh, hz, hsum, hharm, -, -, hzb, -, -⟩ := LQGMetric.DFGPS.markov_normAt
    LQGMetric.MarkovFinal.lmLem2_1 P _ hX' h2r c hn (disc c r) hV
  -- the harmonic part as a function
  obtain ⟨G, hGdef⟩ : ∃ G : Ω → ℂ → ℝ, ∀ ω, G ω =
      if h : ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g ((disc c r : TopologicalSpace.Opens ℂ) : Set ℂ) ∧
        ∀ φ : TestOn (disc c r), restrictTo (disc c r) (hh ω) φ = ∫ x, g x * φ x
      then h.choose else 0 := ⟨_, fun _ => rfl⟩
  have hG : ∀ᵐ ω ∂P,
      InnerProductSpace.HarmonicOnNhd (G ω) ((disc c r : TopologicalSpace.Opens ℂ) : Set ℂ) ∧
        ∀ φ : TestOn (disc c r), restrictTo (disc c r) (hh ω) φ = ∫ x, G ω x * φ x := by
    filter_upwards [hharm] with ω hω
    rw [hGdef ω, dite_eq_left hω]
    exact hω.choose_spec
  -- the continuous part: the harmonic part plus the normalizing constant
  obtain ⟨u, hudef⟩ : ∃ u : Ω → ℂ → ℝ, ∀ ω x, u ω x = G ω x + circleAvg (X ω) (2 * r) c :=
    ⟨_, fun _ _ => rfl⟩
  have hucont : ∀ᵐ ω ∂P, ContinuousOn (u ω) (ball c r) := by
    filter_upwards [hG] with ω hω
    have h1 : ContinuousOn (fun x => G ω x + circleAvg (X ω) (2 * r) c) (ball c r) :=
      hω.1.continuousOn.add continuousOn_const
    exact h1.congr fun x _ => hudef ω x
  have hdec : ∀ᵐ ω ∂P, ∀ φ : TestOn (disc c r),
      restrictTo (disc c r) (X ω) φ = restrictTo (disc c r) (hz ω) φ + ∫ x, u ω x * φ x := by
    filter_upwards [hG] with ω hω φ
    let ψ : TestC := ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
    have hψ : ∀ x, ψ x = φ x := fun _ => rfl
    rw [restrictTo_apply_eq_of_coe _ φ ψ hψ, restrictTo_apply_eq_of_coe _ φ ψ hψ]
    have hgφ := hω.2 φ
    rw [restrictTo_apply_eq_of_coe _ φ ψ hψ] at hgφ
    have hs := congrArg (fun T : DistC => T ψ) (hsum ω)
    simp only [addConst, addFun, add_apply, ofCont_apply, ContinuousMap.const_apply,
      hψ] at hs
    have hi1 : Integrable fun x => G ω x * φ x :=
      integrable_mul_testOn_of_continuousOn hω.1.continuousOn φ
    have hi2 : Integrable fun x => φ x := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have e1 : ∫ x, u ω x * φ x = (∫ x, G ω x * φ x) + circleAvg (X ω) (2 * r) c * ∫ x, φ x := by
      rw [← integral_const_mul, ← integral_add hi1 (hi2.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hudef]
      ring
    have e2 : ∫ x, φ x * -circleAvg (X ω) (2 * r) c = -(circleAvg (X ω) (2 * r) c * ∫ x, φ x) := by
      rw [integral_mul_const]
      ring
    rw [e2] at hs
    rw [e1, ← hgφ]
    linarith
  -- the zero-boundary part and its circle-average process
  refine ⟨fun ω => restrictTo (disc c r) (hz ω), u,
    fun ω s z => circleAvg (X ω) s z - Real.circleAverage (u ω) z s, hzb, hucont, hdec, ?_,
    Eventually.of_forall fun ω s z _ _ => (sub_add_cancel _ _).symm⟩
  filter_upwards [hucont, hdec, ae_scaleRegular_wp hX, ae_abs_circleAvg_le_log hX] with ω hu hd hsr hlog
  refine ⟨?_, fun z ε hε hzε v hv hvrad hvs =>
    pairFun_sub_eq_intervalIntegral hsr hlog hu hd hε hzε hv hvrad hvs⟩
  have h1 : ContinuousOn (fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2)
      {p : ℝ × ℂ | 0 < p.1 ∧ closedBall p.2 p.1 ⊆ ball c r} :=
    (continuousOn_circleAvg_of_scaleRegular hsr).mono fun p hp => ⟨hp.1, mem_univ _⟩
  have h2 : ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (u ω) p.2 p.1)
      {p : ℝ × ℂ | 0 < p.1 ∧ closedBall p.2 p.1 ⊆ ball c r} :=
    (continuousOn_circleAverage_of_continuousOn hu).mono fun p hp => ⟨hp.1.le, hp.2⟩
  exact h1.sub h2

end LQGMeasureChart

open LQGMeasureChart LQGMetric MatedCRTHarmonic.LQGCoord MatedCRT.ConeAreaCovariance in
/-- **The field of a valid environment on a disc avoiding the cone point** (first localization step of the
coordinate change of the LQG measure). For a valid environment with `0 < γ < 2`, a measurable version `H` of its
field and a disc `B(c, r)` whose closure avoids `0`, there are a zero-boundary GFF `X` on the disc, a random
function `u`, almost surely continuous on the disc, and a process `hc` such that almost surely `H = X + u` on the
disc, `hc` is a continuous circle-average process of `X` (`IsCircleProcess`), and the circle averages of the
environment are `S.hcirc(s, z) = hc(s, z) + ⨍_{∂B(z,s)} u` for every closed disc `B̄(z, s) ⊆ B(c, r)`. -/
theorem MatedCRTEnv.IsValid.exists_discMarkovDecomposition {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {H : Ω → DistC} (hH : ∀ᵐ ω ∂S.P, ∀ φ : TestC, S.hC ω φ = H ω φ) (c : ℂ) {r : ℝ}
    (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∃ (X : Ω → DistOn (disc c r)) (u : Ω → ℂ → ℝ) (hc : Ω → ℝ → ℂ → ℝ),
      LQGMetric.IsZeroBoundaryGFF (disc c r) X S.P ∧
      (∀ᵐ ω ∂S.P, ContinuousOn (u ω) (ball c r)) ∧
      (∀ᵐ ω ∂S.P, ∀ φ : TestOn (disc c r),
        restrictTo (disc c r) (H ω) φ = X ω φ + ∫ x, u ω x * φ x) ∧
      (∀ᵐ ω ∂S.P, IsCircleProcess c r (X ω) (hc ω)) ∧
      (∀ᵐ ω ∂S.P, ∀ (s : ℝ) (z : ℂ), 0 < s → closedBall z s ⊆ ball c r →
        S.hcirc ω s z = hc ω s z + Real.circleAverage (u ω) z s) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hX := hcpl.gff
  have hαQ : γ < MatedCRTHarmonic.CellScaling.lqgQ γ := by
    show γ < 2 / γ + γ / 2
    have h4 : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ]
      nlinarith
    linarith
  obtain ⟨Xz, u, hc, hzb, hucont, hdec, hcirc, hid⟩ :=
    exists_discMarkovDecomposition_wholePlane hX c hr
  have hsub : ball c r ⊆ ({0}ᶜ : Set ℂ) := fun x hx hx0 => h0 (by
    rw [mem_singleton_iff] at hx0
    rw [← hx0]
    exact ball_subset_closedBall hx)
  have hgood := ae_radialGood hX hcpl.bm_B hcpl.bm_B' hαQ
  -- the field is the cone field, written with its two radial profiles
  have hcone : ∀ᵐ ω ∂S.P, H ω = X ω - MatedCRTHarmonic.CellScaling.ofFunC
      (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) + MatedCRTHarmonic.CellScaling.ofFunC
      (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) := by
    filter_upwards [hae, hH] with ω hω hHω
    refine (DFunLike.ext _ _ fun φ => ?_).trans
      (coneField_eq_cone γ γ (X ω) (fun t => B t ω) (fun t => B' t ω))
    rw [← hHω φ]
    exact hω.2 φ
  -- local integrability of the profiles
  have hloc : ∀ ω, RadialGood γ γ (X ω) (fun t => B t ω) (fun t => B' t ω) →
      LocallyIntegrable (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) volume ∧
        LocallyIntegrable (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) volume := by
    intro ω hg
    obtain ⟨C₁, hC₁⟩ := abs_radialAvg_le hg one_pos
    obtain ⟨C₂, hC₂⟩ := abs_coneProfile_le hg one_pos
    exact ⟨locallyIntegrable_of_logBound (measurable_radialAvg (X ω)) (continuousOn_radialAvg hg.good) hC₁,
      locallyIntegrable_of_logBound (measurable_coneProfile hg) (continuousOn_coneProfile hg)
        fun w hw0 hw1 => (hC₂ w hw0 hw1).1⟩
  refine ⟨Xz, fun ω x => u ω x - MatedCRTHarmonic.CellScaling.radialAvg (X ω) x +
      coneProfile γ γ (fun t => B t ω) (fun t => B' t ω) x, hc, hzb, ?_, ?_, hcirc, ?_⟩
  · -- continuity
    filter_upwards [hucont, hgood] with ω hu hg
    exact (hu.sub ((continuousOn_radialAvg hg.good).mono hsub)).add
      ((continuousOn_coneProfile hg).mono hsub)
  · -- the decomposition of the pairings
    filter_upwards [hdec, hcone, hgood, hucont] with ω hd hco hg hu φ
    obtain ⟨hl₁, hl₂⟩ := hloc ω hg
    let ψ : TestC := ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
    have hψ : ∀ x, ψ x = φ x := fun _ => rfl
    have hXφ := hd φ
    rw [restrictTo_apply_eq_of_coe _ φ ψ hψ] at hXφ
    rw [hco, restrictTo_apply_eq_of_coe _ φ ψ hψ, add_apply,
      sub_apply, ofFunC_apply_li hl₁, ofFunC_apply_li hl₂, hXφ,
      integral_sub_add_mul (integrable_mul_testOn_of_continuousOn hu φ)
        (integrable_mul_testOn_of_continuousOn ((continuousOn_radialAvg hg.good).mono hsub) φ)
        (integrable_mul_testOn_of_continuousOn ((continuousOn_coneProfile hg).mono hsub) φ)]
    have e₁ : ∫ x, ψ x * MatedCRTHarmonic.CellScaling.radialAvg (X ω) x =
        ∫ x, MatedCRTHarmonic.CellScaling.radialAvg (X ω) x * φ x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have e₂ : ∫ x, ψ x * coneProfile γ γ (fun t => B t ω) (fun t => B' t ω) x =
        ∫ x, coneProfile γ γ (fun t => B t ω) (fun t => B' t ω) x * φ x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [e₁, e₂]
    ring
  · -- the circle averages of the environment
    have hOo : IsOpen {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} :=
      (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt ((continuous_snd.dist continuous_const).add continuous_fst) continuous_const)
    have hOsub : ∀ p ∈ {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r}, closedBall p.2 p.1 ⊆ ball c r :=
      fun p hp => (closedBall_subset_ball_iff_dist_add_lt hp.1.le).2 hp.2
    have hOne : ∀ p ∈ {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r}, ‖p.2‖ ≠ p.1 := fun p hp he =>
      h0 (ball_subset_closedBall (hOsub p hp (by rw [mem_closedBall, dist_zero_left, he])))
    have hOz : ∀ p ∈ {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r},
        closedBall p.2 p.1 ⊆ ({0}ᶜ : Set ℂ) := fun p hp => (hOsub p hp).trans hsub
    have hEq : ∀ᵐ ω ∂S.P, EqOn (fun p : ℝ × ℂ => S.hcirc ω p.1 p.2)
        (fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2 -
          Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) p.2 p.1 +
          Real.circleAverage (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) p.2 p.1)
        {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} := by
      refine ae_eqOn_of_continuousOn hOo ?_ ?_ fun p hp => ?_
      · filter_upwards [hS.isQuantumCone.ae_continuousOn_circle] with ω hω
        exact hω.mono fun p hp => ⟨hp.1, mem_univ _⟩
      · filter_upwards [hgood, ae_scaleRegular_wp hX] with ω hg hsr
        have h1 : ContinuousOn (fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2)
            {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} :=
          (continuousOn_circleAvg_of_scaleRegular hsr).mono fun p hp => ⟨hp.1, mem_univ _⟩
        have h2 : ContinuousOn
            (fun p : ℝ × ℂ => Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) p.2 p.1)
            {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} :=
          (continuousOn_circleAverage_of_continuousOn (continuousOn_radialAvg hg.good)).mono
            fun p hp => ⟨hp.1.le, hOz p hp⟩
        have h3 : ContinuousOn (fun p : ℝ × ℂ =>
            Real.circleAverage (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) p.2 p.1)
            {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} :=
          (continuousOn_circleAverage_of_continuousOn (continuousOn_coneProfile hg)).mono
            fun p hp => ⟨hp.1.le, hOz p hp⟩
        exact (h1.sub h2).add h3
      · filter_upwards [Sec1.ae_distribution_circleAvg_eq hS hH hp.1 (hOne p hp), hcone, hgood,
          ae_scaleRegular_wp hX] with ω h1 hco hg hsr
        obtain ⟨hl₁, hl₂⟩ := hloc ω hg
        show S.hcirc ω p.1 p.2 = circleAvg (X ω) p.1 p.2 -
          Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) p.2 p.1 +
          Real.circleAverage (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) p.2 p.1
        rw [← h1, hco]
        exact circleAvg_cone hl₁ hl₂ (continuousOn_radialAvg hg.good) (continuousOn_coneProfile hg) hp.1
          (hOne p hp) (tendsto_mollAvgS_circleAvg_of_scaleRegular hsr hp.1 p.2)
    filter_upwards [hEq, hid, hucont, hgood] with ω hω hidω hu hg s z hs hzs
    have hp : ((s, z) : ℝ × ℂ) ∈ {p : ℝ × ℂ | 0 < p.1 ∧ dist p.2 c + p.1 < r} :=
      ⟨hs, (closedBall_subset_ball_iff_dist_add_lt hs.le).1 hzs⟩
    have hsph : sphere z s ⊆ ball c r := sphere_subset_closedBall.trans hzs
    have ci0 : CircleIntegrable (u ω) z s := (hu.mono hsph).circleIntegrable hs.le
    have ci1 : CircleIntegrable (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) z s :=
      ((continuousOn_radialAvg hg.good).mono (hsph.trans hsub)).circleIntegrable hs.le
    have ci2 : CircleIntegrable (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) z s :=
      ((continuousOn_coneProfile hg).mono (hsph.trans hsub)).circleIntegrable hs.le
    have e : S.hcirc ω s z = circleAvg (X ω) s z -
        Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) z s +
        Real.circleAverage (coneProfile γ γ (fun t => B t ω) (fun t => B' t ω)) z s := hω hp
    show S.hcirc ω s z = hc ω s z + Real.circleAverage (fun x => u ω x -
      MatedCRTHarmonic.CellScaling.radialAvg (X ω) x +
      coneProfile γ γ (fun t => B t ω) (fun t => B' t ω) x) z s
    rw [e, hidω s z hs hzs,
      Real.circleAverage_fun_add (f₁ := fun x => u ω x - MatedCRTHarmonic.CellScaling.radialAvg (X ω) x)
        (ci0.sub ci1) ci2, Real.circleAverage_fun_sub ci0 ci1]
    ring

end MatedCRT
