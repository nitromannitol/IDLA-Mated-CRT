import MatedCRT.FirstPass.Derived.ConeGFFIsGFF
import MatedCRT.FirstPass.Derived.ConeReferenceLQG
import MatedCRT.FirstPass.Frozen.S5Cited
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Ball masses of the quantum cone from Lemma 2.4 of the harmonic-balls paper

`FrozenBerestyckiGwynneConeBallMass` (Berestycki-Gwynne, arXiv:2003.10320v2, Lemma A.1, eq. (A.1), p. 66;
`MatedCRT/FirstPass/Frozen/S5Cited.lean:28`) follows from the volume growth estimate of the field `h^ℂ - α₀ log |·|`
(`LiouvilleVolumeGrowthStmt`, Lemma 2.4 of the harmonic-balls paper with correction [C1]) at `α₀ = γ`:

* on the closed unit disk the circle average embedding of the `γ`-quantum cone agrees with the coupled field
  `h^ℂ - γ log |·|` of `ConeGFFCoupling2.lean`, where `h^ℂ` is a whole-plane GFF on `(Ω × C(ℝ≥0, ℝ), P ⊗ BM)`
  (`isWholePlaneGFF_coneGFF`); the two differ by the continuous remainder `coneCouplingRemainder`, which vanishes on
  the closed unit disk, so the LQG measure of the coupled field is `e^{-γ R} μ_h` (`IsLQGLimit.add_continuous`) and
  it agrees with the cone measure `μ_h` on every ball `B_δ(z) ⊆ B_1(0)`;
* at `α₀ = γ` the exponent `γ (Q - α₀) = 2 - γ²/2` lies between `(2-γ)²/2` and `(2+γ)²/2`, so the exponent ranges of
  Lemma 2.4 are those of (A.1);
* the events of (A.1) depend only on the cone coordinate, so their probability under `P` is their probability under
  the product measure.
-/

open MeasureTheory Set Metric Filter HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The LQG measure of the coupled field `h^ℂ - γ log |·|`, from the LQG measure `m` of the cone circle averages
`hcirc` and the path `w`: `e^{-γ R} m` with `R = coneCouplingRemainder γ hcirc w`. -/
noncomputable def coneGFFMeasure (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (m : Measure ℂ) : Measure ℂ :=
  m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * -coneCouplingRemainder γ hcirc w z))

/-- The coupled LQG measure agrees with the cone measure on measurable subsets of the closed unit disk. -/
theorem coneGFFMeasure_apply_of_subset (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (m : Measure ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) (hs1 : s ⊆ closedBall 0 1) : coneGFFMeasure γ hcirc w m s = m s := by
  unfold coneGFFMeasure
  rw [withDensity_apply _ hs, ← setLIntegral_one]
  refine setLIntegral_congr_fun hs fun x hx => ?_
  have hx1 : ‖x‖ ≤ 1 := by simpa using hs1 hx
  simp [coneCouplingRemainder, hx1]

/-- **The coupled field carries the cone measure.** If `m` is the dyadic LQG limit of the cone circle averages `hcirc`
(continuous on `(0, ∞) × ℂ`) and `w` is continuous, then `coneGFFMeasure γ hcirc w m` is the dyadic LQG limit of the
circle averages of the coupled field `h^ℂ - γ log |·|`. -/
theorem isLQGLimit_coneGFFMeasure (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    {m : Measure ℂ} (hm : IsLQGLimit γ hcirc m) :
    IsLQGLimit γ (fieldCircleAverage γ (coneGFFCircle γ hcirc w)) (coneGFFMeasure γ hcirc w m) := by
  have hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hR : Continuous (coneCouplingRemainder γ hcirc w) := continuous_coneCouplingRemainder γ hc hw
  have hm' : LatticeProb.LQG.IsLQGLimit γ hcirc m := (LPBridge.isLQGLimit_iff _ _ _).1 hm
  have hcont' : ∀ k : ℕ, Continuous (hcirc (LatticeProb.LQG.dyadicScale k)) := fun k => by
    have := hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z _ => ⟨dyadicScale_pos' k, mem_univ z⟩) (s := univ)
    exact continuousOn_univ.1 this
  have hlim : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
      (fun (k : ℕ) (z : ℂ) => -Real.circleAverage (coneCouplingRemainder γ hcirc w) z
        (LatticeProb.LQG.dyadicScale k))
      (fun z => -coneCouplingRemainder γ hcirc w z) atTop K := fun K hK =>
    (LatticeProb.LQG.MassFunctionalDerived.tendstoUniformlyOn_dyadic_circleAverage hR hK).neg
  have key := LatticeProb.LQG.IsLQGLimit.add_continuous
    (Fε := fun ε z => -Real.circleAverage (coneCouplingRemainder γ hcirc w) z ε)
    hm' hcont' hR.neg (fun k => (continuous_dyadic_circleAverage_center hR k).neg) hlim
  have hfun : (fun ε z => hcirc ε z + -Real.circleAverage (coneCouplingRemainder γ hcirc w) z ε) =
      fieldCircleAverage γ (coneGFFCircle γ hcirc w) := by
    funext ε z
    have h := congrFun (congrFun (coneCircle_eq_addCircleAverage γ hcirc w) ε) z
    simp only [LatticeProb.Gauss.addCircleAverage] at h
    rw [h]
    simp only [add_neg_cancel_right]
    rfl
  rw [hfun] at key
  exact (LPBridge.isLQGLimit_iff _ _ _).2 key

/-- **The coupled field and its LQG measure.** For the circle average embedding of a `γ`-quantum cone with LQG measure
`μ` and any `P`-null set `N`, the coupled field of `isWholePlaneGFF_coneGFF` on `(Ω × C(ℝ≥0, ℝ), P ⊗ BM)` has LQG
measure (with log singularity `-γ log |·|`) the coupled measure `coneGFFMeasure`. -/
theorem isLQGMeasureOfField_coneGFF {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hQ : IsQuantumCone γ P hC hcirc)
    (hμ : IsLQGMeasure P γ hcirc μ) {N : Set Ω} (hN0 : P N = 0) :
    IsLQGMeasureOfField (P.prod (brownianMotion 0)) γ γ
      (fun p => coneGFFCircle γ (circleOff N hcirc p.1) (fun t => p.2 t))
      (fun p => coneGFFMeasure γ (circleOff N hcirc p.1) (fun t => p.2 t) (μ p.1)) := by
  have hae : ∀ᵐ ω ∂P, ω ∉ N ∧ ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      IsLQGLimit γ (hcirc ω) (μ ω) := by
    have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hμ
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hQ.ae_continuousOn_circle, hμ'] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have h' := Measure.quasiMeasurePreserving_fst (μ := P) (ν := brownianMotion 0) |>.ae hae
  refine h'.mono fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [circleOff_of_notMem h1]
  exact isLQGLimit_coneGFFMeasure γ h2 p.2.continuous h3

/-- **Berestycki-Gwynne, Lemma A.1, eq. (A.1)** from Lemma 2.4 of the harmonic-balls paper (with [C1]) on
probability spaces of `Type`. -/
theorem frozenBerestyckiGwynneConeBallMass_of_volumeGrowth (h24 : LiouvilleVolumeGrowthStmt.{0}) :
    FrozenBerestyckiGwynneConeBallMass := by
  intro Ω _ P γ hC hcirc μ hγ hγ2 hcone ζ hζ hζ1
  obtain ⟨hP, hQ, hμ⟩ := hcone
  obtain ⟨N, -, hN0, hG⟩ := isWholePlaneGFF_coneGFF hQ
  have hμ' := isLQGMeasureOfField_coneGFF hQ hμ hN0
  have hQγ : γ * (lqgQ γ - γ) = 2 - γ ^ 2 / 2 := by unfold lqgQ; field_simp; ring
  have hαQ : γ < lqgQ γ := by nlinarith
  have h2γ : 0 < (2 - γ) ^ 2 := by have : 0 < 2 - γ := by linarith
                                   positivity
  have hb0 : 0 < max ((2 - γ) ^ 2 / 2 - ζ) ((2 - γ) ^ 2 / 4) := lt_max_of_lt_right (by positivity)
  have hbm : max ((2 - γ) ^ 2 / 2 - ζ) ((2 - γ) ^ 2 / 4) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - γ)) := by
    rw [hQγ]
    exact lt_min (max_lt (by linarith) (by linarith)) (max_lt (by nlinarith) (by nlinarith))
  have ham : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - γ)) < (2 + γ) ^ 2 / 2 + ζ := by
    rw [hQγ]
    exact max_lt (by linarith) (by nlinarith)
  have h := (h24 γ γ hγ hγ2 hαQ _ (P.prod (brownianMotion 0)) _ _ _ hG hμ' _ _ hb0 hbm ham).1
  unfold PolyHighProb at h ⊢
  obtain ⟨p, hp, C, r₀, hr₀, hbd⟩ := h
  refine ⟨p, hp, C, min r₀ 1, lt_min hr₀ one_pos, fun δ hδ hδr => ?_⟩
  have hδ1 : δ < 1 := lt_of_lt_of_le hδr (min_le_right _ _)
  refine le_trans ?_ (hbd δ hδ (lt_of_lt_of_le hδr (min_le_left _ _)))
  rw [← mul_one (P _), ← measure_univ (μ := brownianMotion 0), ← Measure.prod_prod]
  refine measure_mono fun q hq hq' => ?_
  simp only [mem_prod, mem_compl_iff, mem_ofPred_eq] at hq hq'
  apply hq.1
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by linarith) hz
  have hsub : ball z δ ⊆ closedBall 0 1 := by
    refine (ball_subset_ball' ?_).trans ball_subset_closedBall
    rw [mem_ball] at hz
    linarith
  obtain ⟨hlo, hup⟩ := hq' z hz1
  rw [coneGFFMeasure_apply_of_subset _ _ _ _ measurableSet_ball hsub] at hlo hup
  exact ⟨hlo, hup.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (le_max_left _ _)))⟩

/-- **Berestycki-Gwynne, Lemma A.1, eq. (A.1), from the whole-plane ball-mass bounds.** The single remaining input is
the Ding-Gwynne ball-mass estimate for the whole-plane field (`WholePlaneLQGBallMassBounds`, Ding-Gwynne 2020, Lemma
3.8): Lemma 2.4 of the harmonic-balls paper follows from it with the proved coordinate change at `α₀ = 0`
(`lqgMeasureCoordChange_zero_holds`) and existence of the LQG measure (`lqgMeasureExistence_derived`). -/
theorem frozenBerestyckiGwynneConeBallMass_of_ballMassBounds
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc) :
    FrozenBerestyckiGwynneConeBallMass :=
  frozenBerestyckiGwynneConeBallMass_of_volumeGrowth
    (liouvilleVolumeGrowthStmt_of_existence hDG lqgMeasureCoordChange_zero_holds
      (fun _ _ P γ α hC hcirc => lqgMeasureExistence_derived P γ α hC hcirc))

end MatedCRT.FirstPass.Derived
