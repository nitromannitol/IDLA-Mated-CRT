import MatedCRT.FirstPass.S1c.Threshold
import MatedCRT.FirstPass.Frozen.S1c

/-!
# FIRST PASS, Lemma 5.3: rational threshold characterization of the least supersolution (deterministic part)

The S1c threshold lemma (`neg_mul_green_lt_leastSupersolution_iff`, `threshold_iff_moments`) is stated for the single
constant `-uG(0,p)`. Its proof uses only that the supersolution values at `p` are nonempty and bounded below. So for an
arbitrary real `c` and a lower bound `hbdd`, `c < v(u)(p)` iff some rational `q > c` is below no supersolution value at `p`.
This generic form gives the superlevel sets `{c < v(μ_ω)(p)}` that B1b needs.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open MatedCRT

/-- **Rational threshold characterization** (B1b, deterministic): for any real `c` and a supersolution class whose values at
`p` are bounded below, `c < v(u)(p)` iff some rational `q > c` is below no value `w(p)` of a supersolution `w`. -/
theorem lt_leastSupersolution_iff_exists_rat {μ : Measure ℂ} {R u : ℝ} (hu : 0 < u)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x) (c : ℝ) {p : ℂ}
    (hbdd : BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions μ R 0 u)) :
    c < leastSupersolution μ R 0 u p ↔
      ∃ q : ℚ, c < (q : ℝ) ∧ ¬ ∃ w ∈ supersolutions μ R 0 u, w p < (q : ℝ) := by
  set S : Set ℝ := (fun w : ℂ → ℝ => w p) '' supersolutions μ R 0 u with hS
  have hne : S.Nonempty := ⟨(0 : ℂ → ℝ) p, ⟨0, zero_mem_supersolutions μ hu hG, rfl⟩⟩
  have hlss : leastSupersolution μ R 0 u p = sInf S := rfl
  rw [hlss]
  constructor
  · intro h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    refine ⟨q, hq1, ?_⟩
    rintro ⟨w, hw, hwq⟩
    have h1 : sInf S ≤ w p := csInf_le hbdd ⟨w, hw, rfl⟩
    linarith
  · rintro ⟨q, hq1, hno⟩
    have hle : (q : ℝ) ≤ sInf S := by
      refine le_csInf hne ?_
      rintro y ⟨w, hw, rfl⟩
      show (q : ℝ) ≤ w p
      by_contra hlt
      exact hno ⟨w, hw, not_le.1 hlt⟩
    linarith

/-- **Moment form of the rational threshold** (B1b): the same characterization with the rational events expressed through
the moment vector `(∫ φs k dμ)_k`, as in `threshold_iff_moments` (S1c/Threshold.lean:80). -/
theorem lt_leastSupersolution_iff_moments {μ : Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hμ : μ (closedBall (0 : ℂ) R) < ⊤)
    (hu : 0 < u) (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x) (c : ℝ)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (hbdd : BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions μ R 0 u)) :
    c < leastSupersolution μ R 0 u p ↔
      ∃ q : ℚ, c < (q : ℝ) ∧
        (fun k => ∫ x, φs k x ∂μ) ∉
          Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ) := by
  rw [lt_leastSupersolution_iff_exists_rat hu hG c hbdd]
  refine exists_congr fun q => and_congr Iff.rfl (not_congr ?_)
  exact mem_image_iff_exists_supersolution hR μ hμ φs hφs hdense u (q : ℝ) ⟨p, hp⟩
    (fun k => ∫ x, φs k x ∂μ) (fun k => rfl)

/-- **Null-measurable superlevel sets** (B1b, S1c pattern with the AE form of the test-integral measurability): for a
random measure `μ_ω` with a.s. finite mass on the disc, a.s. bounded-below supersolution values at `p`, and each test
integral `ω ↦ ∫ φ dμ_ω` almost surely measurable, the event `{c < v(u)(p)(μ_ω)}` is `P`-null-measurable for every real `c`. -/
theorem nullMeasurableSet_lt_leastSupersolution_rat {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R)
    (hu : 0 < u) (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → tsupport φ ⊆ closedBall (0 : ℂ) R →
      AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R) (c : ℝ)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions (μ ω) R 0 u)) :
    NullMeasurableSet {ω | c < leastSupersolution (μ ω) R 0 u p} P := by
  let Y : Ω → (ℕ → ℝ) := fun ω k => ∫ x, φs k x ∂(μ ω)
  have hY : AEMeasurable Y P :=
    aemeasurable_pi_iff.2 fun k => hmeas (φs k)
      (contDiff_two_of_isTestFunction (hφs k).1).continuous ((hφs k).1.2.2.trans ball_subset_closedBall)
  set g : Ω → (ℕ → ℝ) := hY.mk Y with hgdef
  have hg : Measurable g := hY.measurable_mk
  have hYg : Y =ᵐ[P] g := hY.ae_eq_mk
  have hA : ∀ q : ℚ, AnalyticSet (Prod.fst '' supersolutionPairs hR φs u
      (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ)) :=
    fun q => analyticSet_supersolutionMoments hR (fun k => (hφs k).1) u _ ⟨p, hp⟩ (q : ℝ)
  have hNM : ∀ q : ℚ, NullMeasurableSet (Y ⁻¹' (Prod.fst '' supersolutionPairs hR φs u
      (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ))) P := by
    intro q
    have h1 : NullMeasurableSet (g ⁻¹' (Prod.fst '' supersolutionPairs hR φs u
        (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ))) P :=
      (hF1 (ℕ → ℝ) (P.map g) (by infer_instance) _ (hA q)).preimage ⟨hg, fun _ h => h⟩
    refine h1.congr ?_
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hYg] with ω hω
    simp only [mem_preimage, hω]
  have hset : {ω | c < leastSupersolution (μ ω) R 0 u p} =ᵐ[P]
      ⋃ q : ℚ, ({ω | c < (q : ℝ)} ∩ (Y ⁻¹' (Prod.fst '' supersolutionPairs hR φs u
        (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ)))ᶜ) := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hμ, hbdd] with ω hω hbω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_preimage]
    exact lt_leastSupersolution_iff_moments hR hω hu φs hφs hdense hG c hp hbω
  exact (NullMeasurableSet.iUnion fun q =>
    ((MeasurableSet.const _).nullMeasurableSet.inter (hNM q).compl)).congr hset.symm

/-- **Superlevel sets to null measurability** (generic measure theory): if every superlevel set `{c < f}` is null measurable,
then `f` is `NullMeasurable` (every Borel preimage is null measurable), via `borel ℝ = generateFrom (range Ioi)`. -/
theorem nullMeasurable_of_superlevel_null {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (h : ∀ c : ℝ, NullMeasurableSet {ω | c < f ω} P) : NullMeasurable f P := by
  let A : MeasurableSpace ℝ :=
    { MeasurableSet' := fun s => NullMeasurableSet (f ⁻¹' s) P
      measurableSet_empty := by
        simp only [preimage_empty]
        exact MeasurableSet.empty.nullMeasurableSet
      measurableSet_compl := fun s hs => by
        rw [preimage_compl]
        exact hs.compl
      measurableSet_iUnion := fun s hs => by
        rw [preimage_iUnion]
        exact NullMeasurableSet.iUnion hs }
  have hIoi : ∀ c : ℝ, MeasurableSet[A] (Ioi c) := fun c => h c
  have hgen : borel ℝ ≤ A := by
    rw [borel_eq_generateFrom_Ioi]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨c, rfl⟩
    exact hIoi c
  intro s hs
  exact hgen s hs

/-- **B1b, AE form**: for a random measure `μ_ω` with a.s. finite mass on the disc and
a.s. bounded-below supersolution values at `p`, the least supersolution value `ω ↦ v(u)(p)(μ_ω)` is `AEMeasurable`, from the
Lusin theorem (`FrozenUniversalMeasurabilityOfAnalytic`) and the AE-form test-integral measurability `hmeas`. -/
theorem aemeasurable_leastSupersolution_of_moments {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R)
    (hu : 0 < u) (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → tsupport φ ⊆ closedBall (0 : ℂ) R →
      AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions (μ ω) R 0 u)) :
    AEMeasurable (fun ω => leastSupersolution (μ ω) R 0 u p) P := by
  apply NullMeasurable.aemeasurable
  apply nullMeasurable_of_superlevel_null
  intro c
  exact nullMeasurableSet_lt_leastSupersolution_rat hF1 hR hu hμ hmeas φs hφs hdense hG hp c hbdd

end MatedCRT.S5c
