import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2g.ScaleGluing
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.FirstPass.S2i.ContinuousDecoder
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

/-! # The global family factor (FirstPass S2i, z2): `ConeGlobalFamilyFactorStep`

Deterministic part: the extension `extCircle` of a carrier point, the scaled circle profiles `scaleProc γ n p`
(`circleProcess` of the rescaled profile at the cone scale radius `scaleRad γ n p` and scale `b n = n + 1`), and their
identities with the cone scaling (`scaleProc_circleProcess`). Route: notes/fp-gaps/CHATGPT-q1-open-steps.md Section 9,
with the gluing `globalFamilyProcess_eq_of_scales` (FirstPass/S2g/ScaleGluing.lean). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- The extension of a circle average process to all radii, by `0` at nonpositive radii. -/
noncomputable def extCircle (p : Ioi (0 : ℝ) × ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then p (⟨r, h⟩, z) else 0

theorem circleProcess_extCircle (p : Ioi (0 : ℝ) × ℂ → ℝ) : circleProcess (extCircle p) = p := by
  funext q
  obtain ⟨⟨r, hr⟩, z⟩ := q
  have hr' : 0 < r := hr
  simp [circleProcess, extCircle, hr']

theorem coneScaleRadius_extCircle_circleProcess (γ : ℝ) (c : ℝ → ℂ → ℝ) (b : ℝ) :
    coneScaleRadius γ (extCircle (circleProcess c)) b = coneScaleRadius γ c b := by
  unfold coneScaleRadius
  congr 1
  ext r
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, by simpa [extCircle, circleProcess, hr] using h⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, by simpa [extCircle, circleProcess, hr] using h⟩

theorem circleProcess_rescaledCircle_extCircle (γ : ℝ) (c : ℝ → ℂ → ℝ) {R b : ℝ} (hR : 0 < R) :
    circleProcess (rescaledCircle γ (extCircle (circleProcess c)) R b) =
      circleProcess (rescaledCircle γ c R b) := by
  funext q
  obtain ⟨⟨r, hr⟩, z⟩ := q
  have hRr : 0 < R * r := mul_pos hR hr
  simp [circleProcess, rescaledCircle, extCircle, hRr]

/-- The scale radius `R_{b_n}` of a carrier point, at the scale `b n = n + 1` (the sequence of Section 9, G1). -/
noncomputable def scaleRad (γ : ℝ) (n : ℕ) (p : Ioi (0 : ℝ) × ℂ → ℝ) : ℝ :=
  coneScaleRadius γ (extCircle p) ((n : ℝ) + 1)

/-- The circle process of the rescaled profile at scale `b n`, for the carrier point `p`. -/
noncomputable def scaleProc (γ : ℝ) (n : ℕ) (p : Ioi (0 : ℝ) × ℂ → ℝ) : Ioi (0 : ℝ) × ℂ → ℝ :=
  circleProcess (rescaledCircle γ (extCircle p) (scaleRad γ n p) ((n : ℝ) + 1))

/-- On a circle average process of a continuous profile with positive scale radius, `scaleProc` is the circle process
of the cone rescaling `rescaledCircle γ c (R_b) b` (`coneScaleRadius γ c b`). -/
theorem scaleProc_circleProcess (γ : ℝ) (n : ℕ) (c : ℝ → ℂ → ℝ)
    (hR : 0 < coneScaleRadius γ c ((n : ℝ) + 1)) :
    scaleProc γ n (circleProcess c) =
      circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
  unfold scaleProc scaleRad
  rw [coneScaleRadius_extCircle_circleProcess]
  exact circleProcess_rescaledCircle_extCircle γ c hR


/-- The decoded log-profile along the real line at zero angle: `r ↦ c_x(r, 0) + Q log r` for the grid decoder `c_x`. -/
noncomputable def profAlong (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (x : ℕ → ℝ) (r : ℝ) : ℝ :=
  extCircle (fun q => profileDec hD x q) r 0 + lqgQ γ * Real.log r

theorem measurable_profAlong_rat (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (q : ℚ) (hq : 0 < (q : ℝ)) :
    Measurable fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ) := by
  have hfun : (fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ)) =
      fun x : ℕ → ℝ => profileDec hD x (⟨(q : ℝ), hq⟩, (0 : ℂ)) + lqgQ γ * Real.log q := by
    funext x
    simp only [profAlong, extCircle, hq, dite_true]
  have hm : Measurable fun x : ℕ → ℝ => ((x, (⟨(q : ℝ), hq⟩, (0 : ℂ))) : (ℕ → ℝ) × CirclePt) :=
    measurable_id.prodMk measurable_const
  rw [hfun]
  exact ((measurable_profileDec hD).comp hm).add measurable_const

/-- On a Borel set of codes of continuous profiles, the set where the scale radius exceeds `s` is Borel
(Mathlib-free level-set characterization, `lt_sSup_level_iff`). -/
theorem measurableSet_inter_radius_gt (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (b s : ℝ)
    (S : Set (ℕ → ℝ)) (hS : MeasurableSet S)
    (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    MeasurableSet (S ∩ {x : ℕ → ℝ | s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b}) := by
  have hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun x : ℕ → ℝ => profAlong γ hD x (q : ℝ) :=
    fun q hq => measurable_profAlong_rat γ hD q hq
  have h1 := measurableSet_levelBoundedTest hF (γ⁻¹ * Real.log b)
  have h2 := measurableSet_existsLevelAbove hF (γ⁻¹ * Real.log b) s
  have h3 := measurableSet_existsLevelAbove hF (γ⁻¹ * Real.log b) 0
  have hP : MeasurableSet {x : ℕ → ℝ | (levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
      existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) s) ∨
      (s < 0 ∧ ¬(levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
        existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) 0))} := by
    exact (h1.inter h2).union ((MeasurableSet.const _).inter (h1.inter h3).compl)
  have heq : S ∩ {x : ℕ → ℝ | s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b} =
      S ∩ {x : ℕ → ℝ | (levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
      existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) s) ∨
      (s < 0 ∧ ¬(levelBoundedTest (profAlong γ hD x) (γ⁻¹ * Real.log b) ∧
        existsLevelAbove (profAlong γ hD x) (γ⁻¹ * Real.log b) 0))} := by
    ext x
    constructor
    · rintro ⟨hxS, hx⟩
      refine ⟨hxS, ?_⟩
      have hx' : s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b := hx
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      rw [hr] at hx'
      exact (lt_sSup_level_iff (hcont x hxS) s).1 hx'
    · rintro ⟨hxS, hx⟩
      refine ⟨hxS, ?_⟩
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      show s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b
      have hr : coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b =
          sSup {r : ℝ | 0 < r ∧ profAlong γ hD x r = γ⁻¹ * Real.log b} := by
        unfold coneScaleRadius profAlong
        rfl
      rw [hr]
      exact (lt_sSup_level_iff (hcont x hxS) s).2 hx
  rw [heq]
  exact hS.inter hP


open Classical in
/-- The decoded scale radius, set to `0` off the Borel set `S` of codes. -/
noncomputable def radiusOn (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ)) (b : ℝ)
    (x : ℕ → ℝ) : ℝ :=
  if x ∈ S then coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b else 0

theorem measurable_radiusOn (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (b : ℝ) (S : Set (ℕ → ℝ))
    (hS : MeasurableSet S) (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    Measurable (radiusOn γ hD S b) := by
  refine measurable_of_Ioi fun s => ?_
  have hA := measurableSet_inter_radius_gt γ hD b s S hS hcont
  have hB : MeasurableSet (Sᶜ ∩ {_x : ℕ → ℝ | s < 0}) := hS.compl.inter (MeasurableSet.const _)
  have hpre : radiusOn γ hD S b ⁻¹' Ioi s =
      (S ∩ {x : ℕ → ℝ | s < coneScaleRadius γ (extCircle (fun q => profileDec hD x q)) b}) ∪
        (Sᶜ ∩ {_x : ℕ → ℝ | s < 0}) := by
    ext x
    by_cases hx : x ∈ S
    · simp [radiusOn, hx]
    · simp [radiusOn, hx]
  rw [hpre]
  exact hA.union hB

/-- A total positive version of a real: `exp (log r)`, equal to `r` for `r > 0` (no case split). -/
noncomputable def posVal (r : ℝ) : ℝ := Real.exp (Real.log r)

theorem posVal_pos (r : ℝ) : 0 < posVal r := Real.exp_pos _

theorem posVal_of_pos {r : ℝ} (hr : 0 < r) : posVal r = r := Real.exp_log hr

theorem measurable_posVal : Measurable posVal :=
  Real.measurable_exp.comp Real.measurable_log

/-- The total point map `(r, z) ↦ (r, z)` on the carrier (`r` replaced by `posVal r`). -/
noncomputable def ptOf (r : ℝ) (z : ℂ) : CirclePt := (⟨posVal r, posVal_pos r⟩, z)

theorem measurable_ptOf : Measurable fun p : ℝ × ℂ => ptOf p.1 p.2 :=
  (Measurable.subtype_mk (measurable_posVal.comp measurable_fst)).prodMk measurable_snd

theorem ptOf_of_pos {r : ℝ} (hr : 0 < r) (z : ℂ) : ptOf r z = (⟨r, hr⟩, z) := by
  simp only [ptOf, posVal_of_pos hr]

/-- The decoded extended profile is jointly measurable in the code and the radius-angle point. -/
theorem measurable_extDecode {D : ℕ → CirclePt} (hD : DenseRange D) :
    Measurable (fun w : (ℕ → ℝ) × ℝ × ℂ => extCircle (fun q => profileDec hD w.1 q) w.2.1 w.2.2) := by
  have hsnd : Measurable fun w : (ℕ → ℝ) × ℝ × ℂ => ptOf w.2.1 w.2.2 :=
    Measurable.comp (g := fun p : ℝ × ℂ => ptOf p.1 p.2) measurable_ptOf (measurable_snd (α := ℕ → ℝ))
  have hpair : Measurable fun w : (ℕ → ℝ) × ℝ × ℂ => ((w.1, ptOf w.2.1 w.2.2) : (ℕ → ℝ) × CirclePt) :=
    measurable_fst.prodMk hsnd
  have h1 : Measurable fun w : (ℕ → ℝ) × ℝ × ℂ => profileDec hD w.1 (ptOf w.2.1 w.2.2) := by
    have h := (measurable_profileDec hD).comp hpair
    exact h
  have key : Measurable fun w : (ℕ → ℝ) × ℝ × ℂ =>
      if 0 < w.2.1 then profileDec hD w.1 (ptOf w.2.1 w.2.2) else 0 := by
    refine Measurable.ite ?_ h1 measurable_const
    exact measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
  have hfun : (fun w : (ℕ → ℝ) × ℝ × ℂ => extCircle (fun q => profileDec hD w.1 q) w.2.1 w.2.2) =
      fun w => if 0 < w.2.1 then profileDec hD w.1 (ptOf w.2.1 w.2.2) else 0 := by
    funext w
    by_cases h : 0 < w.2.1
    · simp [extCircle, ptOf_of_pos, h]
    · simp [extCircle, h]
  rw [hfun]
  exact key


/-- The rescaled code at scale `n + 1` of the decoded profile of the code `x` (the code of the cone rescaling of the
profile, `rescaledCircle γ c (R_{b_n}) b_n`, evaluated at the dense points `D k`). -/
noncomputable def scodeG (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ)) (n : ℕ)
    (x : ℕ → ℝ) : ℕ → ℝ :=
  fun k => rescaledCircle γ (extCircle (fun q => profileDec hD x q)) (radiusOn γ hD S ((n : ℝ) + 1) x)
    ((n : ℝ) + 1) (D k).1 (D k).2

theorem measurable_scodeG (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ)) (b : ℝ)
    (hS : MeasurableSet S) (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) (k : ℕ) :
    Measurable fun x : ℕ → ℝ => rescaledCircle γ (extCircle (fun q => profileDec hD x q))
      (radiusOn γ hD S b x) b (D k).1 (D k).2 := by
  have hR : Measurable (radiusOn γ hD S b) := measurable_radiusOn γ hD b S hS hcont
  have hmul : Measurable fun x : ℕ → ℝ => radiusOn γ hD S b x * (D k).1 := hR.mul_const _
  have hmulC : Measurable fun x : ℕ → ℝ => ((radiusOn γ hD S b x : ℝ) : ℂ) * (D k).2 :=
    (Complex.measurable_ofReal.comp hR).mul_const _
  have hpt : Measurable fun x : ℕ → ℝ => (radiusOn γ hD S b x * (D k).1, ((radiusOn γ hD S b x : ℝ) : ℂ) * (D k).2) :=
    hmul.prodMk hmulC
  have hw : Measurable fun x : ℕ → ℝ => ((x, (radiusOn γ hD S b x * (D k).1,
      ((radiusOn γ hD S b x : ℝ) : ℂ) * (D k).2)) : (ℕ → ℝ) × ℝ × ℂ) :=
    measurable_id.prodMk hpt
  have h1 : Measurable fun x : ℕ → ℝ => extCircle (fun q => profileDec hD x q)
      (radiusOn γ hD S b x * (D k).1) (((radiusOn γ hD S b x : ℝ) : ℂ) * (D k).2) := by
    have h := (measurable_extDecode hD).comp hw
    exact h
  have hlog : Measurable fun x : ℕ → ℝ => lqgQ γ * Real.log (radiusOn γ hD S b x) :=
    (Real.measurable_log.comp hR).const_mul _
  have h2 : Measurable fun x : ℕ → ℝ => extCircle (fun q => profileDec hD x q)
      (radiusOn γ hD S b x * (D k).1) (((radiusOn γ hD S b x : ℝ) : ℂ) * (D k).2) +
      lqgQ γ * Real.log (radiusOn γ hD S b x) := h1.add hlog
  have h3 := h2.sub (measurable_const (a := γ⁻¹ * Real.log b))
  unfold rescaledCircle
  exact h3


/-- The glued global family of the code `x` (Section 9, G3): `(t, z) ↦ 0 < t ∧ ∃ n, t < b_n T_n(x) ∧ z ∈ Λ^{(n)}_t`,
where `Λ^{(n)}_t` is the rescaling `R_n⁻¹ Γ^{(n)}_{t / b_n}` of the decoded canonical family at scale `n`, with the
decoder `F` of the canonical factor. The decoded process `decodeFamily (F (scodeG n x))` is the canonical process of the
rescaled profile. -/
noncomputable def globalCodeFactor (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (x : ℕ → ℝ) : ℝ × ℂ → Prop :=
  fun q => 0 < q.1 ∧ ∃ n : ℕ, q.1 < ((n : ℝ) + 1) * (F (scodeG γ hD S n x)).1 ∧
    decodeFamily (F (scodeG γ hD S n x)) (((n : ℝ) + 1)⁻¹ * q.1,
      (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)

theorem measurable_globalCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (hF : Measurable F) (hS : MeasurableSet S)
    (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    Measurable (globalCodeFactor γ hD S F) := by
  have hR : ∀ n : ℕ, Measurable (radiusOn γ hD S ((n : ℝ) + 1)) :=
    fun n => measurable_radiusOn γ hD ((n : ℝ) + 1) S hS hcont
  have hsc : ∀ n : ℕ, Measurable (scodeG γ hD S n) := fun n =>
    measurable_pi_iff.2 fun k => measurable_scodeG γ hD S ((n : ℝ) + 1) hS hcont k
  have hΨ : ∀ n : ℕ, Measurable fun x : ℕ → ℝ => (F (scodeG γ hD S n x)).1 := fun n =>
    measurable_fst.comp (hF.comp (hsc n))
  have hRinv : ∀ n : ℕ, Measurable fun x : ℕ → ℝ => (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) :=
    fun n => Complex.measurable_ofReal.comp (hR n).inv
  have hset : ∀ q : ℝ × ℂ, MeasurableSet {x : ℕ → ℝ | globalCodeFactor γ hD S F x q} := by
    intro q
    have e : {x : ℕ → ℝ | globalCodeFactor γ hD S F x q} =
        {_x : ℕ → ℝ | 0 < q.1} ∩ ⋃ n : ℕ, ({x : ℕ → ℝ | q.1 < ((n : ℝ) + 1) * (F (scodeG γ hD S n x)).1} ∩
          {x : ℕ → ℝ | decodeFamily (F (scodeG γ hD S n x)) (((n : ℝ) + 1)⁻¹ * q.1,
            (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)}) := by
      ext x
      simp only [globalCodeFactor, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    rw [e]
    refine (MeasurableSet.const _).inter (MeasurableSet.iUnion fun n => ?_)
    refine (measurableSet_lt measurable_const ((hΨ n).const_mul ((n : ℝ) + 1))).inter ?_
    have hmap : Measurable fun x : ℕ → ℝ => ((F (scodeG γ hD S n x)), (((n : ℝ) + 1)⁻¹ * q.1,
        (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)) :=
      (hF.comp (hsc n)).prodMk (measurable_const.prodMk ((hRinv n).mul_const _))
    have hdec := measurableSet_decodeFamily_uncurry.preimage hmap
    exact hdec
  exact Measurable.of_eval fun q => measurableSet_setOfPred.1 (hset q)


/-- **The glued identity (deterministic; Section 9, G5).** A global cone family `Λ` for `μ` has the process of the glued
canonical families: if at each scale `n` the decoded canonical process of the code `x` is the space-time process of a
cone family `Γ n` for the rescaled measure, stopped at `T n` with `T n = (F (scodeG n x)).1`, and the scales cover, then
`globalFamilyProcess Λ = globalCodeFactor x`. -/
theorem globalFamilyProcess_eq_globalCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (x : ℕ → ℝ) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) (R T : ℕ → ℝ) (Γ : ℕ → ℝ → Set ℂ)
    (hR : ∀ n : ℕ, 0 < R n) (hRx : ∀ n : ℕ, radiusOn γ hD S ((n : ℝ) + 1) x = R n)
    (hfam : ∀ n : ℕ, IsConeHarmonicBallFamilyOn (rescaledMeasure μ (R n) ((n : ℝ) + 1)) (Γ n) (T n))
    (hst : ∀ n : ℕ, IsStoppedAtHalfBall (Γ n) (T n))
    (hT : ∀ n : ℕ, (F (scodeG γ hD S n x)).1 = T n)
    (hdec : ∀ n : ℕ, decodeFamily (F (scodeG γ hD S n x)) = familyProcess (Γ n) (T n))
    (hcov : ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) * T n) :
    globalFamilyProcess Λ = globalCodeFactor γ hD S F x := by
  have hfam' : ∀ n : ℕ, IsConeHarmonicBallFamilyOn μ (rescaledFamily (Γ n) (R n)⁻¹ ((n : ℝ) + 1)⁻¹)
      (((n : ℝ) + 1) * T n) := fun n =>
    (rescaledFamily_transfer_fp (hR n) (by positivity) (hfam n) (hst n)).1
  rw [globalFamilyProcess_eq_of_scales hΛ hfam' hcov]
  funext q
  apply propext
  constructor
  · rintro ⟨hq, n, h1, h2⟩
    have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨hq, n, ?_, ?_⟩
    · rw [hT n]
      exact h1
    · rw [hdec n, hRx n]
      refine ⟨⟨mul_pos (inv_pos.2 hb) hq, (inv_mul_lt_iff₀ hb).2 h1⟩, ?_⟩
      exact h2
  · rintro ⟨hq, n, h1, h2⟩
    refine ⟨hq, n, ?_, ?_⟩
    · rw [hT n] at h1
      exact h1
    · rw [hdec n, hRx n] at h2
      obtain ⟨_, h⟩ := h2
      exact h


/-- The code of a continuous profile is the code of its scale-`b` rescaling, on the continuous set (the identity used
for the rescaled codes of Section 9, G1). -/
theorem scodeG_eq_circleCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (c : ℝ → ℂ → ℝ) (hc : Continuous (circleProcess c)) (n : ℕ)
    (hS : circleCode D (circleProcess c) ∈ S) (hR : 0 < coneScaleRadius γ c ((n : ℝ) + 1)) :
    scodeG γ hD S n (circleCode D (circleProcess c)) =
      circleCode D (circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) := by
  have hprof : (fun q : CirclePt => profileDec hD (circleCode D (circleProcess c)) q) = circleProcess c := by
    funext q
    exact profileDec_circleCode hD hc q
  have hrad : radiusOn γ hD S ((n : ℝ) + 1) (circleCode D (circleProcess c)) =
      coneScaleRadius γ c ((n : ℝ) + 1) := by
    unfold radiusOn
    simp only [hS, ↓reduceIte]
    rw [hprof, coneScaleRadius_extCircle_circleProcess]
  funext k
  show rescaledCircle γ (extCircle (fun q => profileDec hD (circleCode D (circleProcess c)) q))
      (radiusOn γ hD S ((n : ℝ) + 1) (circleCode D (circleProcess c))) ((n : ℝ) + 1) (D k).1 (D k).2 =
      circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) (D k)
  rw [hrad, hprof]
  exact congrFun (circleProcess_rescaledCircle_extCircle γ c hR) (D k)


/-- The rescaled profile of a continuous code: the log-profile along the real line is continuous on `(0, ∞)`. -/
theorem profAlong_continuousOn_code (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (c : ℝ → ℂ → ℝ)
    (hcc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (profAlong γ hD (circleCode D (circleProcess c))) (Ioi 0) := by
  have hprof : (fun q : CirclePt => profileDec hD (circleCode D (circleProcess c)) q) = circleProcess c := by
    funext q
    exact profileDec_circleCode hD (continuous_circleProcess_of_continuousOn hcc) q
  have hmaps : MapsTo (fun r : ℝ => (r, (0 : ℂ))) (Ioi 0) (Ioi 0 ×ˢ univ) :=
    fun r hr => ⟨hr, mem_univ _⟩
  have hc0 : ContinuousOn (fun r : ℝ => c r 0) (Ioi 0) :=
    hcc.comp (continuousOn_id.prodMk continuousOn_const) hmaps
  have hlog : ContinuousOn (fun r : ℝ => Real.log r) (Ioi 0) :=
    Real.continuousOn_log.mono (fun r (hr : 0 < r) => ne_of_gt hr)
  have h1 : ContinuousOn (fun r : ℝ => c r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hc0.add (hlog.const_smul (lqgQ γ))
  refine h1.congr ?_
  intro r hr
  have hr' : 0 < r := hr
  have hq := congrFun hprof (⟨⟨r, hr'⟩, (0 : ℂ)⟩ : CirclePt)
  show extCircle (fun q => profileDec hD (circleCode D (circleProcess c)) q) r 0 +
      lqgQ γ * Real.log r = c r 0 + lqgQ γ * Real.log r
  simp [extCircle, hr', hq, circleProcess]

/-- The circle average process of a cone field is measurable in the sample (product σ-algebra on the carrier). -/
theorem measurable_circleProcess_of_quantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQC : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => circleProcess (hcirc ω) := by
  refine measurable_pi_iff.2 fun q => ?_
  exact hQC.measurable_circle (q.1 : ℝ) q.2 q.1.2


/-- The almost sure facts of a sample used by the global factor: continuity, the LQG limit and, for every scale
`n + 1`, the positivity of the scale radius and the LQG limit of the rescaled profile. -/
def ConeExtra {Ω : Type} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (ω : Ω) : Prop :=
  ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧ IsLQGLimit γ (hcirc ω) (μ ω) ∧
    ∀ n : ℕ, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) ∧
      IsLQGLimit γ (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))


/-- **Reference good set (Section 9, G1-G2).** On the reference cone, a Borel set `Bs` of sample codes of continuous
profiles captures almost every sample; the rescaled codes at every scale are almost surely in `B`, and the scaled
canonical horizons are almost surely unbounded. -/
theorem global_reference_good (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) {D : ℕ → CirclePt} (hD : DenseRange D)
    (hscale : QuantumConeScalingInput) {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (hF : Measurable F)
    (hcls : CanonicalFactorClauses γ (fun p => (F (circleCode D p)).1)
      (fun p => decodeFamily (F (circleCode D p))) ((circleCode D) ⁻¹' B))
    (hextra : ∀ᵐ ω ∂P, ConeExtra γ hcirc μ ω) :
    ∃ Bs : Set (ℕ → ℝ), MeasurableSet Bs ∧ (∀ x ∈ Bs, ContinuousOn (profAlong γ hD x) (Ioi 0)) ∧
      ∀ᵐ ω ∂P, circleCode D (circleProcess (hcirc ω)) ∈ B ∧ circleCode D (circleProcess (hcirc ω)) ∈ Bs ∧
        (∀ n : ℕ, scodeG γ hD Bs n (circleCode D (circleProcess (hcirc ω))) ∈ B) ∧
        ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) *
          (F (scodeG γ hD Bs n (circleCode D (circleProcess (hcirc ω)))) ).1 := by
  have hP' : IsProbabilityMeasure P := hcone.1
  have hQC : IsQuantumCone γ P hC hcirc := hcone.2.1
  have hκ : Measurable fun ω => circleCode D (circleProcess (hcirc ω)) :=
    (measurable_circleCode D).comp (measurable_circleProcess_of_quantumCone hQC)
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    filter_upwards [hextra] with ω hω
    exact hω.1
  obtain ⟨Et, hEt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  have hEm : MeasurableSet Etᶜ := htm.compl
  have hEfull : P Etᶜᶜ = 0 := by
    rw [compl_compl]
    exact ht0
  obtain ⟨Bs, hBs, hBsE, hBsae⟩ :=
    exists_borel_full_image P (fun ω => circleCode D (circleProcess (hcirc ω))) hκ Etᶜ hEm hEfull
  have hcontS : ∀ x ∈ Bs, ContinuousOn (profAlong γ hD x) (Ioi 0) := by
    intro x hx
    obtain ⟨ω, hωE, hωx⟩ := hBsE hx
    have hcω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
      by_contra hn
      exact hωE (hEt hn)
    rw [← hωx]
    exact profAlong_continuousOn_code γ hD (hcirc ω) hcω
  refine ⟨Bs, hBs, hcontS, ?_⟩
  have hiB : ∀ᵐ ω ∂P, circleCode D (circleProcess (hcirc ω)) ∈ B :=
    (hcls.2 Ω P hC hcirc μ hcone).2.2
  have hcc : Measurable (circleCode D) := measurable_circleCode D
  have hgAE : ∀ n : ℕ, AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))) P := fun n =>
    Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ0 hγ2 hQC (by positivity)
  have hlawn : ∀ n : ℕ, P.map (fun ω => circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)))) =
      P.map (fun ω => circleCode D (circleProcess (hcirc ω))) := by
    intro n
    have hl := hscale γ hγ0 hγ2 Ω P hC hcirc hP' hQC ((n : ℝ) + 1) (by positivity)
    calc P.map (fun ω => circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))))
        = (P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)))).map (circleCode D) :=
          (AEMeasurable.map_map_of_aemeasurable hcc.aemeasurable (hgAE n)).symm
      _ = (P.map (fun ω => circleProcess (hcirc ω))).map (circleCode D) := by rw [hl]
      _ = P.map (fun ω => circleCode D (circleProcess (hcirc ω))) :=
          AEMeasurable.map_map_of_aemeasurable hcc.aemeasurable
            (measurable_circleProcess_of_quantumCone hQC).aemeasurable
  have hscMem : ∀ n : ℕ, ∀ᵐ ω ∂P, circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))) ∈ B := fun n =>
    ae_mem_of_law_eq_measurable hB hκ.aemeasurable ((hcc.comp_aemeasurable (hgAE n))) (hlawn n) hiB
  have hscEq : ∀ n : ℕ, ∀ᵐ ω ∂P, scodeG γ hD Bs n (circleCode D (circleProcess (hcirc ω))) =
      circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
        (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))) := by
    intro n
    filter_upwards [hBsae, hextra] with ω h1 h2
    exact scodeG_eq_circleCode γ hD Bs (hcirc ω) (continuous_circleProcess_of_continuousOn h2.1) n h1
      (h2.2.2 n).1
  have hscAll : ∀ᵐ ω ∂P, ∀ n : ℕ, scodeG γ hD Bs n (circleCode D (circleProcess (hcirc ω))) =
      circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
        (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))) := ae_all_iff.2 hscEq
  have hpos : ∀ᵐ ω ∂P, 0 < (F (circleCode D (circleProcess (hcirc ω)))).1 := by
    filter_upwards [hextra, hiB] with ω h1 h2
    have h := hcls.1 (hcirc ω) h2 h1.1 (μ ω) h1.2.1
    have hp : 0 < halfBallTime (μ ω) := h.2.2.1
    rw [h.1] at hp
    exact hp
  have hΨm : Measurable fun x : ℕ → ℝ => (F x).1 := measurable_fst.comp hF
  have hTn : ∀ n : ℕ, AEMeasurable (fun ω => (F (circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))))).1) P := fun n =>
    hΨm.comp_aemeasurable (hcc.comp_aemeasurable (hgAE n))
  have hlawT : ∀ n : ℕ, P.map (fun ω => (F (circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))))).1) =
      P.map (fun ω => (F (circleCode D (circleProcess (hcirc ω)))).1) := by
    intro n
    calc P.map (fun ω => (F (circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))))).1)
        = (P.map (fun ω => circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))))).map (fun x => (F x).1) :=
          (AEMeasurable.map_map_of_aemeasurable hΨm.aemeasurable
            (hcc.comp_aemeasurable (hgAE n))).symm
      _ = (P.map (fun ω => circleCode D (circleProcess (hcirc ω)))).map (fun x => (F x).1) := by
          rw [hlawn n]
      _ = P.map (fun ω => (F (circleCode D (circleProcess (hcirc ω)))).1) :=
          AEMeasurable.map_map_of_aemeasurable hΨm.aemeasurable hκ.aemeasurable
  have hscMemAll : ∀ᵐ ω ∂P, ∀ n : ℕ, circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))) ∈ B := ae_all_iff.2 hscMem
  have hunb := ae_forall_exists_scale_gt (P := P)
    (X := fun ω => (F (circleCode D (circleProcess (hcirc ω)))).1) (hΨm.comp_aemeasurable hκ.aemeasurable)
    hpos (T := fun n ω => (F (circleCode D (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)))) ).1) hTn hlawT
  filter_upwards [hiB, hBsae, hscAll, hunb, hscMemAll] with ω h1 h2 h3 h4 h5
  refine ⟨h1, h2, fun n => ?_, fun M => ?_⟩
  · rw [h3 n]
    exact h5 n
  · obtain ⟨k, hk⟩ := h4 M
    refine ⟨k, ?_⟩
    rw [h3 k]
    exact hk


/-- The radius of a sample code (on the set `S` of codes of continuous profiles) is the cone scale radius of the profile. -/
theorem radiusOn_circleCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (c : ℝ → ℂ → ℝ) (hc : Continuous (circleProcess c)) (b : ℝ)
    (hS : circleCode D (circleProcess c) ∈ S) :
    radiusOn γ hD S b (circleCode D (circleProcess c)) = coneScaleRadius γ c b := by
  have hprof : (fun q : CirclePt => profileDec hD (circleCode D (circleProcess c)) q) = circleProcess c := by
    funext q
    exact profileDec_circleCode hD hc q
  unfold radiusOn
  simp only [hS, ↓reduceIte]
  rw [hprof, coneScaleRadius_extCircle_circleProcess]

/-- The Borel set of codes on which the global family is glued (Section 9, G1): codes of the reference samples that
lie in the Borel set `B` of the canonical factor, with all rescaled codes in `B` and the scaled horizons unbounded. -/
def globalBss (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (B Bs : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) : Set (ℕ → ℝ) :=
  (B ∩ Bs ∩ (⋂ n : ℕ, scodeG γ hD Bs n ⁻¹' B)) ∩
    (⋂ M : ℕ, ⋃ n : ℕ, {x : ℕ → ℝ | (M : ℝ) < ((n : ℝ) + 1) * (F (scodeG γ hD Bs n x)).1})

theorem measurableSet_globalBss (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (B Bs : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (hF : Measurable F) (hB : MeasurableSet B) (hBs : MeasurableSet Bs)
    (hcont : ∀ x ∈ Bs, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    MeasurableSet (globalBss γ hD B Bs F) := by
  have hsc : ∀ n : ℕ, Measurable (scodeG γ hD Bs n) := fun n =>
    measurable_pi_iff.2 fun k => measurable_scodeG γ hD Bs ((n : ℝ) + 1) hBs hcont k
  have hΨn : ∀ n : ℕ, Measurable fun x : ℕ → ℝ => (F (scodeG γ hD Bs n x)).1 := fun n =>
    measurable_fst.comp (hF.comp (hsc n))
  refine MeasurableSet.inter (MeasurableSet.inter (hB.inter hBs) (MeasurableSet.iInter fun n => hsc n hB)) ?_
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const ((hΨn n).const_mul _)


/-- **`ConeGlobalFamilyFactorStep` (FirstPass S2i, z2; Section 9 of notes/fp-gaps/CHATGPT-q1-open-steps.md).** From the
canonical factor (`coneCanonicalFactor_code_of`, the closure step `ConeHalfBallClosureInsideStep`, the volume growth
statement), the scale invariance in law `QuantumConeScalingInput`, the LQG measure properties `LQGMeasurePropertiesStmt`,
and the two frozen cone externals. -/
theorem coneGlobalFamilyFactor_proved (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeGlobalFamilyFactorStep := by
  intro γ hγ0 hγ2
  obtain ⟨Ω, instΩ, hSB, P, hC, hcirc, μ, hcone⟩ := hE2 γ hγ0 hγ2
  have hP : IsProbabilityMeasure P := hcone.1
  have hQC : IsQuantumCone γ P hC hcirc := hcone.2.1
  have hextra : ∀ᵐ ω ∂P, ConeExtra γ hcirc μ ω := by
    have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) :=
      hQC.ae_continuousOn_circle
    have hLQG : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
    have hRL : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) ∧
        IsLQGLimit γ (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))
          (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) := fun n =>
      (coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale)) γ hγ0 hγ2 Ω P hC hcirc μ hcone
        ((n : ℝ) + 1) (by positivity)
    filter_upwards [hcont, hLQG, ae_all_iff.2 hRL] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨D, B, F, hD, hB, hF, hcls, hwit⟩ :=
    coneCanonicalFactor_code_of hcan hcl h27 hE1 γ hγ0 hγ2 Ω P hC hcirc μ hcone (ConeExtra γ hcirc μ) hextra
  obtain ⟨Bs, hBs, hcontS, hgood⟩ :=
    global_reference_good γ hγ0 hγ2 hD hscale P hC hcirc μ hcone B hB F hF hcls hextra
  have hBssm : MeasurableSet (globalBss γ hD B Bs F) :=
    measurableSet_globalBss γ hD B Bs F hF hB hBs hcontS
  refine ⟨fun p => globalCodeFactor γ hD Bs F (circleCode D p), (circleCode D) ⁻¹' globalBss γ hD B Bs F,
    measurable_circleCode D hBssm, ?_, ?_⟩
  · intro c hcG hcc ν hν Λ' hΛ'
    have hcpc : Continuous (circleProcess c) := continuous_circleProcess_of_continuousOn hcc
    obtain ⟨⟨⟨hxB, hxS⟩, hxA⟩, hxC⟩ := hcG
    obtain ⟨ω, hωE, hωx⟩ := hwit _ hxB
    obtain ⟨hcontω, hLQGω, hRLω⟩ := hωE
    have hprof : circleProcess (hcirc ω) = circleProcess c :=
      eq_of_circleCode_eq hD (continuous_circleProcess_of_continuousOn hcontω) hcpc hωx
    have hcfun : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, c ε z = hcirc ω ε z := fun ε hε z =>
      (congrFun hprof (⟨ε, hε⟩, z)).symm
    have hνμ : μ ω = ν := hLQGω.unique (isLQGLimit_congr hcfun hν)
    subst hνμ
    have hRe : ∀ b : ℝ, coneScaleRadius γ c b = coneScaleRadius γ (hcirc ω) b := fun b => by
      rw [← coneScaleRadius_extCircle_circleProcess γ c b, ← hprof,
        coneScaleRadius_extCircle_circleProcess γ (hcirc ω) b]
    have hRpos : ∀ n : ℕ, 0 < coneScaleRadius γ c ((n : ℝ) + 1) := fun n => by
      rw [hRe]
      exact (hRLω n).1
    have hid : ∀ n : ℕ, scodeG γ hD Bs n (circleCode D (circleProcess c)) =
        circleCode D (circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) :=
      fun n => scodeG_eq_circleCode γ hD Bs c hcpc n hxS (hRpos n)
    have hRx : ∀ n : ℕ, radiusOn γ hD Bs ((n : ℝ) + 1) (circleCode D (circleProcess c)) =
        coneScaleRadius γ c ((n : ℝ) + 1) := fun n => radiusOn_circleCode γ hD Bs c hcpc _ hxS
    have hcnG : ∀ n : ℕ, circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))
        ∈ (circleCode D) ⁻¹' B := by
      intro n
      show circleCode D (circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) ∈ B
      rw [← hid n]
      exact (Set.mem_iInter.mp hxA) n
    have hcncont : ∀ n : ℕ, ContinuousOn
        (fun p : ℝ × ℂ => rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1) p.1 p.2)
        (Ioi 0 ×ˢ univ) := fun n => continuousOn_rescaledCircle hcc (hRpos n)
    have hcnLQG : ∀ n : ℕ, IsLQGLimit γ (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))
        (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
      intro n
      rw [hRe]
      refine isLQGLimit_congr ?_ (hRLω n).2
      intro ε hε z
      have hR : 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) := (hRLω n).1
      unfold rescaledCircle
      rw [hcfun (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) * ε) (mul_pos hR hε)]
    have hcl_n : ∀ n : ℕ, halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) = (F (circleCode D (circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))))).1 ∧
        (∃ Γ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) Γ (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) ∧
          IsStoppedAtHalfBall Γ (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)))) ∧
        0 < halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) ∧
        ∀ (T : ℝ) (Γ : ℝ → Set ℂ), 0 < T → IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) Γ T →
          IsStoppedAtHalfBall Γ T → familyProcess Γ T = decodeFamily (F (circleCode D (circleProcess (rescaledCircle γ c (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))))) := by
      intro n
      exact hcls.1 _ (hcnG n) (hcncont n) _ (hcnLQG n)
    have hex : ∀ n : ℕ, ∃ Γ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn
        (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) Γ
        (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) ∧
        IsStoppedAtHalfBall Γ
        (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) :=
      fun n => (hcl_n n).2.1
    choose Γ hΓ hst using hex
    have hT : ∀ n : ℕ, (F (scodeG γ hD Bs n (circleCode D (circleProcess c)))).1 =
        halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
      intro n
      rw [hid n]
      exact ((hcl_n n).1).symm
    have hdec : ∀ n : ℕ, decodeFamily (F (scodeG γ hD Bs n (circleCode D (circleProcess c)))) =
        familyProcess (Γ n) (halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1))) := by
      intro n
      rw [hid n]
      exact ((hcl_n n).2.2.2 _ (Γ n) ((hcl_n n).2.2.1) (hΓ n) (hst n)).symm
    have hcov : ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) *
        halfBallTime (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
      intro M
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hxC M)
      exact ⟨n, by rw [← hT n]; exact hn⟩
    show globalFamilyProcess Λ' = globalCodeFactor γ hD Bs F (circleCode D (circleProcess c))
    exact globalFamilyProcess_eq_globalCode γ hD Bs F (circleCode D (circleProcess c)) hΛ'
      (fun n => coneScaleRadius γ c ((n : ℝ) + 1)) (fun n => halfBallTime
        (rescaledMeasure (μ ω) (coneScaleRadius γ c ((n : ℝ) + 1)) ((n : ℝ) + 1)))
      Γ hRpos hRx hΓ hst hT hdec hcov
  · intro Ω' _ P' hC' hcirc' μ' hcone'
    have hGm : MeasurableSet ((circleCode D) ⁻¹' globalBss γ hD B Bs F) := measurable_circleCode D hBssm
    refine ⟨(measurable_globalCode γ hD Bs F hF hBs hcontS |>.comp (measurable_circleCode D)).aemeasurable, ?_⟩
    have hGref : ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ (circleCode D) ⁻¹' globalBss γ hD B Bs F := by
      filter_upwards [hgood] with ω hω
      obtain ⟨h1, h2, h3, h4⟩ := hω
      show circleCode D (circleProcess (hcirc ω)) ∈ globalBss γ hD B Bs F
      unfold globalBss
      exact ⟨⟨⟨h1, h2⟩, Set.mem_iInter.2 h3⟩, Set.mem_iInter.2 fun M => Set.mem_iUnion.2 (h4 M)⟩
    have hQcC : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
      (measurable_circleProcess_of_quantumCone hQC).aemeasurable
    have hQcC' : AEMeasurable (fun ω => circleProcess (hcirc' ω)) P' :=
      (measurable_circleProcess_of_quantumCone hcone'.2.1).aemeasurable
    have hlaw := hE1 γ hγ0 hγ2 Ω P hC hcirc μ hcone Ω' P' hC' hcirc' μ' hcone'
    have h1 : ∀ᵐ y ∂(P.map (fun ω => circleProcess (hcirc ω))), y ∈ (circleCode D) ⁻¹' globalBss γ hD B Bs F :=
      (ae_map_iff hQcC hGm).2 hGref
    rw [hlaw] at h1
    exact (ae_map_iff hQcC' hGm).1 h1

end MatedCRT
