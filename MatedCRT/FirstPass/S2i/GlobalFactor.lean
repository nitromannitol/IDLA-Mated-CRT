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
noncomputable def globalCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (x : ℕ → ℝ) : ℝ × ℂ → Prop :=
  fun q => 0 < q.1 ∧ ∃ n : ℕ, q.1 < ((n : ℝ) + 1) * (F (scodeG γ hD S n x)).1 ∧
    decodeFamily (F (scodeG γ hD S n x)) (((n : ℝ) + 1)⁻¹ * q.1,
      (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)

theorem measurable_globalCode (γ : ℝ) {D : ℕ → CirclePt} (hD : DenseRange D) (S : Set (ℕ → ℝ))
    (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)) (hF : Measurable F) (hS : MeasurableSet S)
    (hcont : ∀ x ∈ S, ContinuousOn (profAlong γ hD x) (Ioi 0)) :
    Measurable (globalCode γ hD S F) := by
  have hR : ∀ n : ℕ, Measurable (radiusOn γ hD S ((n : ℝ) + 1)) :=
    fun n => measurable_radiusOn γ hD ((n : ℝ) + 1) S hS hcont
  have hsc : ∀ n : ℕ, Measurable (scodeG γ hD S n) := fun n =>
    measurable_pi_iff.2 fun k => measurable_scodeG γ hD S ((n : ℝ) + 1) hS hcont k
  have hΨ : ∀ n : ℕ, Measurable fun x : ℕ → ℝ => (F (scodeG γ hD S n x)).1 := fun n =>
    measurable_fst.comp (hF.comp (hsc n))
  have hRinv : ∀ n : ℕ, Measurable fun x : ℕ → ℝ => (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) :=
    fun n => Complex.measurable_ofReal.comp (hR n).inv
  have hset : ∀ q : ℝ × ℂ, MeasurableSet {x : ℕ → ℝ | globalCode γ hD S F x q} := by
    intro q
    have e : {x : ℕ → ℝ | globalCode γ hD S F x q} =
        {_x : ℕ → ℝ | 0 < q.1} ∩ ⋃ n : ℕ, ({x : ℕ → ℝ | q.1 < ((n : ℝ) + 1) * (F (scodeG γ hD S n x)).1} ∩
          {x : ℕ → ℝ | decodeFamily (F (scodeG γ hD S n x)) (((n : ℝ) + 1)⁻¹ * q.1,
            (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)}) := by
      ext x
      simp only [globalCode, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    rw [e]
    refine (MeasurableSet.const _).inter (MeasurableSet.iUnion fun n => ?_)
    refine (measurableSet_lt measurable_const ((hΨ n).const_mul ((n : ℝ) + 1))).inter ?_
    have hmap : Measurable fun x : ℕ → ℝ => ((F (scodeG γ hD S n x)), (((n : ℝ) + 1)⁻¹ * q.1,
        (((radiusOn γ hD S ((n : ℝ) + 1) x)⁻¹ : ℝ) : ℂ) * q.2)) :=
      (hF.comp (hsc n)).prodMk (measurable_const.prodMk ((hRinv n).mul_const _))
    have hdec := measurableSet_decodeFamily_uncurry.preimage hmap
    exact hdec
  exact Measurable.of_eval fun q => measurableSet_setOfPred.1 (hset q)

end MatedCRT
