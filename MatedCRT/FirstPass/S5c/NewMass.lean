import Mathlib

/-!
# FIRST PASS, stopped clause of 5.1: countable representation of the new-mass event `E_t` (G-stopped Gap 1 repair)

Operator ruling 2026-11-09 19:20 UTC: the Gap 1 repair of G-stopped (CHATGPT-stopped-repair-check.md, item 1) is correct
after one measurability insertion: the event `E_t` that a monotone family of open sets gains a point at time `t` not
in any earlier member has the countable representation

  `E_t = ⋃_{C rational closed disk} ( {C ⊆ Λ_t} ∩ ⋂_{q rational, 0 < q < t} {C ⊄ Λ_q} )`.

The reverse inclusion uses compactness: if every point of `C` lies in an earlier member, finitely many (monotone, hence one)
earlier member covers `C`. Deterministic set theory for a monotone family of open sets in `ℂ`, plus the countable-union
measurability. Harmonic-balls potential theory is not used; the family is an arbitrary monotone open family (the
harmonic-ball family satisfies it: `SatisfiesHarmonicBallConditions.monotoneOn`, regular open values).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- The *new mass at time `t`*: a point of `Λ_t` lying in no earlier member `Λ_q`, `0 < q < t`. -/
def NewMassAt (Λ : ℝ → Set ℂ) (t : ℝ) : Prop :=
  ∃ x ∈ Λ t, ∀ q : ℝ, 0 < q → q < t → x ∉ Λ q

/-- The closed disk with rational centre `c = (a, b)` (the point `a + b i`) and rational radius `r`. -/
def ratDisk (c : ℚ × ℚ) (r : ℚ) : Set ℂ :=
  closedBall (⟨(c.1 : ℝ), (c.2 : ℝ)⟩ : ℂ) (r : ℝ)

/-- **Forward direction**: a new point of an open `Λ_t` lies in a rational closed disk inside `Λ_t` that avoids
every earlier `Λ_q`. -/
theorem exists_ratDisk_of_newMassAt {Λ : ℝ → Set ℂ} {t : ℝ}
    (hopen : IsOpen (Λ t)) (hx : ∃ x ∈ Λ t, ∀ q : ℝ, 0 < q → q < t → x ∉ Λ q) :
    ∃ (c : ℚ × ℚ) (r : ℚ), 0 < (r : ℝ) ∧ ratDisk c r ⊆ Λ t ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ (q : ℝ) := by
  obtain ⟨x, hxt, hxq⟩ := hx
  obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.1 hopen x hxt
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - r0 / 6 < x.re + r0 / 6 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - r0 / 6 < x.im + r0 / 6 by linarith)
  have h1 : (x.re - (a : ℝ)) ^ 2 < (r0 / 6) ^ 2 := by nlinarith
  have h2 : (x.im - (b : ℝ)) ^ 2 < (r0 / 6) ^ 2 := by nlinarith
  have hdist : dist x (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) < r0 / 3 := by
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' (by linarith)]
    dsimp only
    nlinarith
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show dist x (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) <
    r0 - dist x (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) by linarith)
  refine ⟨(a, b), r, lt_of_le_of_lt dist_nonneg hr1, ?_, ?_⟩
  · intro y hy
    apply hball
    rw [mem_ball]
    have hy' : dist y (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) ≤ (r : ℝ) := hy
    have htri := dist_triangle y (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) x
    rw [dist_comm (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) x] at htri
    linarith
  · intro q _ _ hsub
    have hxC : x ∈ ratDisk (a, b) r := by
      show x ∈ closedBall (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) (r : ℝ)
      rw [mem_closedBall]
      exact hr1.le
    exact hxq (q : ℝ) (by assumption) (by assumption) (hsub hxC)

/-- **Reverse direction**: a rational closed disk inside `Λ_t` avoiding every earlier rational member contains a new point
at time `t`. Compactness of the disk and monotonicity give the contradiction. -/
theorem newMassAt_of_ratDisk {Λ : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn Λ (Ioi 0)) (hopen : ∀ s : ℝ, 0 < s → IsOpen (Λ s))
    {c : ℚ × ℚ} {r : ℚ} (hsub : ratDisk c r ⊆ Λ t)
    (hno : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ (q : ℝ)) :
    NewMassAt Λ t := by
  by_contra hcon
  have hcov : ratDisk c r ⊆ ⋃ i : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, Λ ((i.1 : ℚ) : ℝ) := by
    intro x hx
    have hxt := hsub hx
    have hex : ∃ q : ℝ, 0 < q ∧ q < t ∧ x ∈ Λ q := by
      by_contra h
      exact hcon ⟨x, hxt, fun q hq0 hqt hxq => h ⟨q, hq0, hqt, hxq⟩⟩
    obtain ⟨q, hq0, hqt, hxq⟩ := hex
    obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hqt
    have hq'0 : (0 : ℝ) < (q' : ℝ) := lt_trans hq0 hq1
    refine mem_iUnion.2 ⟨⟨q', hq'0, hq2⟩, ?_⟩
    exact hmono (mem_Ioi.2 hq0) (mem_Ioi.2 hq'0) hq1.le hxq
  have hK : IsCompact (ratDisk c r) := isCompact_closedBall _ _
  obtain ⟨q0, h0, h0t⟩ := exists_rat_btwn ht
  have : Nonempty {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t} := ⟨⟨q0, h0, h0t⟩⟩
  have hF : Monotone (fun i : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t} => Λ ((i.1 : ℚ) : ℝ)) := by
    intro i j hij
    have hle : ((i.1 : ℚ) : ℝ) ≤ ((j.1 : ℚ) : ℝ) := Rat.cast_le.2 hij
    exact hmono (mem_Ioi.2 i.2.1) (mem_Ioi.2 j.2.1) hle
  obtain ⟨i, hi⟩ := hK.elim_directed_cover
    (fun i : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t} => Λ ((i.1 : ℚ) : ℝ))
    (fun i => hopen _ i.2.1) hcov hF.directed_le
  exact hno i.1 i.2.1 i.2.2 hi

/-- **Countable representation of the new-mass event** (G-stopped Gap 1 repair): for a monotone family of open sets,
`NewMassAt Λ t` holds iff some rational closed disk lies in `Λ_t` and in no earlier rational member. -/
theorem newMassAt_iff_ratDisk {Λ : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn Λ (Ioi 0)) (hopen : ∀ s : ℝ, 0 < s → IsOpen (Λ s)) :
    NewMassAt Λ t ↔ ∃ (c : ℚ × ℚ) (r : ℚ), 0 < (r : ℝ) ∧ ratDisk c r ⊆ Λ t ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ (q : ℝ) := by
  constructor
  · intro h
    exact exists_ratDisk_of_newMassAt (hopen t ht) h
  · rintro ⟨c, r, _, hsub, hno⟩
    exact newMassAt_of_ratDisk ht hmono hopen hsub hno

/-- **Measurability of the new-mass event** (G-stopped Gap 1 repair, the measurability insertion): if each event
`{ω | C ⊆ Λ_s(ω)}` for a rational disk `C` and real `s` is measurable, then `{ω | NewMassAt (Λ ω) t}` is measurable, being a
countable union over rational centres, radii and rational times. -/
theorem measurableSet_newMassAt {Ω : Type*} [MeasurableSpace Ω] {Λ : Ω → ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0)) (hopen : ∀ ω, ∀ s : ℝ, 0 < s → IsOpen (Λ ω s))
    (hmeas : ∀ (c : ℚ × ℚ) (r : ℚ) (s : ℝ), MeasurableSet {ω | ratDisk c r ⊆ Λ ω s}) :
    MeasurableSet {ω | NewMassAt (Λ ω) t} := by
  have hset : {ω | NewMassAt (Λ ω) t} =
      ⋃ (c : ℚ × ℚ) (r : ℚ), {ω | 0 < (r : ℝ)} ∩ ({ω | ratDisk c r ⊆ Λ ω t} ∩
        ⋂ (q : ℚ), {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ ω (q : ℝ)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      obtain ⟨c, r, hr, hsub, hno⟩ := (newMassAt_iff_ratDisk ht (hmono ω) (hopen ω)).1 h
      exact ⟨c, r, hr, hsub, fun q h1 h2 => hno q h1 h2⟩
    · rintro ⟨c, r, hr, hsub, hno⟩
      exact (newMassAt_iff_ratDisk ht (hmono ω) (hopen ω)).2
        ⟨c, r, hr, hsub, fun q h1 h2 => hno q h1 h2⟩
  rw [hset]
  refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun r => ?_
  refine (MeasurableSet.const _).inter ((hmeas c r t).inter (MeasurableSet.iInter fun q => ?_))
  by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) < t
  · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ ω (q : ℝ)} =
        {ω | ratDisk c r ⊆ Λ ω (q : ℝ)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, h.1, h.2, true_implies]
    rw [e]
    exact (hmeas c r (q : ℝ)).compl
  · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisk c r ⊆ Λ ω (q : ℝ)} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e]
    exact MeasurableSet.univ

end MatedCRT.S5c
