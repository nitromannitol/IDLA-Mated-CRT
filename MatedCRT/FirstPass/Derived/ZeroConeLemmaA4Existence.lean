import MatedCRT.FirstPass.Derived.ZeroConeLemmaA4Proof

/-!
# The existence of the capped squares (A.2) of Gwynne–Miller–Sheffield at the `0`-quantum cone

Gwynne–Miller–Sheffield (arXiv:1705.11161, (A.2) and Lemma A.4) consider, for `m ∈ (0, ∞)`, the largest square
`Ŝ_m` of an independent uniform dyadic system containing `0` of area at most `m`. This file reduces the existence
clause (A.2) of `ZeroConeUniformRootLemmaA4` to two properties of the area measure `ν` of the `0`-quantum cone,

* `ν` is finite on compact sets, and has no atom at `0`;
* `ν` has infinite total mass (`ZeroConeInfiniteMass`),

and to the following facts on the uniform dyadic system, which hold for almost every system: its offsets are
compatible, the origin lies on no grid line, and the squares of the chain at the origin exhaust the plane.
For such a system the masses of the squares of the chain at the origin increase with the generation (the squares
are nested), tend to `ν {0} = 0` as the generation decreases (the squares shrink to `{0}`, continuity from above of
a finite measure) and to `ν ℂ = ∞` as the generation increases (continuity from below), so the chain has a
largest square of mass at most `m` (`LatticeProb.DyadicOffset.exists_isCappedSquare_squareAt`).

## Main definitions

* `ZeroConeInfiniteMass`: the area measure of the `0`-quantum cone has infinite total mass almost surely.
* `ZeroConeNoAtomAtOrigin`: the area measure of the `0`-quantum cone has no atom at the origin almost surely.
* `ZeroConeUniformRootLemmaA4Law`: the law clause of Lemma A.4 (arXiv:1705.11161), that is,
  `ZeroConeUniformRootLemmaA4` without the existence clause (A.2).

## Main statements

* `ZeroConeRoot.exists_isCappedSquare_of_massData`: the existence of `Ŝ_m` for a dyadic system with the
  properties above and a measure with the properties above.
* `ae_exists_isCappedSquare_zeroCone_of_infMass`: the clause (A.2) of `ZeroConeUniformRootLemmaA4`.
* `zeroConeUniformRootLemmaA4_of_law_of_infMass`: `ZeroConeUniformRootLemmaA4` from its law clause.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal Pointwise

namespace ZeroConeRoot

open LatticeProb.DyadicOffset (unifIco gridFloor squareAt IsOffGrid IsCompatible dyadicSquares
  cornerSquare isCompact_cornerSquare squareAt_mono mem_squareAt exists_isCappedSquare_squareAt
  ae_isCompatible_isOffGrid_system ae_iUnion_squareAt_eq_univ)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- The intersection of the squares of generations `-n`, `n ∈ ℕ`, of the chain at the origin is `{0}`. -/
theorem iInter_squareAt_neg_eq (s : ℝ) (o₁ o₂ : ℕ → ℝ) :
    ⋂ n : ℕ, squareAt s o₁ o₂ (-(n : ℤ)) 0 = {0} := by
  have hbd : ∀ (z : ℂ), (∀ n : ℕ, z ∈ squareAt s o₁ o₂ (-(n : ℤ)) 0) → ∀ n : ℕ,
      |z.re| ≤ (2 : ℝ) ^ s * (1 / 2) ^ n ∧ |z.im| ≤ (2 : ℝ) ^ s * (1 / 2) ^ n := by
    intro z hz n
    have h0 := mem_squareAt (s := s) (o₁ := o₁) (o₂ := o₂) (-(n : ℤ)) 0
    have hz' := hz n
    have hside : (2 : ℝ) ^ (s + ((-(n : ℤ) : ℤ) : ℝ)) = (2 : ℝ) ^ s * (1 / 2) ^ n := by
      rw [Int.cast_neg, Int.cast_natCast, Real.rpow_add two_pos, Real.rpow_neg (by norm_num),
        Real.rpow_natCast, one_div, inv_pow]
    simp only [squareAt, LatticeProb.DyadicOffset.mem_cornerSquare, Complex.zero_re, Complex.zero_im] at h0 hz'
    rw [hside] at h0 hz'
    exact ⟨abs_le.2 ⟨by linarith [h0.1, hz'.1, h0.2.1], by linarith [h0.1, hz'.2.1, h0.2.1]⟩,
      abs_le.2 ⟨by linarith [h0.2.2.1, hz'.2.2.1, h0.2.2.2], by linarith [h0.2.2.1, hz'.2.2.2, h0.2.2.2]⟩⟩
  ext z
  simp only [mem_iInter, mem_singleton_iff]
  constructor
  · intro hz
    have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ s * (1 / 2) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((2 : ℝ) ^ s)
    have hre : |z.re| ≤ 0 := ge_of_tendsto' hlim fun n => (hbd z hz n).1
    have him : |z.im| ≤ 0 := ge_of_tendsto' hlim fun n => (hbd z hz n).2
    exact Complex.ext (abs_nonpos_iff.1 hre) (abs_nonpos_iff.1 him)
  · rintro rfl n
    exact mem_squareAt _ _

/-- **The existence of the capped square `Ŝ_m` at the origin.** Let `ν` be finite on compact sets, without atom at
`0` and of infinite total mass, and let a dyadic system have compatible offsets, no grid line through the origin
and squares of the chain at the origin exhausting the plane. Then for every `m ∈ (0, ∞)` the largest square of the
system containing `0` of mass at most `m` exists. -/
theorem exists_isCappedSquare_of_massData {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤)
    (h0 : ν {0} = 0) (hinf : ν univ = ⊤) {s : ℝ} {o₁ o₂ : ℕ → ℝ} (h₁ : IsCompatible o₁)
    (h₂ : IsCompatible o₂) (hw : IsOffGrid s o₁ o₂ 0) (hU : ⋃ j, squareAt s o₁ o₂ j 0 = univ)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hm : m ≠ ∞) :
    ∃ S, IsCappedSquare (dyadicSquares s o₁ o₂) (⇑ν) m 0 S := by
  have hmono : Monotone fun j : ℤ => ν (squareAt s o₁ o₂ j 0) := fun i j hij =>
    measure_mono (squareAt_mono h₁ h₂ hw hij)
  have hlow : ∃ j, ν (squareAt s o₁ o₂ j 0) ≤ m := by
    have hA : Antitone fun n : ℕ => squareAt s o₁ o₂ (-(n : ℤ)) 0 := fun a b hab =>
      squareAt_mono h₁ h₂ hw (by simpa using hab)
    have hAm : ∀ n : ℕ, NullMeasurableSet (squareAt s o₁ o₂ (-(n : ℤ)) 0) ν := fun n =>
      (isCompact_cornerSquare _ _ _).isClosed.measurableSet.nullMeasurableSet
    have hfin : ∃ n : ℕ, ν (squareAt s o₁ o₂ (-(n : ℤ)) 0) ≠ ⊤ :=
      ⟨0, (hν _ (isCompact_cornerSquare _ _ _)).ne⟩
    have hlim := tendsto_measure_iInter_atTop hAm hA hfin
    rw [iInter_squareAt_neg_eq, h0] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hm0))).exists
    exact ⟨-(n : ℤ), hn.le⟩
  have hhigh : ∃ j, m < ν (squareAt s o₁ o₂ j 0) := by
    by_contra hcon
    push Not at hcon
    have hle : ν univ ≤ m := by
      rw [← hU, (squareAt_mono h₁ h₂ hw).directed_le.measure_iUnion]
      exact iSup_le hcon
    rw [hinf] at hle
    exact hm (top_le_iff.1 hle)
  obtain ⟨j, -, -, hj⟩ := exists_isCappedSquare_squareAt h₁ h₂ hw (ν := ⇑ν) (m := m) hmono hlow hhigh
  exact ⟨_, hj⟩

end ZeroConeRoot

open ZeroConeRoot
open LatticeProb.DyadicOffset (unifIco dyadicSquares cornerSquare gridFloor squareAt IsOffGrid
  ae_isCompatible_isOffGrid_system ae_iUnion_squareAt_eq_univ)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- **The area measure of the `0`-quantum cone has infinite total mass.** For `X₀'` a whole-plane GFF and `b`, `b'`
independent standard Brownian motions independent of it, `zeroConeFieldOf γ X₀' b b'` is the circle-average
embedding of the `0`-quantum cone, and `M h` a measurable choice of the vague limit of the dyadic area approximations
of `h`: almost surely `M h` has infinite total mass. -/
def ZeroConeInfiniteMass (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∀ M : Field → Measure ℂ, Measurable M →
      (∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (M h)) →
      ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), M h Set.univ = ⊤

/-- **The area measure of the `0`-quantum cone has no atom at the origin**, in the setting of
`ZeroConeInfiniteMass`: almost surely `M h {0} = 0`. -/
def ZeroConeNoAtomAtOrigin (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∀ M : Field → Measure ℂ, Measurable M →
      (∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (M h)) →
      ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), M h {0} = 0

/-- **The law clause of Lemma A.4 of Gwynne–Miller–Sheffield** (arXiv:1705.11161, Lemma A.4, the printed source of
this clause: "Let `z_m` be sampled uniformly from Lebesgue measure on `Ŝ_m`, normalized to be a probability
measure. Then `(ℂ, h, z_m, ∞)` agrees in law with `(ℂ, h, 0, ∞)` as a quantum surface, i.e., there is a random
constant `C_m > 0` such that `h(C_m · + z_m) + Q log C_m =d h`"). This is `ZeroConeUniformRootLemmaA4` without its
first clause, the existence of the squares `Ŝ_m` of (A.2), which is proved separately
(`ae_exists_isCappedSquare_zeroCone_of_infMass`). -/
def ZeroConeUniformRootLemmaA4Law (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∀ M : Field → Measure ℂ, Measurable M →
      (∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (M h)) →
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ Z : Field × DyCoord × (ℝ × ℝ) → ℂ, Measurable Z →
        (∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw, ∃ a c ℓ : ℝ, 0 < ℓ ∧
          cappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 = cornerSquare a c ℓ ∧
          ∀ u : ℝ × ℝ, Z (p.1, p.2, u) = ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) →
        ∃ C : Field × DyCoord × (ℝ × ℝ) × ℝ → ℝ, Measurable C ∧ (∀ x, 0 < C x) ∧
          ((P'.map (zeroConeFieldOf γ X₀' b b')).prod
              (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1)))).map
            (fun x => lqgSimilarityField γ (C x) (Z (x.1, x.2.1, x.2.2.1)) x.1) =
            P'.map (zeroConeFieldOf γ X₀' b b')

/-- **The existence of the squares `Ŝ_m` of (A.2) for the `0`-quantum cone** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, (A.2)): given that the area measure has no atom at the origin and infinite total mass, almost
surely for every `m ∈ (0, ∞)` the largest square of the uniform dyadic system containing `0` of area at most `m`
exists. -/
theorem ae_exists_isCappedSquare_zeroCone_of_infMass (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hinf : ZeroConeInfiniteMass γ hγ) (hno : ZeroConeNoAtomAtOrigin γ hγ) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : LQGMetric.IsWholePlaneGFF X₀' P') (hb : IsBrownianReal b P')
    (hb' : IsBrownianReal b' P')
    (hXbb : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P')
    (M : Field → Measure ℂ) (hM : Measurable M)
    (hMv : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (M h)) :
    ∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S := by
  have hHm := aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hi := hinf P' X₀' b b' hP hX hb hb' hXbb hbb' M hM hMv
  have ha := hno P' X₀' b b' hP hX hb hb' hXbb hbb' M hM hMv
  have hloc : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), ∀ K : Set ℂ, IsCompact K → M h K < ⊤ :=
    hMv.mono fun _ hh => hh.1
  have hq : ∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw,
      LatticeProb.DyadicOffset.IsCompatible p.2.2.1 ∧ LatticeProb.DyadicOffset.IsCompatible p.2.2.2 ∧
        IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 :=
    ZeroConeRoot.ae_prod_snd_of_ae (ae_isCompatible_isOffGrid_system 0)
  have hU : ∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw,
      ⋃ j, squareAt p.2.1 p.2.2.1 p.2.2.2 j 0 = Set.univ :=
    ZeroConeRoot.ae_prod_snd_of_ae (ae_iUnion_squareAt_eq_univ.mono fun _ hq => hq 0)
  filter_upwards [ZeroConeRoot.ae_prod_fst_of_ae hloc, ZeroConeRoot.ae_prod_fst_of_ae ha,
    ZeroConeRoot.ae_prod_fst_of_ae hi, hq, hU] with p hp1 hp2 hp3 hp4 hp5 m hm0 hm
  exact exists_isCappedSquare_of_massData hp1 hp2 hp3 hp4.1 hp4.2.1 hp4.2.2 hp5 hm0 hm

/-- **Lemma A.4 of Gwynne–Miller–Sheffield with the existence of the square (A.2)**
(`ZeroConeUniformRootLemmaA4`) from its law clause (`ZeroConeUniformRootLemmaA4Law`), the infinite total mass and
the absence of an atom at the origin of the area measure of the `0`-quantum cone. -/
theorem zeroConeUniformRootLemmaA4_of_law_of_infMass (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hinf : ZeroConeInfiniteMass γ hγ) (hno : ZeroConeNoAtomAtOrigin γ hγ)
    (h : ZeroConeUniformRootLemmaA4Law γ hγ) : ZeroConeUniformRootLemmaA4 γ hγ := by
  intro Ω' _ P' X₀' b b' hP hX hb hb' hXbb hbb' M hM hMv
  exact ⟨ae_exists_isCappedSquare_zeroCone_of_infMass γ hγ hinf hno P' X₀' b b' hP hX hb hb' hXbb hbb' M hM
      hMv, h P' X₀' b b' hP hX hb hb' hXbb hbb' M hM hMv⟩

end MatedCRT
