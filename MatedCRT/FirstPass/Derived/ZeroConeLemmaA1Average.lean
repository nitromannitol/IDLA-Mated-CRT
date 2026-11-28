import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Root
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Tail
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Sectors
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Cesaro
import LatticeProb.Prob.DyadicExhaustion

/-!
# Cesàro averages of the exterior observation (Lemma A.1 of Gwynne–Miller–Sheffield)

Step 4 of the proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A; written answer 58,
section 3, fourth and fifth paragraphs). The local observation `J(h, z)` averaged over the capped square `S_m` of an
independent uniform dyadic system approximates `F(h)` in `L¹` (hypothesis `hR3`, display (1) of the written proof).
The exterior versions of the area measure and of the local observation, which depend on the restriction of the field
to `{|w| > k}` only, are taken as hypotheses (`hD`, `hG`). Removing the disc `{|w| ≤ k + 1}` from the area measure
shifts the level of the capped square by the mass `d` of the disc, once the square contains the disc; the shift is
absorbed by averaging over the levels `m ∈ [N, 2N]`.

## Main statement

* `exists_extVersion_approx`: for every `η > 0` there is a function measurable for the exterior σ-algebra
  `extSigma k` which approximates `F` in `L¹` up to `δ + η`.

## Auxiliary statements

* `measurable_rootSample_comp'`: the uniform root sampler is jointly measurable in the measure, the dyadic system, the
  uniform point and the level.
* `rootSample_eq_of_shift`: the root sampler of the exterior mass at level `m` is the root sampler of the full mass at
  level `m + d` once the capped square contains the disc.
* `exists_forall_abs_rootMean_sub_le`: the mean of the exterior observation at the root of level `m` is within `ε`
  of the mean of the local observation at level `m + d`, for all large `m`.
* `abs_cesaro_sub_le`: the averages over `[N, 2N]` of two bounded functions which differ by a shift `d` and an
  error at most `ε` differ by at most `2 K d / N + ε`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-! ### Joint measurability in the level -/

section Measurability

/-- The largest index of a measurable family of sets of indices in `ℤ` is measurable. -/
theorem measurable_sSup_int {β : Type*} [MeasurableSpace β] {A : ℤ → Set β}
    (hA : ∀ j, MeasurableSet (A j)) : Measurable fun x => sSup {j : ℤ | x ∈ A j} := by
  have himp : ∀ (j : ℤ) (P : Prop), MeasurableSet {x : β | x ∈ A j → P} := by
    intro j P
    by_cases hP : P
    · convert MeasurableSet.univ using 1
      ext x
      simp [hP]
    · convert (hA j).compl using 1
      ext x
      simp [hP]
  have hgood : MeasurableSet {x : β | (∃ j, x ∈ A j) ∧ ∃ N : ℤ, ∀ j, x ∈ A j → j ≤ N} := by
    have : {x : β | (∃ j, x ∈ A j) ∧ ∃ N : ℤ, ∀ j, x ∈ A j → j ≤ N} =
        (⋃ j, A j) ∩ ⋃ N : ℤ, ⋂ j, {x | x ∈ A j → j ≤ N} := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    rw [this]
    exact (MeasurableSet.iUnion hA).inter
      (MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j => himp j _)
  refine measurable_to_countable' fun i => ?_
  have hpre : (fun x : β => sSup {j : ℤ | x ∈ A j}) ⁻¹' {i} =
      (A i ∩ ⋂ j, {x | x ∈ A j → j ≤ i}) ∪
        ({x | (∃ j, x ∈ A j) ∧ ∃ N : ℤ, ∀ j, x ∈ A j → j ≤ N}ᶜ ∩ {_x | i = 0}) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter, mem_ofPred_eq,
      mem_compl_iff]
    constructor
    · intro hp
      by_cases hg : (∃ j, x ∈ A j) ∧ ∃ N : ℤ, ∀ j, x ∈ A j → j ≤ N
      · left
        obtain ⟨⟨j₀, hj₀⟩, N, hN⟩ := hg
        have hne : ({j | x ∈ A j} : Set ℤ).Nonempty := ⟨j₀, hj₀⟩
        have hbdd : BddAbove ({j | x ∈ A j} : Set ℤ) := ⟨N, fun j hj => hN j hj⟩
        have hmem := Int.csSup_mem hne hbdd
        rw [← hp]
        exact ⟨hmem, fun j hj => le_csSup hbdd hj⟩
      · right
        refine ⟨hg, ?_⟩
        rw [← hp]
        refine ZeroConeRoot.int_sSup_eq_zero fun h => hg ⟨?_, ?_⟩
        · obtain ⟨j, hj⟩ := h.1
          exact ⟨j, hj⟩
        · obtain ⟨N, hN⟩ := h.2
          exact ⟨N, fun j hj => hN hj⟩
    · rintro (⟨hi, hmax⟩ | ⟨hg, rfl⟩)
      · show sSup {j : ℤ | x ∈ A j} = i
        exact le_antisymm (csSup_le ⟨i, hi⟩ fun j hj => hmax j hj) (le_csSup ⟨i, fun j hj => hmax j hj⟩ hi)
      · show sSup {j : ℤ | x ∈ A j} = 0
        refine ZeroConeRoot.int_sSup_eq_zero fun h => hg ⟨?_, ?_⟩
        · obtain ⟨j, hj⟩ := h.1
          exact ⟨j, hj⟩
        · obtain ⟨N, hN⟩ := h.2
          exact ⟨N, fun j hj => hN hj⟩
  rw [hpre]
  exact ((hA i).inter (MeasurableSet.iInter fun j => himp j _)).union
    (hgood.compl.inter (MeasurableSet.const _))

/-- **The generation of the root square is jointly measurable in the measure, the dyadic system and the level.** -/
theorem measurable_rootGen_comp {β : Type*} [MeasurableSpace β] {N : β → Measure ℂ}
    {q : β → ZeroConeRoot.DyCoord} {m : β → ℝ≥0∞} (hN : Measurable N) (hq : Measurable q)
    (hm : Measurable m) : Measurable fun x => ZeroConeRoot.rootGen (N x) (q x) (m x) := by
  have hA : ∀ j : ℤ, MeasurableSet {x : β | ZeroConeRoot.chainMass (N x) (q x) j ≤ m x} := fun j =>
    measurableSet_le ((ZeroConeRoot.measurable_chainMass j).comp (hN.prodMk hq)) hm
  exact measurable_sSup_int (A := fun j => {x : β | ZeroConeRoot.chainMass (N x) (q x) j ≤ m x}) hA

/-- **The uniform root sampler is jointly measurable in the measure, the dyadic system, the uniform point and the
level.** -/
theorem measurable_rootSample_comp' {β : Type*} [MeasurableSpace β] {N : β → Measure ℂ}
    {q : β → ZeroConeRoot.DyCoord} {u : β → ℝ × ℝ} {m : β → ℝ≥0∞} (hN : Measurable N) (hq : Measurable q)
    (hu : Measurable u) (hm : Measurable m) :
    Measurable fun x => ZeroConeRoot.rootSample (N x) (q x) (m x) (u x) := by
  have hG : Measurable fun r : ℤ × (ZeroConeRoot.DyCoord × (ℝ × ℝ)) =>
      ZeroConeRoot.chainPoint r.2.1 r.1 r.2.2 :=
    measurable_from_prod_countable_right fun j => ZeroConeRoot.measurable_chainPoint j
  have h := hG.comp ((measurable_rootGen_comp hN hq hm).prodMk (hq.prodMk hu))
  simp only [Function.comp_def] at h
  unfold ZeroConeRoot.rootSample
  exact h

/-- The mean of an observation `J` at the uniform root of the capped square of level `m` of the dyadic system `q`. -/
def rootMean (J : ℂ → ℝ) (ν : Measure ℂ) (q : ZeroConeRoot.DyCoord) (m : ℝ≥0∞) : ℝ :=
  ∫ u, J (ZeroConeRoot.rootSample ν q m u) ∂ZeroConeRoot.unifSquareLaw

/-- **The mean at the root is jointly measurable** in the parameter of the observation, the measure, the dyadic
system and the level. -/
theorem measurable_rootMean {β X : Type*} [MeasurableSpace β] [MeasurableSpace X] {J : X × ℂ → ℝ}
    (hJ : Measurable J) {x : β → X} {N : β → Measure ℂ} {q : β → ZeroConeRoot.DyCoord} {m : β → ℝ≥0∞}
    (hx : Measurable x) (hN : Measurable N) (hq : Measurable q) (hm : Measurable m) :
    Measurable fun b => rootMean (fun z => J (x b, z)) (N b) (q b) (m b) := by
  have hF : Measurable fun p : β × (ℝ × ℝ) =>
      J (x p.1, ZeroConeRoot.rootSample (N p.1) (q p.1) (m p.1) p.2) :=
    hJ.comp ((hx.comp measurable_fst).prodMk (measurable_rootSample_comp' (hN.comp measurable_fst)
      (hq.comp measurable_fst) measurable_snd (hm.comp measurable_fst)))
  show Measurable fun b => ∫ u, J (x b, ZeroConeRoot.rootSample (N b) (q b) (m b) u)
    ∂ZeroConeRoot.unifSquareLaw
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_rootMean_le {J : ℂ → ℝ} {K : ℝ} (hJ : ∀ z, |J z| ≤ K) (ν : Measure ℂ) (q : ZeroConeRoot.DyCoord)
    (m : ℝ≥0∞) : |rootMean J ν q m| ≤ K := by
  have := norm_integral_le_of_norm_le_const (μ := ZeroConeRoot.unifSquareLaw)
    (f := fun u => J (ZeroConeRoot.rootSample ν q m u)) (C := K)
    (ae_of_all _ fun u => by simpa using hJ _)
  simpa [rootMean] using this

theorem rootMean_nonneg {J : ℂ → ℝ} (hJ : ∀ z, 0 ≤ J z) (ν : Measure ℂ) (q : ZeroConeRoot.DyCoord)
    (m : ℝ≥0∞) : 0 ≤ rootMean J ν q m :=
  integral_nonneg fun _ => hJ _

end Measurability

/-! ### The shift of the level by the mass of the disc -/

section Shift

open LatticeProb.DyadicOffset (IsCompatible IsOffGrid IsExhaustive squareAt dyadicSquares cornerSquare gridFloor
  eq_squareAt_of_mem squareAt_mono exists_forall_ge_mem_gridInterval mem_cornerSquare)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- A closed disc is contained in the squares of large generation containing the origin, for exhaustive offsets. -/
theorem closedBall_subset_squareAt {s : ℝ} {o₁ o₂ : ℕ → ℝ} (h₁ : IsExhaustive o₁) (h₂ : IsExhaustive o₂)
    (R : ℝ) : ∃ J : ℤ, ∀ j : ℤ, J ≤ j → Metric.closedBall (0 : ℂ) R ⊆ squareAt s o₁ o₂ j 0 := by
  obtain ⟨K₁, hK₁⟩ := exists_forall_ge_mem_gridInterval h₁ s 0 R
  obtain ⟨K₁', hK₁'⟩ := exists_forall_ge_mem_gridInterval h₁ s 0 (-R)
  obtain ⟨K₂, hK₂⟩ := exists_forall_ge_mem_gridInterval h₂ s 0 R
  obtain ⟨K₂', hK₂'⟩ := exists_forall_ge_mem_gridInterval h₂ s 0 (-R)
  refine ⟨((max (max K₁ K₁') (max K₂ K₂') : ℕ) : ℤ), fun j hj z hz => ?_⟩
  have hle : ∀ K : ℕ, K ≤ max (max K₁ K₁') (max K₂ K₂') → (K : ℤ) ≤ j := fun K hK =>
    (Nat.cast_le.2 hK).trans hj
  obtain ⟨a1, b1⟩ := hK₁ j (hle _ (le_trans (le_max_left _ _) (le_max_left _ _)))
  obtain ⟨a2, b2⟩ := hK₁' j (hle _ (le_trans (le_max_right _ _) (le_max_left _ _)))
  obtain ⟨a3, b3⟩ := hK₂ j (hle _ (le_trans (le_max_left _ _) (le_max_right _ _)))
  obtain ⟨a4, b4⟩ := hK₂' j (hle _ (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hz' : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 hz
  have hre := abs_le.1 ((Complex.abs_re_le_norm z).trans hz')
  have him := abs_le.1 ((Complex.abs_im_le_norm z).trans hz')
  simp only [squareAt, Complex.zero_re, Complex.zero_im, mem_cornerSquare] at a1 a2 a3 a4 b1 b2 b3 b4 ⊢
  exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-- A closed square is determined by its lower left corner and its side. -/
theorem cornerSquare_inj {a c ℓ a' c' ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (h : cornerSquare a c ℓ = cornerSquare a' c' ℓ') : a = a' ∧ c = c' ∧ ℓ = ℓ' := by
  have l1 := ZeroConeRoot.side_le_of_cornerSquare_subset hℓ.le h.le
  have l2 := ZeroConeRoot.side_le_of_cornerSquare_subset hℓ'.le h.ge
  have c1 : (⟨a, c⟩ : ℂ) ∈ cornerSquare a c ℓ :=
    ⟨le_rfl, le_add_of_nonneg_right hℓ.le, le_rfl, le_add_of_nonneg_right hℓ.le⟩
  have c2 : (⟨a', c'⟩ : ℂ) ∈ cornerSquare a' c' ℓ' :=
    ⟨le_rfl, le_add_of_nonneg_right hℓ'.le, le_rfl, le_add_of_nonneg_right hℓ'.le⟩
  rw [h] at c1
  rw [← h] at c2
  obtain ⟨c11, -, c12, -⟩ := c1
  obtain ⟨c21, -, c22, -⟩ := c2
  exact ⟨le_antisymm c21 c11, le_antisymm c22 c12, le_antisymm l1 l2⟩

/-- The squares of the system containing the origin are nested. -/
theorem dyadic_nest {s : ℝ} {o₁ o₂ : ℕ → ℝ} (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    (hw : IsOffGrid s o₁ o₂ 0) :
    ∀ S₁ ∈ dyadicSquares s o₁ o₂, ∀ S₂ ∈ dyadicSquares s o₁ o₂, (0 : ℂ) ∈ S₁ → (0 : ℂ) ∈ S₂ →
      S₁ ⊆ S₂ ∨ S₂ ⊆ S₁ := by
  intro S₁ hS₁ S₂ hS₂ hw₁ hw₂
  obtain ⟨j₁, rfl⟩ := eq_squareAt_of_mem hw hS₁ hw₁
  obtain ⟨j₂, rfl⟩ := eq_squareAt_of_mem hw hS₂ hw₂
  rcases le_total j₁ j₂ with h | h
  · exact Or.inl (squareAt_mono h₁ h₂ hw h)
  · exact Or.inr (squareAt_mono h₁ h₂ hw h)

/-- **The root of the exterior mass at level `m` is the root of the full mass at level `m + d`**, once the capped
square of the full mass at level `m + d` contains the disc `K` and the exterior mass is the full mass minus `d`
on the squares containing `K`. -/
theorem rootSample_eq_of_shift {ν ν' : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤)
    (hν' : ∀ K : Set ℂ, IsCompact K → ν' K < ⊤) {q : ZeroConeRoot.DyCoord} (hc₁ : IsCompatible q.2.1)
    (hc₂ : IsCompatible q.2.2) (hw : IsOffGrid q.1 q.2.1 q.2.2 0) {m d : ℝ≥0∞} (hd : d ≠ ⊤)
    {K S : Set ℂ} (hrel : ∀ S' ∈ dyadicSquares q.1 q.2.1 q.2.2, K ⊆ S' → ν S' = ν' S' + d)
    (hS : IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) (m + d) 0 S) (hK : K ⊆ S) (u : ℝ × ℝ) :
    ZeroConeRoot.rootSample ν' q m u = ZeroConeRoot.rootSample ν q (m + d) u := by
  have hS' := isCappedSquare_of_shift (ν' := ⇑ν') hd (dyadic_nest hc₁ hc₂ hw) hrel hS hK
  have e₁ := (ZeroConeRoot.rootGen_spec hν hw hS).2
  have e₂ := (ZeroConeRoot.rootGen_spec hν' hw hS').2
  rw [hS.cappedSquare_eq] at e₁
  rw [hS'.cappedSquare_eq] at e₂
  have e := e₁.symm.trans e₂
  simp only [squareAt, Complex.zero_re, Complex.zero_im] at e
  obtain ⟨h1, h2, h3⟩ := cornerSquare_inj (by positivity) (by positivity) e
  unfold ZeroConeRoot.rootSample ZeroConeRoot.chainPoint
  rw [h1, h2, h3]

/-- The mass outside a measurable set `U` is the full mass minus the mass of the complement, on the sets
containing the complement. -/
theorem measure_eq_restrict_add {ν : Measure ℂ} {U K : Set ℂ} (hU : MeasurableSet U) (hKU : Uᶜ = K)
    {S' : Set ℂ} (hS' : K ⊆ S') : ν S' = ν.restrict U S' + ν K := by
  rw [Measure.restrict_apply' hU, ← measure_inter_add_sdiff S' hU]
  have : S' \ U = K := by
    ext z
    constructor
    · rintro ⟨_, hz⟩
      rw [← hKU]
      exact hz
    · intro hz
      refine ⟨hS' hz, ?_⟩
      rw [← hKU] at hz
      exact hz
  rw [this]

end Shift

/-! ### The exterior mean is close to the shifted mean -/

section Closeness

open LatticeProb.DyadicOffset (IsCompatible IsOffGrid IsExhaustive squareAt dyadicSquares isCompact_cornerSquare)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- The mean of two bounded observations which agree outside a disc `{|z| ≤ R}` differ by at most the bound times the
probability that the uniform root lies in the disc. -/
theorem abs_rootMean_sub_le {J J' : ℂ → ℝ} (hJ : Measurable J) (hJ' : Measurable J') {K : ℝ}
    (h0 : ∀ z, 0 ≤ J z) (hK : ∀ z, J z ≤ K) (h0' : ∀ z, 0 ≤ J' z) (hK' : ∀ z, J' z ≤ K) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → J z = J' z) (ν : Measure ℂ) (q : ZeroConeRoot.DyCoord) (m : ℝ≥0∞) :
    |rootMean J ν q m - rootMean J' ν q m| ≤ K * (ZeroConeRoot.nearMass ν q m R).toReal := by
  have hz : Measurable fun u : ℝ × ℝ => ZeroConeRoot.rootSample ν q m u :=
    ZeroConeRoot.measurable_rootSample_comp (N := fun _ : ℝ × ℝ => ν) (q := fun _ => q) measurable_const
      measurable_const measurable_id m
  have hI : Integrable (fun u => J (ZeroConeRoot.rootSample ν q m u)) ZeroConeRoot.unifSquareLaw :=
    integrable_of_abs_le (hJ.comp hz) fun u => by
      rw [abs_of_nonneg (h0 _)]
      exact hK _
  have hI' : Integrable (fun u => J' (ZeroConeRoot.rootSample ν q m u)) ZeroConeRoot.unifSquareLaw :=
    integrable_of_abs_le (hJ'.comp hz) fun u => by
      rw [abs_of_nonneg (h0' _)]
      exact hK' _
  have hset : MeasurableSet {u : ℝ × ℝ | ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R} :=
    measurableSet_le hz.norm measurable_const
  have hint : Integrable ({u : ℝ × ℝ | ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R}.indicator fun _ => K)
      ZeroConeRoot.unifSquareLaw := (integrable_const K).indicator hset
  have hmain : ‖∫ u, (J (ZeroConeRoot.rootSample ν q m u) - J' (ZeroConeRoot.rootSample ν q m u))
        ∂ZeroConeRoot.unifSquareLaw‖ ≤
      ∫ u, {u : ℝ × ℝ | ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R}.indicator (fun _ => K) u
        ∂ZeroConeRoot.unifSquareLaw := by
    refine norm_integral_le_of_norm_le hint (ae_of_all _ fun u => ?_)
    by_cases hu : ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R
    · rw [indicator_of_mem (show u ∈ {u : ℝ × ℝ | ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R} from hu),
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h0 (ZeroConeRoot.rootSample ν q m u), hK (ZeroConeRoot.rootSample ν q m u),
        h0' (ZeroConeRoot.rootSample ν q m u), hK' (ZeroConeRoot.rootSample ν q m u)]
    · rw [indicator_of_notMem (show u ∉ {u : ℝ × ℝ | ‖ZeroConeRoot.rootSample ν q m u‖ ≤ R} from hu),
        hR _ (not_le.1 hu), sub_self]
      simp
  calc |rootMean J ν q m - rootMean J' ν q m|
      = ‖∫ u, (J (ZeroConeRoot.rootSample ν q m u) - J' (ZeroConeRoot.rootSample ν q m u))
        ∂ZeroConeRoot.unifSquareLaw‖ := by
        rw [rootMean, rootMean, ← integral_sub hI hI', Real.norm_eq_abs]
    _ ≤ _ := hmain
    _ = K * (ZeroConeRoot.nearMass ν q m R).toReal := by
        rw [integral_indicator_const K hset, smul_eq_mul, mul_comm]
        rfl

theorem chainMass_ne_top {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) (q : ZeroConeRoot.DyCoord)
    (j : ℤ) : ZeroConeRoot.chainMass ν q j ≠ ⊤ := by
  rw [ZeroConeRoot.chainMass, ZeroConeRoot.sqMass_eq hν]
  exact (hν _ (isCompact_cornerSquare _ _ _)).ne

/-- **The mean of the exterior observation at level `m` is close to the mean of the local observation at level
`m + d`, for all large `m`.** The two observations agree outside a disc, the root of the shifted level lies in a
fixed disc with a probability tending to `0`, and the capped square of the exterior mass at level `m` is the capped
square of the full mass at level `m + d` once it contains the disc `{|z| ≤ r}`, whose mass is `d`. -/
theorem exists_forall_abs_rootMean_sub_le {ν : Measure ℂ} {U : Set ℂ} {r : ℝ} (hU : MeasurableSet U)
    (hKU : Uᶜ = Metric.closedBall (0 : ℂ) r) (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤)
    {q : ZeroConeRoot.DyCoord} (hc₁ : IsCompatible q.2.1) (hc₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0) (hex₁ : IsExhaustive q.2.1) (hex₂ : IsExhaustive q.2.2)
    (hcap : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ⊤ →
      ∃ S, IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 S)
    {J J' : ℂ → ℝ} (hJ : Measurable J) (hJ' : Measurable J') {K : ℝ} (h0 : ∀ z, 0 ≤ J z)
    (hK : ∀ z, J z ≤ K) (h0' : ∀ z, 0 ≤ J' z) (hK' : ∀ z, J' z ≤ K) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → J z = J' z) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ≥0∞, m₀ ≠ ⊤ ∧ 1 ≤ m₀ ∧ ∀ m : ℝ≥0∞, m₀ ≤ m → m ≠ ⊤ →
      |rootMean J (ν.restrict U) q m - rootMean J' ν q (m + ν (Metric.closedBall (0 : ℂ) r))| ≤ ε := by
  have hKfin : ν (Metric.closedBall (0 : ℂ) r) ≠ ⊤ := (hν _ (isCompact_closedBall 0 r)).ne
  have hν' : ∀ K : Set ℂ, IsCompact K → ν.restrict U K < ⊤ := fun K hK =>
    lt_of_le_of_lt (Measure.restrict_le_self K) (hν K hK)
  obtain ⟨J₁, hJ₁⟩ := closedBall_subset_squareAt (s := q.1) hex₁ hex₂ r
  have hKnn : 0 ≤ K := (h0 0).trans (hK 0)
  set R' : ℝ := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z, R' < ‖z‖ → J z = J' z := fun z hz => hR z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hT : Tendsto (fun n : ℕ => (2 : ℝ) ^ (q.1 + (n : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ q.1 * 2 ^ n) atTop atTop :=
      Tendsto.const_mul_atTop (Real.rpow_pos_of_pos two_pos q.1) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    refine h1.congr fun n => ?_
    rw [Real.rpow_add two_pos, Real.rpow_natCast]
  have hev := ((tendsto_const_nhds (x := K * (2 * R'))).div_atTop hT).eventually (ge_mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  set Jg : ℤ := max J₁ (n : ℤ) with hJg
  refine ⟨ZeroConeRoot.chainMass ν q Jg + 1, ENNReal.add_ne_top.2 ⟨chainMass_ne_top hν q Jg, ENNReal.one_ne_top⟩,
    le_add_self, fun m hm hmT => ?_⟩
  set d : ℝ≥0∞ := ν (Metric.closedBall (0 : ℂ) r) with hd
  have hm1 : 1 ≤ m := le_add_self.trans hm
  have hm0 : m + d ≠ 0 := (zero_lt_one.trans_le (hm1.trans le_self_add)).ne'
  have hmT' : m + d ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hmT, hKfin⟩
  obtain ⟨S, hS⟩ := hcap (m + d) hm0 hmT'
  have hspec := ZeroConeRoot.rootGen_spec hν hw hS
  have hgen : Jg ≤ ZeroConeRoot.rootGen ν q (m + d) := by
    refine hspec.1.2 ?_
    show ZeroConeRoot.chainMass ν q Jg ≤ m + d
    exact (le_self_add.trans hm).trans le_self_add
  have hSeq : S = squareAt q.1 q.2.1 q.2.2 (ZeroConeRoot.rootGen ν q (m + d)) 0 := by
    rw [← hS.cappedSquare_eq]
    exact hspec.2
  have hKS : Metric.closedBall (0 : ℂ) r ⊆ S := by
    rw [hSeq]
    exact hJ₁ _ ((le_max_left _ _).trans hgen)
  have hrel : ∀ S' ∈ dyadicSquares q.1 q.2.1 q.2.2, Metric.closedBall (0 : ℂ) r ⊆ S' →
      ν S' = ν.restrict U S' + d := fun S' _ hS'K => measure_eq_restrict_add hU hKU hS'K
  have hshift := rootSample_eq_of_shift hν hν' hc₁ hc₂ hw hKfin hrel hS hKS
  have hmean : rootMean J (ν.restrict U) q m = rootMean J ν q (m + d) := by
    unfold rootMean
    simp only [hshift]
  rw [hmean]
  refine (abs_rootMean_sub_le hJ hJ' h0 hK h0' hK' hR' ν q (m + d)).trans ?_
  have hnm := ZeroConeRoot.nearMass_le ν q (m + d) R'
  have hpos : ∀ x : ℝ, 0 < (2 : ℝ) ^ (q.1 + x) := fun x => Real.rpow_pos_of_pos two_pos _
  have hnR : (n : ℝ) ≤ ((ZeroConeRoot.rootGen ν q (m + d) : ℤ) : ℝ) := by
    have h1 : (n : ℤ) ≤ ZeroConeRoot.rootGen ν q (m + d) := (le_max_right _ _).trans hgen
    have h2 : (((n : ℤ) : ℤ) : ℝ) ≤ ((ZeroConeRoot.rootGen ν q (m + d) : ℤ) : ℝ) := Int.cast_le.2 h1
    simpa using h2
  have hpow : (2 : ℝ) ^ (q.1 + (n : ℝ)) ≤ (2 : ℝ) ^ (q.1 + ((ZeroConeRoot.rootGen ν q (m + d) : ℤ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hreal : (ZeroConeRoot.nearMass ν q (m + d) R').toReal ≤
      2 * R' / (2 : ℝ) ^ (q.1 + (n : ℝ)) := by
    refine ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hnm).trans ?_)
    rw [ENNReal.toReal_ofReal (div_nonneg (by linarith) (hpos _).le)]
    exact div_le_div_of_nonneg_left (by linarith) (hpos _) hpow
  calc K * (ZeroConeRoot.nearMass ν q (m + d) R').toReal
      ≤ K * (2 * R' / (2 : ℝ) ^ (q.1 + (n : ℝ))) := mul_le_mul_of_nonneg_left hreal hKnn
    _ = K * (2 * R') / (2 : ℝ) ^ (q.1 + (n : ℝ)) := (mul_div_assoc _ _ _).symm
    _ ≤ ε := hn

end Closeness

/-! ### Cesàro averages -/

section Cesaro

theorem intervalIntegrable_of_abs_le {A : ℝ → ℝ} (hA : Measurable A) {K : ℝ} (hK : ∀ m, |A m| ≤ K)
    (a b : ℝ) : IntervalIntegrable A volume a b :=
  ⟨Integrable.of_bound hA.aestronglyMeasurable K (ae_of_all _ fun x => by simpa using hK x),
    Integrable.of_bound hA.aestronglyMeasurable K (ae_of_all _ fun x => by simpa using hK x)⟩

/-- **The averages over `[N, 2N]` of two bounded functions, one of which is the shift by `d` of the other up to an
error `ε` for large arguments, differ by at most `2 K d / N + ε`.** -/
theorem abs_cesaro_sub_le {A B : ℝ → ℝ} (hA : Measurable A) (hB : Measurable B) {K ε d m₀ N : ℝ}
    (hd : 0 ≤ d) (hAK : ∀ m, |A m| ≤ K) (hBK : ∀ m, |B m| ≤ K)
    (hε : ∀ m, m₀ ≤ m → |B m - A (m + d)| ≤ ε) (hN : 0 < N) (hNm : m₀ ≤ N) :
    |N⁻¹ * (∫ m in N..2 * N, A m) - N⁻¹ * ∫ m in N..2 * N, B m| ≤ 2 * K * d / N + ε := by
  have hAi := intervalIntegrable_of_abs_le hA hAK
  have hBi := intervalIntegrable_of_abs_le hB hBK
  have hAdm : Measurable fun m => A (m + d) := hA.comp (measurable_id.add_const d)
  have hAdi := intervalIntegrable_of_abs_le hAdm (fun m => hAK _)
  have hshift : ∫ m in N..2 * N, A (m + d) = ∫ m in N + d..2 * N + d, A m :=
    intervalIntegral.integral_comp_add_right A d
  have hsplit1 : (∫ m in N..N + d, A m) + ∫ m in N + d..2 * N + d, A m = ∫ m in N..2 * N + d, A m :=
    intervalIntegral.integral_add_adjacent_intervals (hAi _ _) (hAi _ _)
  have hsplit2 : (∫ m in N..2 * N, A m) + ∫ m in 2 * N..2 * N + d, A m = ∫ m in N..2 * N + d, A m :=
    intervalIntegral.integral_add_adjacent_intervals (hAi _ _) (hAi _ _)
  have hb1 : ‖∫ m in N..N + d, A m‖ ≤ K * |N + d - N| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by simpa using hAK x
  have hb2 : ‖∫ m in 2 * N..2 * N + d, A m‖ ≤ K * |2 * N + d - 2 * N| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by simpa using hAK x
  have hd1 : |N + d - N| = d := by rw [add_sub_cancel_left, abs_of_nonneg hd]
  have hd2 : |2 * N + d - 2 * N| = d := by rw [add_sub_cancel_left, abs_of_nonneg hd]
  rw [hd1] at hb1
  rw [hd2] at hb2
  have hKnn : 0 ≤ K := (abs_nonneg _).trans (hAK 0)
  have hdiff : |(∫ m in N..2 * N, A m) - ∫ m in N..2 * N, A (m + d)| ≤ 2 * K * d := by
    have : (∫ m in N..2 * N, A m) - ∫ m in N..2 * N, A (m + d) =
        (∫ m in N..N + d, A m) - ∫ m in 2 * N..2 * N + d, A m := by
      rw [hshift]
      linarith
    rw [this]
    have := abs_sub (∫ m in N..N + d, A m) (∫ m in 2 * N..2 * N + d, A m)
    simp only [Real.norm_eq_abs] at hb1 hb2
    linarith
  have hdiff2 : |(∫ m in N..2 * N, A (m + d)) - ∫ m in N..2 * N, B m| ≤ ε * N := by
    rw [← intervalIntegral.integral_sub (hAdi _ _) (hBi _ _)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := N) (b := 2 * N) (C := ε)
      (f := fun m => A (m + d) - B m) fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hε x (hNm.trans hx.1.le)
    have h2 : |2 * N - N| = N := by rw [two_mul, add_sub_cancel_left, abs_of_pos hN]
    rw [h2, Real.norm_eq_abs] at h
    linarith
  have hsum : |(∫ m in N..2 * N, A m) - ∫ m in N..2 * N, B m| ≤ 2 * K * d + ε * N := by
    have := abs_add_le ((∫ m in N..2 * N, A m) - ∫ m in N..2 * N, A (m + d))
      ((∫ m in N..2 * N, A (m + d)) - ∫ m in N..2 * N, B m)
    rw [sub_add_sub_cancel] at this
    linarith
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN)]
  calc N⁻¹ * |(∫ m in N..2 * N, A m) - ∫ m in N..2 * N, B m|
      ≤ N⁻¹ * (2 * K * d + ε * N) := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hN).le
    _ = 2 * K * d / N + ε := by field_simp

end Cesaro

/-! ### The Cesàro approximation -/

section CesaroApprox

/-- Interval integrals of a jointly measurable function are measurable in the parameter. -/
theorem measurable_intervalIntegral {α : Type*} [MeasurableSpace α] {f : α × ℝ → ℝ} (hf : Measurable f)
    (a b : ℝ) : Measurable fun x => ∫ m in a..b, f (x, m) := by
  simp only [intervalIntegral]
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc a b))).measurable.sub
    (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc b a))).measurable

theorem abs_cesaro_le {A : ℝ → ℝ} {K : ℝ} (hK : ∀ m, |A m| ≤ K) {N : ℝ} (hN : 0 ≤ N) :
    |N⁻¹ * ∫ m in N..2 * N, A m| ≤ K := by
  rcases hN.eq_or_lt with h | h
  · subst h
    rw [inv_zero, zero_mul, abs_zero]
    exact (abs_nonneg _).trans (hK 0)
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := N) (b := 2 * N) (C := K) (f := A)
      fun x _ => by simpa using hK x
    have h2 : |2 * N - N| = N := by rw [two_mul, add_sub_cancel_left, abs_of_pos h]
    rw [h2, Real.norm_eq_abs] at hb
    rw [abs_mul, abs_of_pos (inv_pos.2 h)]
    calc N⁻¹ * |∫ m in N..2 * N, A m| ≤ N⁻¹ * (K * N) :=
          mul_le_mul_of_nonneg_left hb (inv_pos.2 h).le
      _ = K := by field_simp

/-- **The averages over `[N, 2N]` of the observation at levels `m` approximate `F` in `L¹` up to `δ + η`**, for
large `N`, when the observation `a` at level `m` approximates `F` up to `δ` for every `m > 0` and the observation
`e` is, up to a vanishing error, the shift of `a` by a finite `d(x)`. -/
theorem exists_cesaro_approx {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {F : α → ℝ} (hF : Measurable F) {K δ : ℝ} (hF0 : ∀ x, 0 ≤ F x) (hFK : ∀ x, F x ≤ K)
    {a e : α × ℝ → ℝ} (ha : Measurable a) (he : Measurable e) (ha0 : ∀ x, 0 ≤ a x) (haK : ∀ x, a x ≤ K)
    (he0 : ∀ x, 0 ≤ e x) (heK : ∀ x, e x ≤ K)
    (hR3 : ∀ m : ℝ, 0 < m → ∫ x, |F x - a (x, m)| ∂P ≤ δ) {d : α → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hclose : ∀ᵐ x ∂P, ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → |e (x, m) - a (x, m + d x)| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∫ x, |F x - (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, e (x, m)| ∂P ≤ δ + η := by
  have habs_a : ∀ x, |a x| ≤ K := fun x => by rw [abs_of_nonneg (ha0 x)]; exact haK x
  have habs_e : ∀ x, |e x| ≤ K := fun x => by rw [abs_of_nonneg (he0 x)]; exact heK x
  have hsec_a : ∀ x : α, Measurable fun m : ℝ => a (x, m) := fun x =>
    ha.comp (measurable_const.prodMk measurable_id)
  have hsec_e : ∀ x : α, Measurable fun m : ℝ => e (x, m) := fun x =>
    he.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ : ∃ C : ℕ → α → ℝ, ∀ N x, C N x = (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, a (x, m) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → α → ℝ, ∀ N x, B N x = (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, e (x, m) :=
    ⟨_, fun _ _ => rfl⟩
  have hCm : ∀ N : ℕ, Measurable (C N) := fun N => by
    have := (measurable_intervalIntegral ha (N : ℝ) (2 * N)).const_mul ((N : ℝ)⁻¹)
    convert this using 1
    funext x
    exact hC N x
  have hBm : ∀ N : ℕ, Measurable (B N) := fun N => by
    have := (measurable_intervalIntegral he (N : ℝ) (2 * N)).const_mul ((N : ℝ)⁻¹)
    convert this using 1
    funext x
    exact hB N x
  have hCb : ∀ (N : ℕ) x, |C N x| ≤ K := fun N x => by
    rw [hC]
    exact abs_cesaro_le (A := fun m => a (x, m)) (fun m => habs_a _) (Nat.cast_nonneg N)
  have hBb : ∀ (N : ℕ) x, |B N x| ≤ K := fun N x => by
    rw [hB]
    exact abs_cesaro_le (A := fun m => e (x, m)) (fun m => habs_e _) (Nat.cast_nonneg N)
  have hFb : ∀ x, |F x| ≤ K := fun x => by rw [abs_of_nonneg (hF0 x)]; exact hFK x
  have hFCm : ∀ N : ℕ, Measurable fun x => |F x - C N x| := fun N => (hF.sub (hCm N)).abs
  have hFCb : ∀ (N : ℕ) x, |(|F x - C N x|)| ≤ 2 * K := fun N x => by
    rw [abs_abs]
    calc |F x - C N x| ≤ |F x| + |C N x| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hFb x, hCb N x]
  have hCBm : ∀ N : ℕ, Measurable fun x => |C N x - B N x| := fun N => ((hCm N).sub (hBm N)).abs
  have hCBb : ∀ (N : ℕ) x, |(|C N x - B N x|)| ≤ 2 * K := fun N x => by
    rw [abs_abs]
    calc |C N x - B N x| ≤ |C N x| + |B N x| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hBb N x, hCb N x]
  have hFBm : ∀ N : ℕ, Measurable fun x => |F x - B N x| := fun N => (hF.sub (hBm N)).abs
  have hFBb : ∀ (N : ℕ) x, |(|F x - B N x|)| ≤ 2 * K := fun N x => by
    rw [abs_abs]
    calc |F x - B N x| ≤ |F x| + |B N x| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hFb x, hBb N x]
  -- the first error: `F` against the average of `a`
  have hstep1 : ∀ N : ℕ, 0 < N → ∫ x, |F x - C N x| ∂P ≤ δ := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨W, hW⟩ : ∃ W : α × ℝ → ℝ, ∀ p, W p = |F p.1 - a p| := ⟨_, fun _ => rfl⟩
    have hWm : Measurable W := by
      have := ((hF.comp measurable_fst).sub ha).abs
      convert this using 1
      funext p
      exact hW p
    have hWb : ∀ p, |W p| ≤ K := fun p => by
      rw [hW, abs_abs, abs_le]
      constructor <;> linarith [hF0 p.1, hFK p.1, ha0 p, haK p]
    have hpt : ∀ x, |F x - C N x| ≤ (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, W (x, m) := by
      intro x
      have hFx : F x = (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, F x := by
        rw [intervalIntegral.integral_const, smul_eq_mul, two_mul, add_sub_cancel_left]
        field_simp
      have hdiff : F x - C N x = (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, (F x - a (x, m)) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          (intervalIntegrable_of_abs_le (hsec_a x) (fun m => habs_a _) _ _), mul_sub, ← hFx, hC]
      rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hNr)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hNr).le
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith)) (le_of_eq ?_)
      refine intervalIntegral.integral_congr fun m _ => ?_
      exact (hW (x, m)).symm
    have hWi : Measurable fun x => (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, W (x, m) :=
      (measurable_intervalIntegral hWm _ _).const_mul _
    have hWbd : ∀ x, |(N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, W (x, m)| ≤ K := fun x =>
      abs_cesaro_le (A := fun m => W (x, m)) (fun m => hWb _) hNr.le
    refine (integral_mono (integrable_of_abs_le (hFCm N) (hFCb N)) (integrable_of_abs_le hWi hWbd) hpt).trans ?_
    rw [integral_const_mul]
    have hswap : ∫ x, (∫ m in (N : ℝ)..2 * N, W (x, m)) ∂P =
        ∫ m in (N : ℝ)..2 * N, (∫ x, W (x, m) ∂P) := by
      simp only [intervalIntegral.integral_of_le (show (N : ℝ) ≤ 2 * N by linarith)]
      refine integral_integral_swap ?_
      exact Integrable.of_bound hWm.aestronglyMeasurable K
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hWb p)
    rw [hswap]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ)) (b := 2 * N) (C := δ)
      (f := fun m => ∫ x, W (x, m) ∂P) fun m hm => by
        rw [Set.uIoc_of_le (by linarith)] at hm
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => by rw [hW]; exact abs_nonneg _)]
        have := hR3 m (lt_of_lt_of_le hNr hm.1.le)
        simpa [hW] using this
    have h2 : |2 * (N : ℝ) - N| = N := by rw [two_mul, add_sub_cancel_left, abs_of_pos hNr]
    rw [h2, Real.norm_eq_abs] at hb
    calc (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, (∫ x, W (x, m) ∂P) ≤ (N : ℝ)⁻¹ * (δ * N) :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hb) (inv_pos.2 hNr).le
      _ = δ := by field_simp
  -- the second error: the averages of `a` and `e`
  have hstep2 : Tendsto (fun N : ℕ => ∫ x, |C N x - B N x| ∂P) atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂P, Tendsto (fun N : ℕ => |C N x - B N x|) atTop (𝓝 0) := by
      filter_upwards [hclose] with x hx
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨m₀, hm₀⟩ := hx (ε / 4) (by positivity)
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max m₀ 1) (4 * K * d x / ε))
      refine ⟨N₀, fun N hN => ?_⟩
      have hNN : (N₀ : ℝ) ≤ N := Nat.cast_le.2 hN
      have h1 : m₀ < N := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) (hN₀.trans_le hNN)
      have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (zero_le_one.trans ((le_max_right _ _).trans
        (le_max_left _ _))) (hN₀.trans_le hNN)
      have h4 : 4 * K * d x / ε < N := lt_of_le_of_lt (le_max_right _ _) (hN₀.trans_le hNN)
      have hbound := abs_cesaro_sub_le (hsec_a x) (hsec_e x) (K := K) (ε := ε / 4) (d := d x) (m₀ := m₀)
        (N := (N : ℝ)) (hd x) (fun m => habs_a _) (fun m => habs_e _) hm₀ hNpos h1.le
      rw [Real.dist_eq, sub_zero, abs_abs, hC, hB]
      have h5 : 2 * K * d x / N ≤ ε / 2 := by
        rw [div_le_iff₀ hNpos]
        have := (div_lt_iff₀ hε).1 h4
        nlinarith
      linarith
    have hdc := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun (N : ℕ) x => |C N x - B N x|) (f := fun _ => (0 : ℝ)) (fun _ => 2 * K)
      (fun N => (hCBm N).aestronglyMeasurable) (integrable_const _)
      (fun N => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hCBb N x) hlim
    simpa using hdc
  have hev : ∀ᶠ N : ℕ in atTop, ∫ x, |C N x - B N x| ∂P < η := hstep2.eventually (gt_mem_nhds hη)
  obtain ⟨N, hN1, hN2⟩ := (hev.and (eventually_gt_atTop 0)).exists
  refine ⟨N, hN2, ?_⟩
  have hpt : ∀ x, |F x - B N x| ≤ |F x - C N x| + |C N x - B N x| := fun x => by
    have := abs_add_le (F x - C N x) (C N x - B N x)
    rwa [sub_add_sub_cancel] at this
  have hfinal : ∫ x, |F x - B N x| ∂P ≤ δ + η := by
    calc ∫ x, |F x - B N x| ∂P ≤ ∫ x, (|F x - C N x| + |C N x - B N x|) ∂P :=
          integral_mono (integrable_of_abs_le (hFBm N) (hFBb N))
            ((integrable_of_abs_le (hFCm N) (hFCb N)).add (integrable_of_abs_le (hCBm N) (hCBb N))) hpt
      _ = ∫ x, |F x - C N x| ∂P + ∫ x, |C N x - B N x| ∂P :=
          integral_add (integrable_of_abs_le (hFCm N) (hFCb N)) (integrable_of_abs_le (hCBm N) (hCBb N))
      _ ≤ δ + η := by linarith [hstep1 N hN2]
  simpa only [hB] using hfinal

end CesaroApprox

/-! ### Integrating out the independent dyadic system -/

section Integrate

/-- **Jensen for the independent variable**: the `L¹` distance from `F` to the average over the independent
variable of a bounded jointly measurable function is at most the `L¹` distance on the product. -/
theorem lintegral_abs_sub_integral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {Q : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q] {F : α → ℝ} (hF : Measurable F)
    {B : α × β → ℝ} (hB : Measurable B) {K : ℝ} (hFK : ∀ x, |F x| ≤ K) (hBK : ∀ p, |B p| ≤ K) :
    ∫⁻ x, ENNReal.ofReal |F x - ∫ y, B (x, y) ∂Q| ∂μ ≤
      ENNReal.ofReal (∫ p, |F p.1 - B p| ∂μ.prod Q) := by
  have hgm : Measurable fun x => ∫ y, B (x, y) ∂Q :=
    hB.stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ x, |∫ y, B (x, y) ∂Q| ≤ K := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := Q) (f := fun y => B (x, y)) (C := K)
      (ae_of_all _ fun y => by simpa using hBK (x, y))
    simpa using this
  have hI : Measurable fun x => |F x - ∫ y, B (x, y) ∂Q| := (hF.sub hgm).abs
  have hIb : ∀ x, |(|F x - ∫ y, B (x, y) ∂Q|)| ≤ 2 * K := fun x => by
    rw [abs_abs]
    calc |F x - ∫ y, B (x, y) ∂Q| ≤ |F x| + |∫ y, B (x, y) ∂Q| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hFK x, hgb x]
  have hIint : Integrable (fun x => |F x - ∫ y, B (x, y) ∂Q|) μ := integrable_of_abs_le hI hIb
  rw [← ofReal_integral_eq_lintegral_ofReal hIint (ae_of_all _ fun x => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hPm : Measurable fun p : α × β => |F p.1 - B p| := ((hF.comp measurable_fst).sub hB).abs
  have hPint : Integrable (fun p : α × β => |F p.1 - B p|) (μ.prod Q) :=
    integrable_of_abs_le hPm (K := 2 * K) fun p => by
      rw [abs_abs]
      calc |F p.1 - B p| ≤ |F p.1| + |B p| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hFK p.1, hBK p]
  rw [integral_prod _ hPint]
  refine integral_mono hIint hPint.integral_prod_left (fun x => ?_)
  have hBx : Integrable (fun y => B (x, y)) Q :=
    integrable_of_abs_le (hB.comp (measurable_const.prodMk measurable_id)) fun y => hBK _
  exact abs_sub_integral_le_integral_abs_sub hBx (F x)

end Integrate

/-! ### The exterior version of the average -/

section Main

open LatticeProb.DyadicOffset (IsCompatible IsOffGrid IsExhaustive dyadicSquares offsetLaw unifIco
  ae_isCompatible_isOffGrid_system ae_isExhaustive_offsetLaw)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- The complement of the open exterior `{|w| > r}` is the closed disc of radius `r`. -/
theorem extOpen_compl (r : ℝ) :
    ((extOpen r : TopologicalSpace.Opens ℂ) : Set ℂ)ᶜ = Metric.closedBall (0 : ℂ) r := by
  ext w
  simp [extOpen, not_lt]

/-- Almost every uniform dyadic system has exhaustive offsets in both coordinates. -/
theorem ae_isExhaustive_uniformDyadicLaw :
    ∀ᵐ q ∂ZeroConeRoot.uniformDyadicLaw, IsExhaustive q.2.1 ∧ IsExhaustive q.2.2 := by
  have h1 : ∀ᵐ z ∂(offsetLaw.prod offsetLaw), IsExhaustive z.1 :=
    ZeroConeRoot.ae_prod_fst_of_ae ae_isExhaustive_offsetLaw
  have h2 : ∀ᵐ z ∂(offsetLaw.prod offsetLaw), IsExhaustive z.2 :=
    ZeroConeRoot.ae_prod_snd_of_ae ae_isExhaustive_offsetLaw
  exact ZeroConeRoot.ae_prod_snd_of_ae (μ := unifIco 1) (ν := offsetLaw.prod offsetLaw)
    (p := fun z => IsExhaustive z.1 ∧ IsExhaustive z.2) (by filter_upwards [h1, h2] with z a b; exact ⟨a, b⟩)

/-- **The `L¹` approximation of `F` by the Cesàro average of the exterior observation** (Lemma A.1 of
Gwynne–Miller–Sheffield, arXiv:1705.11161, Appendix A, Step 4; written answer 58, section 3, fourth and fifth
paragraphs). Let `F` be bounded, `f` the local observation, and suppose that the average `A_m` of the local
observation over the capped square of level `m` of an independent uniform dyadic system approximates `F` up to `δ`
(`hR3`), that the area measure has almost surely infinite mass in each of the eight sectors, and that the
area measure of the exterior `{|w| > k + 1}` and the local observation at the points `z` with mass radius below
`|z| - (k + 2)` are measurable functions of the restriction of the field to `{|w| > k}` (`hD`, `hG`). Then `F` is
approximated up to `δ + η` in `L¹` by a function measurable for the exterior σ-algebra `extSigma k`: the
average over the independent dyadic system and over the levels `m ∈ [N, 2N]` of the exterior averages `A_m^k`,
for `N` large (`S^k_m = S_{m + d}` for large `m`, `d` the mass of the disc `{|w| ≤ k + 1}`). -/
theorem exists_extVersion_approx (γ : ℝ) {μ : Measure Field} [IsProbabilityMeasure μ] {F : Field → ℝ}
    (hFm : Measurable F) {K : ℝ} (hF0 : ∀ h, 0 ≤ F h) (hFK : ∀ h, F h ≤ K) {a : ℕ}
    {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfK : ∀ x, f x ≤ K)
    {b₀ δ : ℝ} (hgood : ∀ᵐ h ∂μ, h ∈ ConeAreaCovariance.goodSet γ)
    (hsec : ∀ᵐ h ∂μ, ∀ j : Fin 8, ConeAreaCovariance.areaMap γ h (a1Sector j) = ⊤)
    (hfin : ∀ᵐ h ∂μ, IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ h))
    (hA2 : ∀ᵐ p ∂μ.prod ZeroConeRoot.uniformDyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ⊤ →
      ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(ConeAreaCovariance.areaMap γ p.1)) m 0 S)
    (hR3 : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ⊤ →
      ∫ p, |F p.1 - rootAverage γ f b₀ m p.1 p.2| ∂μ.prod ZeroConeRoot.uniformDyadicLaw ≤ δ)
    (k : ℕ)
    (hD : ∃ D : LQGMetric.DistOn (extOpen (k : ℝ)) → Measure ℂ, Measurable D ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ,
        D (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (ConeAreaCovariance.areaMap γ h).restrict (extOpen ((k : ℝ) + 1)))
    (hG : ∃ G : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ → ℝ, Measurable G ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ, ∀ z : ℂ,
        ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) b₀ z < ‖z‖ - ((k : ℝ) + 2) →
          G (LQGMetric.restrictTo (extOpen (k : ℝ)) h, z) = rootObs γ f b₀ h z)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : Field → ℝ, StronglyMeasurable[extSigma (k : ℝ)] g ∧
      ∫⁻ h, ENNReal.ofReal |F h - g h| ∂μ ≤ ENNReal.ofReal (δ + η) := by
  classical
  have hK : 0 ≤ K := (hF0 0).trans (hFK 0)
  obtain ⟨D, hDm, hDe⟩ := hD
  obtain ⟨G, hGm, hGe⟩ := hG
  -- the truncated exterior observation
  obtain ⟨G', hG'⟩ : ∃ G' : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ → ℝ, ∀ p, G' p = max 0 (min (G p) K) :=
    ⟨_, fun _ => rfl⟩
  have hG'm : Measurable G' := by
    have := (measurable_const (a := (0 : ℝ))).max (hGm.min (measurable_const (a := K)))
    convert this using 1
    funext p
    exact hG' p
  have hG'0 : ∀ p, 0 ≤ G' p := fun p => by rw [hG']; exact le_max_left _ _
  have hG'K : ∀ p, G' p ≤ K := fun p => by rw [hG']; exact max_le hK (min_le_right _ _)
  obtain ⟨E, hE⟩ : ∃ E : LQGMetric.DistOn (extOpen (k : ℝ)) → ZeroConeRoot.DyCoord → ℝ≥0∞ → ℝ,
      ∀ T q m, E T q m = rootMean (fun z => G' (T, z)) (D T) q m := ⟨_, fun _ _ _ => rfl⟩
  have hEm : Measurable fun p : (LQGMetric.DistOn (extOpen (k : ℝ)) × ZeroConeRoot.DyCoord) × ℝ =>
      E p.1.1 p.1.2 (ENNReal.ofReal p.2) := by
    have h1 := measurable_rootMean (β := (LQGMetric.DistOn (extOpen (k : ℝ)) × ZeroConeRoot.DyCoord) × ℝ)
      (X := LQGMetric.DistOn (extOpen (k : ℝ))) hG'm (x := fun b => b.1.1) (N := fun b => D b.1.1)
      (q := fun b => b.1.2) (m := fun b => ENNReal.ofReal b.2) measurable_fst.fst (hDm.comp measurable_fst.fst)
      measurable_fst.snd (ENNReal.measurable_ofReal.comp measurable_snd)
    convert h1 using 1
    funext p
    exact hE _ _ _
  -- the data on the product of the field and the dyadic system
  obtain ⟨Aobs, hAobs⟩ : ∃ A : (Field × ZeroConeRoot.DyCoord) × ℝ → ℝ, ∀ p, A p =
      rootMean (rootObs γ f b₀ p.1.1) (ConeAreaCovariance.areaMap γ p.1.1) p.1.2 (ENNReal.ofReal p.2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Eext, hEext⟩ : ∃ A : (Field × ZeroConeRoot.DyCoord) × ℝ → ℝ, ∀ p, A p =
      E (LQGMetric.restrictTo (extOpen (k : ℝ)) p.1.1) p.1.2 (ENNReal.ofReal p.2) := ⟨_, fun _ => rfl⟩
  obtain ⟨dd, hdd⟩ : ∃ d : Field × ZeroConeRoot.DyCoord → ℝ, ∀ x, d x =
      (ConeAreaCovariance.areaMap γ x.1 (Metric.closedBall (0 : ℂ) ((k : ℝ) + 1))).toReal :=
    ⟨_, fun _ => rfl⟩
  have hdd0 : ∀ x, 0 ≤ dd x := fun x => by rw [hdd]; exact ENNReal.toReal_nonneg
  have hAm : Measurable Aobs := by
    have h1 := measurable_rootMean (β := (Field × ZeroConeRoot.DyCoord) × ℝ) (X := Field)
      (J := fun p : Field × ℂ => rootObs γ f b₀ p.1 p.2) (measurable_rootObs γ hfm b₀)
      (x := fun b => b.1.1) (N := fun b => ConeAreaCovariance.areaMap γ b.1.1) (q := fun b => b.1.2)
      (m := fun b => ENNReal.ofReal b.2) measurable_fst.fst
      ((ConeAreaCovariance.measurable_areaMap γ).comp measurable_fst.fst) measurable_fst.snd
      (ENNReal.measurable_ofReal.comp measurable_snd)
    convert h1 using 1
    funext p
    exact hAobs p
  have hEextm : Measurable Eext := by
    have h1 := hEm.comp ((((LQGMetric.measurable_restrictTo (extOpen (k : ℝ))).comp measurable_fst.fst).prodMk
      measurable_fst.snd).prodMk measurable_snd)
    convert h1 using 1
    funext p
    exact hEext p
  have ha0 : ∀ x, 0 ≤ Aobs x := fun x => by
    rw [hAobs]
    exact rootMean_nonneg (fun z => rootObs_nonneg γ hf0 b₀ _ z) _ _ _
  have haK : ∀ x, Aobs x ≤ K := fun x => by
    rw [hAobs]
    refine (le_abs_self _).trans (abs_rootMean_le (fun z => ?_) _ _ _)
    rw [abs_of_nonneg (rootObs_nonneg γ hf0 b₀ _ z)]
    exact rootObs_le γ hfK hK b₀ _ z
  have he0 : ∀ x, 0 ≤ Eext x := fun x => by
    rw [hEext, hE]
    exact rootMean_nonneg (fun z => hG'0 _) _ _ _
  have heK : ∀ x, Eext x ≤ K := fun x => by
    rw [hEext, hE]
    refine (le_abs_self _).trans (abs_rootMean_le (fun z => ?_) _ _ _)
    rw [abs_of_nonneg (hG'0 _)]
    exact hG'K _
  -- the approximation at every level
  have hfinμ : ∀ᵐ h ∂μ, ∀ K' : Set ℂ, IsCompact K' → ConeAreaCovariance.areaMap γ h K' < ⊤ :=
    hfin.mono fun h hh K' hK' => by
      have := hh
      exact hK'.measure_lt_top
  have hgp := ZeroConeRoot.ae_goodPair (M := ConeAreaCovariance.areaMap γ) hfinμ hA2
  have hR3' : ∀ m : ℝ, 0 < m →
      ∫ x, |F x.1 - Aobs (x, m)| ∂μ.prod ZeroConeRoot.uniformDyadicLaw ≤ δ := by
    intro m hm
    have hm0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm).ne'
    have haff := ZeroConeRoot.ae_rootSample_affine hgp hm0 ENNReal.ofReal_ne_top
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hR3 (ENNReal.ofReal m) hm0 ENNReal.ofReal_ne_top)
    filter_upwards [haff] with x hx
    have h1 := rootAverage_eq γ hfm b₀ (ENNReal.ofReal m) x.1 x.2 hx
    rw [hAobs]
    dsimp only
    unfold rootMean
    rw [h1]
  -- the exterior observation is close to the shifted observation
  have hgoodP : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw, x.1 ∈ ConeAreaCovariance.goodSet γ :=
    ZeroConeRoot.ae_prod_fst_of_ae hgood
  have hsecP : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw,
      ∀ j : Fin 8, ConeAreaCovariance.areaMap γ x.1 (a1Sector j) = ⊤ :=
    ZeroConeRoot.ae_prod_fst_of_ae hsec
  have hfinP : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw,
      IsFiniteMeasureOnCompacts (ConeAreaCovariance.areaMap γ x.1) := ZeroConeRoot.ae_prod_fst_of_ae hfin
  have hcompP : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw,
      IsCompatible x.2.2.1 ∧ IsCompatible x.2.2.2 ∧ IsOffGrid x.2.1 x.2.2.1 x.2.2.2 0 :=
    ZeroConeRoot.ae_prod_snd_of_ae (p := fun q : ZeroConeRoot.DyCoord =>
      IsCompatible q.2.1 ∧ IsCompatible q.2.2 ∧ IsOffGrid q.1 q.2.1 q.2.2 0)
      (ae_isCompatible_isOffGrid_system 0)
  have hexhP : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw,
      IsExhaustive x.2.2.1 ∧ IsExhaustive x.2.2.2 :=
    ZeroConeRoot.ae_prod_snd_of_ae (p := fun q : ZeroConeRoot.DyCoord =>
      IsExhaustive q.2.1 ∧ IsExhaustive q.2.2) ae_isExhaustive_uniformDyadicLaw
  have hclose : ∀ᵐ x ∂μ.prod ZeroConeRoot.uniformDyadicLaw, ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m →
      |Eext (x, m) - Aobs (x, m + dd x)| ≤ ε := by
    filter_upwards [hgoodP, hsecP, hfinP, hcompP, hexhP, hA2] with x hxg hxs hxf hxc hxe hxcap
    intro ε hε
    have := hxf
    have hν : ∀ K' : Set ℂ, IsCompact K' → ConeAreaCovariance.areaMap γ x.1 K' < ⊤ := fun K' hK' =>
      hK'.measure_lt_top
    obtain ⟨R, hR⟩ := exists_massRadius_lt_norm_sub hxs ((k : ℝ) + 2) b₀
    have hJJ : ∀ z, R < ‖z‖ →
        G' (LQGMetric.restrictTo (extOpen (k : ℝ)) x.1, z) = rootObs γ f b₀ x.1 z := fun z hz => by
      have h1 := hGe x.1 hxg z (hR z hz)
      rw [hG', h1, min_eq_left (rootObs_le γ hfK hK b₀ x.1 z),
        max_eq_right (rootObs_nonneg γ hf0 b₀ x.1 z)]
    obtain ⟨m₀, hm₀T, -, hm₀⟩ := exists_forall_abs_rootMean_sub_le
      (U := ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ)) (r := (k : ℝ) + 1)
      (extOpen ((k : ℝ) + 1)).isOpen.measurableSet (extOpen_compl _) hν hxc.1 hxc.2.1 hxc.2.2 hxe.1 hxe.2
      hxcap (J := fun z => G' (LQGMetric.restrictTo (extOpen (k : ℝ)) x.1, z))
      (J' := fun z => rootObs γ f b₀ x.1 z) (hG'm.comp (measurable_const.prodMk measurable_id))
      (measurable_rootObs_section γ hfm b₀ x.1) (K := K) (fun z => hG'0 _) (fun z => hG'K _)
      (fun z => rootObs_nonneg γ hf0 b₀ _ z) (fun z => rootObs_le γ hfK hK b₀ _ z) hJJ hε
    refine ⟨m₀.toReal, fun m hm => ?_⟩
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg.trans hm
    have hle : m₀ ≤ ENNReal.ofReal m := by
      rw [← ENNReal.ofReal_toReal hm₀T]
      exact ENNReal.ofReal_le_ofReal hm
    have h1 := hm₀ (ENNReal.ofReal m) hle ENNReal.ofReal_ne_top
    have hd : ENNReal.ofReal (m + dd x) = ENNReal.ofReal m +
        ConeAreaCovariance.areaMap γ x.1 (Metric.closedBall (0 : ℂ) ((k : ℝ) + 1)) := by
      rw [ENNReal.ofReal_add hm0 (hdd0 x), hdd, ENNReal.ofReal_toReal (hν _ (isCompact_closedBall _ _)).ne]
    rw [hEext, hAobs, hE, hDe x.1 hxg]
    dsimp only
    rw [hd]
    exact h1
  obtain ⟨N, hNpos, hN⟩ := exists_cesaro_approx (P := μ.prod ZeroConeRoot.uniformDyadicLaw)
    (F := fun x : Field × ZeroConeRoot.DyCoord => F x.1) (hFm.comp measurable_fst) (fun x => hF0 _)
    (fun x => hFK _) hAm hEextm ha0 haK he0 heK hR3' hdd0 hclose hη
  -- the average over the levels and the dyadic system
  obtain ⟨Bf, hBf⟩ : ∃ B : Field × ZeroConeRoot.DyCoord → ℝ, ∀ x,
      B x = (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, Eext (x, m) := ⟨_, fun _ => rfl⟩
  have hBm : Measurable Bf := by
    have := (measurable_intervalIntegral hEextm (N : ℝ) (2 * N)).const_mul ((N : ℝ)⁻¹)
    convert this using 1
    funext x
    exact hBf x
  have hBb : ∀ x, |Bf x| ≤ K := fun x => by
    rw [hBf]
    refine abs_cesaro_le (A := fun m => Eext (x, m)) (fun m => ?_) (Nat.cast_nonneg N)
    rw [abs_of_nonneg (he0 _)]
    exact heK _
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : LQGMetric.DistOn (extOpen (k : ℝ)) × ZeroConeRoot.DyCoord → ℝ, ∀ y, Ψ y =
      (N : ℝ)⁻¹ * ∫ m in (N : ℝ)..2 * N, E y.1 y.2 (ENNReal.ofReal m) := ⟨_, fun _ => rfl⟩
  have hΨm : Measurable Ψ := by
    have := (measurable_intervalIntegral hEm (N : ℝ) (2 * N)).const_mul ((N : ℝ)⁻¹)
    convert this using 1
    funext y
    exact hΨ y
  have hBΨ : ∀ x : Field × ZeroConeRoot.DyCoord,
      Bf x = Ψ (LQGMetric.restrictTo (extOpen (k : ℝ)) x.1, x.2) := fun x => by
    rw [hBf, hΨ]
    simp only [hEext]
  refine ⟨fun h => ∫ q, Ψ (LQGMetric.restrictTo (extOpen (k : ℝ)) h, q) ∂ZeroConeRoot.uniformDyadicLaw,
    ?_, ?_⟩
  · have hΦ : Measurable fun T : LQGMetric.DistOn (extOpen (k : ℝ)) =>
        ∫ q, Ψ (T, q) ∂ZeroConeRoot.uniformDyadicLaw :=
      hΨm.stronglyMeasurable.integral_prod_right'.measurable
    have hmeas : Measurable[extSigma (k : ℝ)] fun h : Field =>
        ∫ q, Ψ (LQGMetric.restrictTo (extOpen (k : ℝ)) h, q) ∂ZeroConeRoot.uniformDyadicLaw :=
      hΦ.comp (comap_measurable (LQGMetric.restrictTo (extOpen (k : ℝ))))
    exact hmeas.stronglyMeasurable
  · have hint : ∀ h : Field, ∫ q, Ψ (LQGMetric.restrictTo (extOpen (k : ℝ)) h, q)
        ∂ZeroConeRoot.uniformDyadicLaw = ∫ q, Bf (h, q) ∂ZeroConeRoot.uniformDyadicLaw := fun h => by
      simp only [hBΨ]
    simp only [hint]
    refine (lintegral_abs_sub_integral_le (μ := μ) (Q := ZeroConeRoot.uniformDyadicLaw) hFm hBm (K := K)
      (fun h => by rw [abs_of_nonneg (hF0 h)]; exact hFK h) hBb).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [hBf] using hN

end Main

end MatedCRT
