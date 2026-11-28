import MatedCRT.FirstPass.Derived.ZeroConeJointStepsProof
import MatedCRT.FirstPass.Derived.ZeroConeQuantumCurveCovarianceProof
import MatedCRT.FirstPass.Derived.ConeAreaBumpTiltProof
import LatticeProb.Prob.DyadicExhaustion
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# Lemma A.4 of Gwynne–Miller–Sheffield at uniform roots of dyadic squares

For the circle-average embedding `h` of the `0`-quantum cone (`zeroConeFieldOf`), with LQG area measure `μ_h`, and an
independent uniform dyadic system `𝒟` (Gwynne–Miller–Sheffield, arXiv:1807.07515, §2.1; the LP model
`LatticeProb.DyadicOffset` with coordinates `(s, o¹, o²)`), Gwynne–Miller–Sheffield (arXiv:1705.11161, (A.2) and
Lemma A.4) consider the largest square `Ŝ_m` of `𝒟` containing `0` with `μ_h(Ŝ_m) ≤ m`, a point `z_m` sampled
uniformly from Lebesgue measure on `Ŝ_m`, and state that there is a random constant `C_m > 0` with
`h(C_m · + z_m) + Q log C_m` equal in law to `h`.

## Main definitions

* `ZeroConeRoot.sqMass`: the mass of a closed square, through its open neighbourhoods; jointly measurable in the
  measure and the square, equal to the mass of the square for locally finite measures (`sqMass_eq`).
* `ZeroConeRoot.rootGen`, `ZeroConeRoot.rootSample`: the generation of the largest square of the chain at the origin
  of mass at most `m`, and the point `corner + side · (u₁ + i u₂)` of that square; jointly measurable.
* `ZeroConeUniformRootLemmaA4`: Lemma A.4 of Gwynne–Miller–Sheffield with the existence of the square (A.2), stated
  for every Borel area map which is almost surely the vague limit of the area approximations and with a measurable
  constant for every prescribed sampler (a named printed input, which strengthens the printed statement in the three
  respects listed in its docstring).

## Main statements

* `ZeroConeRoot.measurable_measure_section_of_isOpen`: the mass of the sections of an open set is jointly measurable
  in the measure and the parameter.
* `ZeroConeRoot.measurable_massRadius`, `ZeroConeRoot.massRadius_map_similarity`: the mass radius
  `r_s(z) = inf {r > 0 : ν(B_r(z)) > s}` is jointly measurable, and covariant under the LQG coordinate change.
* `ZeroConeRoot.measurable_rootSample`.
* `exists_reroot_of_uniformRoot`: from the uniform-root form to the re-rooting of the field at the root, with the
  escape of the roots to infinity.
* `zeroConeLemmaA4`: Lemma A.4 for the circle-average embedding of the `0`-quantum cone (`ZeroConeLemmaA4`), from
  `ZeroConeUniformRootLemmaA4`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal Pointwise

namespace ZeroConeRoot

/-! ### Masses of open sets, balls and the mass radius -/

section Masses

/-- **The mass of the sections of an open set is jointly measurable in the measure and the parameter.** For an open
set `O ⊆ X × ℂ` (with `X` second countable), `(ν, x) ↦ ν {w | (x, w) ∈ O}` is measurable for the Giry σ-algebra:
the sections are directed unions of finite unions of basic opens of a countable product basis. -/
theorem measurable_measure_section_of_isOpen {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {O : Set (X × ℂ)} (hO : IsOpen O) :
    Measurable fun p : Measure ℂ × X => p.1 {w | (p.2, w) ∈ O} := by
  classical
  obtain ⟨bX, hbXc, -, hbX⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨bC, hbCc, -, hbC⟩ := TopologicalSpace.exists_countable_basis ℂ
  let I : Set (Set X × Set ℂ) := {q | q.1 ∈ bX ∧ q.2 ∈ bC ∧ q.1 ×ˢ q.2 ⊆ O}
  have hIc : I.Countable := by
    refine (hbXc.prod hbCc).mono ?_
    rintro q ⟨h1, h2, -⟩
    exact Set.mem_prod.2 ⟨h1, h2⟩
  have : Countable I := hIc.to_subtype
  have hsec : ∀ x : X, {w | (x, w) ∈ O} = ⋃ F : Finset I, ⋃ i ∈ F, ⋃ (_ : x ∈ i.1.1), i.1.2 := by
    intro x
    rw [← iUnion_eq_iUnion_finset fun i : I => ⋃ (_ : x ∈ i.1.1), i.1.2]
    ext w
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hw
      obtain ⟨B, hB, hxwB, hBO⟩ := (hbX.prod hbC).exists_subset_of_mem_open hw hO
      obtain ⟨U, hU, V, hV, rfl⟩ := hB
      exact ⟨⟨(U, V), hU, hV, hBO⟩, hxwB.1, hxwB.2⟩
    · rintro ⟨i, hx, hw⟩
      exact i.2.2.2 ⟨hx, hw⟩
  let β : (F : Finset I) → X → (F → Bool) := fun _ x i => decide (x ∈ i.1.1.1)
  let Ψ : (F : Finset I) → Measure ℂ × (F → Bool) → ℝ≥0∞ := fun _ q =>
    q.1 (⋃ i, ⋃ (_ : q.2 i = true), i.1.1.2)
  have hΨ : ∀ F : Finset I, Measurable (Ψ F) := by
    intro F
    refine measurable_from_prod_countable_left fun b => ?_
    show Measurable fun μ : Measure ℂ => μ (⋃ i, ⋃ (_ : b i = true), i.1.1.2)
    refine Measure.measurable_coe (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => ?_)
    exact (hbC.isOpen i.1.2.2.1).measurableSet
  have hβ : ∀ F : Finset I, Measurable (β F) := by
    intro F
    refine measurable_pi_iff.2 fun i => measurable_to_bool ?_
    have hU : MeasurableSet i.1.1.1 := (hbX.isOpen i.1.2.1).measurableSet
    convert hU using 1
    ext x
    simp [β]
  have hfun : (fun p : Measure ℂ × X => p.1 {w | (p.2, w) ∈ O}) =
      fun p => ⨆ F : Finset I, Ψ F (p.1, β F p.2) := by
    funext p
    rw [hsec p.2]
    have hmono : Monotone fun F : Finset I => ⋃ i ∈ F, ⋃ (_ : p.2 ∈ i.1.1), i.1.2 := by
      intro F G hFG w hw
      simp only [mem_iUnion] at hw ⊢
      obtain ⟨i, hi, hx, hw⟩ := hw
      exact ⟨i, hFG hi, hx, hw⟩
    rw [hmono.directed_le.measure_iUnion]
    congr 1
    funext F
    simp only [Ψ, β]
    congr 1
    ext w
    simp only [mem_iUnion, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hx, hw⟩
      exact ⟨⟨i, hi⟩, hx, hw⟩
    · rintro ⟨⟨i, hi⟩, hx, hw⟩
      exact ⟨i, hi, hx, hw⟩
  rw [hfun]
  exact Measurable.iSup fun F => (hΨ F).comp (measurable_fst.prodMk ((hβ F).comp measurable_snd))

/-- **The mass of a ball is jointly measurable in the measure, the centre and the radius.** -/
theorem measurable_measure_ball :
    Measurable fun p : Measure ℂ × (ℂ × ℝ) => p.1 (Metric.ball p.2.1 p.2.2) := by
  have hO : IsOpen {q : (ℂ × ℝ) × ℂ | dist q.2 q.1.1 < q.1.2} :=
    isOpen_lt (continuous_snd.dist (continuous_fst.comp continuous_fst)) (continuous_snd.comp continuous_fst)
  exact measurable_measure_section_of_isOpen hO

/-- **The mass radius** `r_s(z) = inf {r > 0 : ν(B_r(z)) > s}` of a measure `ν` at `z` (Gwynne–Miller–Sheffield,
arXiv:1705.11161, (A.7), `T_b(z) = inf {r > 0 : μ_h(B_r(z)) = b}`, with balls centred at `z`). The condition here is
`> s` and the value is `0` when no ball has mass larger than `s`; it agrees with (A.7) when `r ↦ ν(B_r(z))` is
continuous and strictly increasing. -/
def massRadius (ν : Measure ℂ) (s : ℝ) (z : ℂ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ ENNReal.ofReal s < ν (Metric.ball z r)}

theorem massRadius_nonneg (ν : Measure ℂ) (s : ℝ) (z : ℂ) : 0 ≤ massRadius ν s z :=
  Real.sInf_nonneg fun _ hr => hr.1.le

/-- The defining set of the mass radius is an up-set in the radius. -/
theorem mem_massRadiusSet_of_le {ν : Measure ℂ} {s : ℝ} {z : ℂ} {r r' : ℝ}
    (hr : 0 < r ∧ ENNReal.ofReal s < ν (Metric.ball z r)) (hrr' : r ≤ r') :
    0 < r' ∧ ENNReal.ofReal s < ν (Metric.ball z r') :=
  ⟨hr.1.trans_le hrr', hr.2.trans_le (measure_mono (Metric.ball_subset_ball hrr'))⟩

/-- **The mass radius is jointly measurable in the measure and the centre**: `r_s(z) < t` iff no ball has mass
larger than `s` (for `t > 0`) or some rational radius `q < t` has mass larger than `s`. -/
theorem measurable_massRadius (s : ℝ) : Measurable fun p : Measure ℂ × ℂ => massRadius p.1 s p.2 := by
  have hball : ∀ r : ℝ, Measurable fun p : Measure ℂ × ℂ => p.1 (Metric.ball p.2 r) := fun r =>
    measurable_measure_ball.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  refine measurable_of_Iio fun t => ?_
  by_cases ht : t ≤ 0
  · convert MeasurableSet.empty
    ext p
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact ht.trans (massRadius_nonneg _ _ _)
  have ht' : 0 < t := lt_of_not_ge ht
  have hset : (fun p : Measure ℂ × ℂ => massRadius p.1 s p.2) ⁻¹' Iio t =
      (⋂ q : ℚ, {p : Measure ℂ × ℂ | 0 < (q : ℝ) → p.1 (Metric.ball p.2 q) ≤ ENNReal.ofReal s}) ∪
        ⋃ q : ℚ, {p : Measure ℂ × ℂ | 0 < (q : ℝ) ∧ (q : ℝ) < t ∧
          ENNReal.ofReal s < p.1 (Metric.ball p.2 q)} := by
    ext p
    simp only [mem_preimage, mem_Iio, mem_union, mem_iInter, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hp
      by_cases hne : {r : ℝ | 0 < r ∧ ENNReal.ofReal s < p.1 (Metric.ball p.2 r)}.Nonempty
      · right
        obtain ⟨r, hr, hrt⟩ := exists_lt_of_csInf_lt hne hp
        obtain ⟨q, hrq, hqt⟩ := exists_rat_btwn hrt
        have hq := mem_massRadiusSet_of_le hr hrq.le
        exact ⟨q, hq.1, hqt, hq.2⟩
      · left
        intro q hq
        refine le_of_not_gt fun hlt => hne ⟨q, hq, hlt⟩
    · rintro (h | ⟨q, hq0, hqt, hq⟩)
      · have hemp : {r : ℝ | 0 < r ∧ ENNReal.ofReal s < p.1 (Metric.ball p.2 r)} = ∅ := by
          ext r
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
          intro hr
          obtain ⟨q, hrq, -⟩ := exists_rat_btwn (show r < r + 1 by linarith)
          exact (measure_mono (Metric.ball_subset_ball hrq.le)).trans (h q (hr.trans hrq))
        show sInf _ < t
        rw [hemp, Real.sInf_empty]
        exact ht'
      · have hmem : (q : ℝ) ∈ {r : ℝ | 0 < r ∧ ENNReal.ofReal s < p.1 (Metric.ball p.2 r)} := ⟨hq0, hq⟩
        have hbdd : BddBelow {r : ℝ | 0 < r ∧ ENNReal.ofReal s < p.1 (Metric.ball p.2 r)} :=
          ⟨0, fun _ hr => hr.1.le⟩
        exact (csInf_le hbdd hmem).trans_lt hqt
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iInter fun q => ?_) (MeasurableSet.iUnion fun q => ?_)
  · by_cases hq : 0 < (q : ℝ)
    · simp only [hq, true_implies]
      exact measurableSet_le (hball q) measurable_const
    · convert MeasurableSet.univ using 1
      ext p
      simp [hq]
  · by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < t
    · simp only [hq.1, hq.2, true_and]
      exact measurableSet_lt measurable_const (hball q)
    · convert MeasurableSet.empty using 1
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hq ⟨h.1, h.2.1⟩

/-- The preimage of the ball `B_r(0)` under `w ↦ C⁻¹ (w − z)` is the ball `B_{C r}(z)`. -/
theorem preimage_similarity_ball {C : ℝ} (hC : 0 < C) (z : ℂ) (r : ℝ) :
    (fun w : ℂ => ((C⁻¹ : ℝ) : ℂ) * (w - z)) ⁻¹' Metric.ball 0 r = Metric.ball z (C * r) := by
  ext w
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_pos hC]
  rw [inv_mul_lt_iff₀ hC]

/-- **Covariance of the mass radius under the LQG coordinate change**: for `ν' = ν ∘ ψ`, `ψ(w) = C w + z`, the mass
radii of `ν'` at `0` are those of `ν` at `z` divided by `C`. -/
theorem massRadius_map_similarity (ν : Measure ℂ) (s : ℝ) {C : ℝ} (hC : 0 < C) (z : ℂ) :
    massRadius (ν.map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)) s 0 = massRadius ν s z / C := by
  have hmeas : Measurable fun w : ℂ => ((C⁻¹ : ℝ) : ℂ) * (w - z) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).measurable
  have hball : ∀ r, (ν.map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)) (Metric.ball 0 r) =
      ν (Metric.ball z (C * r)) := by
    intro r
    rw [Measure.map_apply hmeas measurableSet_ball, preimage_similarity_ball hC]
  have hset : {r : ℝ | 0 < r ∧ ENNReal.ofReal s <
        (ν.map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z)) (Metric.ball 0 r)} =
      C⁻¹ • {r : ℝ | 0 < r ∧ ENNReal.ofReal s < ν (Metric.ball z r)} := by
    ext r
    rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hC.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq, hball]
    constructor
    · rintro ⟨hr, h⟩
      exact ⟨mul_pos hC hr, h⟩
    · rintro ⟨hr, h⟩
      exact ⟨pos_of_mul_pos_right hr hC.le, h⟩
  unfold massRadius
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 hC.le), smul_eq_mul, div_eq_inv_mul]

end Masses

/-! ### Masses of closed squares -/

section Squares

open LatticeProb.DyadicOffset (cornerSquare)

/-- The open neighbourhood of size `δ`, in the maximum of the coordinate distances, of the closed square with lower
left corner `a + i b` and side `ℓ`. -/
def sqNbhd (a b ℓ δ : ℝ) : Set ℂ :=
  {w | a - δ < w.re ∧ w.re < a + ℓ + δ ∧ b - δ < w.im ∧ w.im < b + ℓ + δ}

/-- The mass of the closed square with lower left corner `a + i b` and side `ℓ`, computed through its open
neighbourhoods of size `1/(n+1)`; it is the mass of the square for locally finite measures (`sqMass_eq`). -/
def sqMass (ν : Measure ℂ) (a b ℓ : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ν (sqNbhd a b ℓ (1 / ((n : ℝ) + 1)))

theorem isOpen_sqNbhd_graph (δ : ℝ) :
    IsOpen {q : (ℝ × ℝ × ℝ) × ℂ | q.2 ∈ sqNbhd q.1.1 q.1.2.1 q.1.2.2 δ} := by
  have hre : Continuous fun q : (ℝ × ℝ × ℝ) × ℂ => q.2.re := Complex.continuous_re.comp continuous_snd
  have him : Continuous fun q : (ℝ × ℝ × ℝ) × ℂ => q.2.im := Complex.continuous_im.comp continuous_snd
  have ha : Continuous fun q : (ℝ × ℝ × ℝ) × ℂ => q.1.1 := continuous_fst.fst
  have hb : Continuous fun q : (ℝ × ℝ × ℝ) × ℂ => q.1.2.1 := continuous_fst.snd.fst
  have hl : Continuous fun q : (ℝ × ℝ × ℝ) × ℂ => q.1.2.2 := continuous_fst.snd.snd
  exact (isOpen_lt (ha.sub continuous_const) hre).inter
    ((isOpen_lt hre ((ha.add hl).add continuous_const)).inter
      ((isOpen_lt (hb.sub continuous_const) him).inter (isOpen_lt him ((hb.add hl).add continuous_const))))

theorem isOpen_sqNbhd (a b ℓ δ : ℝ) : IsOpen (sqNbhd a b ℓ δ) :=
  (isOpen_sqNbhd_graph δ).preimage (continuous_const.prodMk continuous_id :
    Continuous fun w : ℂ => (((a, b, ℓ) : ℝ × ℝ × ℝ), w))

/-- **The mass of a closed square is jointly measurable in the measure and the square.** -/
theorem measurable_sqMass :
    Measurable fun p : Measure ℂ × (ℝ × ℝ × ℝ) => sqMass p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  Measurable.iInf fun n => measurable_measure_section_of_isOpen (isOpen_sqNbhd_graph (1 / ((n : ℝ) + 1)))

/-- **For a locally finite measure, `sqMass` is the mass of the closed square**: the square is the decreasing
intersection of its open neighbourhoods, which have finite mass. -/
theorem sqMass_eq {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) (a b ℓ : ℝ) :
    sqMass ν a b ℓ = ν (cornerSquare a b ℓ) := by
  have key : ∀ x y : ℝ, (∀ n : ℕ, x < y + 1 / ((n : ℝ) + 1)) → x ≤ y := fun x y h =>
    le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [h n]
  have hinter : cornerSquare a b ℓ = ⋂ n : ℕ, sqNbhd a b ℓ (1 / ((n : ℝ) + 1)) := by
    ext w
    simp only [LatticeProb.DyadicOffset.mem_cornerSquare, mem_iInter, sqNbhd, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro h
      exact ⟨key _ _ fun n => by linarith [(h n).1], key _ _ fun n => by linarith [(h n).2.1],
        key _ _ fun n => by linarith [(h n).2.2.1], key _ _ fun n => by linarith [(h n).2.2.2]⟩
  have hanti : Antitone fun n : ℕ => sqNbhd a b ℓ (1 / ((n : ℝ) + 1)) := by
    intro n n' hnn' w hw
    have hle : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
    obtain ⟨h1, h2, h3, h4⟩ := hw
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsub : sqNbhd a b ℓ (1 / (((0 : ℕ) : ℝ) + 1)) ⊆ cornerSquare (a - 1) (b - 1) (ℓ + 2) := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    norm_num at h1 h2 h3 h4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hfin : ∃ n : ℕ, ν (sqNbhd a b ℓ (1 / ((n : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, ((measure_mono hsub).trans_lt
      (hν _ (LatticeProb.DyadicOffset.isCompact_cornerSquare _ _ _))).ne⟩
  rw [hinter, hanti.measure_iInter (fun n => (isOpen_sqNbhd _ _ _ _).measurableSet.nullMeasurableSet) hfin]
  rfl

end Squares

/-! ### The uniform dyadic system and the uniform root -/

section Root

open LatticeProb.DyadicOffset (gridFloor latticeFloor unifIco offsetLaw)

/-- The coordinates `(s, o¹, o²)` of a dyadic system (`LatticeProb.DyadicOffset`). -/
abbrev DyCoord : Type := ℝ × (ℕ → ℝ) × (ℕ → ℝ)

/-- **The law of the uniform dyadic system** (Gwynne–Miller–Sheffield, arXiv:1807.07515, §2.1): `s` uniform on
`[0, 1)` and the two offset sequences independent with law `offsetLaw` (a uniform base point and independent fair
parent choices). -/
abbrev uniformDyadicLaw : Measure DyCoord :=
  (unifIco 1).prod (offsetLaw.prod offsetLaw)

/-- The uniform law on the unit square `[0, 1)²`. -/
abbrev unifSquareLaw : Measure (ℝ × ℝ) :=
  (unifIco 1).prod (unifIco 1)

/-- (Copied from `LatticeProb.Prob.CellConfigSquareMeasurable`.) -/
theorem measurable_latticeFloor {β : Type*} [MeasurableSpace β] {c p x : β → ℝ}
    (hc : Measurable c) (hp : Measurable p) (hx : Measurable x) :
    Measurable fun b => latticeFloor (c b) (p b) (x b) := by
  unfold latticeFloor
  exact hc.add (((measurable_of_countable (Int.cast : ℤ → ℝ)).comp
    ((hx.sub hc).div hp).floor).mul hp)

/-- (Copied from `LatticeProb.Prob.CellConfigSquareMeasurable`.) The left end of the grid interval of generation `j`
containing `x` is measurable in the scale, the offsets and `x`. -/
theorem measurable_gridFloor {β : Type*} [MeasurableSpace β] (j : ℤ) {s : β → ℝ}
    {o : β → ℕ → ℝ} {x : β → ℝ} (hs : Measurable s) (ho : Measurable o) (hx : Measurable x) :
    Measurable fun b => gridFloor (s b) (o b) j (x b) := by
  unfold gridFloor
  exact measurable_latticeFloor
    ((measurable_const.pow hs).mul ((measurable_pi_apply j.toNat).comp ho)).neg
    (measurable_const.pow (hs.add_const _)) hx

/-- The mass of the square `squareAt q j 0` of generation `j` of the chain at the origin (`sqMass`). -/
def chainMass (ν : Measure ℂ) (q : DyCoord) (j : ℤ) : ℝ≥0∞ :=
  sqMass ν (gridFloor q.1 q.2.1 j 0) (gridFloor q.1 q.2.2 j 0) ((2 : ℝ) ^ (q.1 + (j : ℝ)))

theorem measurable_chainMass (j : ℤ) :
    Measurable fun p : Measure ℂ × DyCoord => chainMass p.1 p.2 j := by
  have hs : Measurable fun p : Measure ℂ × DyCoord => p.2.1 := measurable_snd.fst
  have ho₁ : Measurable fun p : Measure ℂ × DyCoord => p.2.2.1 := measurable_snd.snd.fst
  have ho₂ : Measurable fun p : Measure ℂ × DyCoord => p.2.2.2 := measurable_snd.snd.snd
  exact measurable_sqMass.comp (measurable_fst.prodMk ((measurable_gridFloor j hs ho₁ measurable_const).prodMk
    ((measurable_gridFloor j hs ho₂ measurable_const).prodMk (measurable_const.pow (hs.add_const _)))))

/-- **The generation of the root square**: the largest generation `j` of the chain of squares at the origin whose
square has mass at most `m` (value `0` if there is no largest one). -/
def rootGen (ν : Measure ℂ) (q : DyCoord) (m : ℝ≥0∞) : ℤ :=
  sSup {j : ℤ | chainMass ν q j ≤ m}

/-- The supremum over `ℤ` of a set which is empty or not bounded above is `0`. -/
theorem int_sSup_eq_zero {S : Set ℤ} (hS : ¬(S.Nonempty ∧ BddAbove S)) : sSup S = 0 := by
  by_cases hne : S.Nonempty
  · exact Int.csSup_of_not_bddAbove fun hb => hS ⟨hne, hb⟩
  · rw [not_nonempty_iff_eq_empty.1 hne, Int.csSup_empty]

theorem measurable_rootGen (m : ℝ≥0∞) : Measurable fun p : Measure ℂ × DyCoord => rootGen p.1 p.2 m := by
  set A : ℤ → Set (Measure ℂ × DyCoord) := fun j => {p | chainMass p.1 p.2 j ≤ m} with hA
  have hAm : ∀ j, MeasurableSet (A j) := fun j => measurableSet_le (measurable_chainMass j) measurable_const
  have himp : ∀ (j : ℤ) (P : Prop), MeasurableSet {p : Measure ℂ × DyCoord | p ∈ A j → P} := by
    intro j P
    by_cases hP : P
    · convert MeasurableSet.univ using 1
      ext p
      simp [hP]
    · convert (hAm j).compl using 1
      ext p
      simp [hP]
  have hgood : MeasurableSet {p : Measure ℂ × DyCoord |
      (∃ j, p ∈ A j) ∧ ∃ N : ℤ, ∀ j, p ∈ A j → j ≤ N} := by
    have : {p : Measure ℂ × DyCoord | (∃ j, p ∈ A j) ∧ ∃ N : ℤ, ∀ j, p ∈ A j → j ≤ N} =
        (⋃ j, A j) ∩ ⋃ N : ℤ, ⋂ j, {p | p ∈ A j → j ≤ N} := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    rw [this]
    exact (MeasurableSet.iUnion hAm).inter
      (MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j => himp j _)
  refine measurable_to_countable' fun i => ?_
  have hpre : (fun p : Measure ℂ × DyCoord => rootGen p.1 p.2 m) ⁻¹' {i} =
      (A i ∩ ⋂ j, {p | p ∈ A j → j ≤ i}) ∪
        ({p | (∃ j, p ∈ A j) ∧ ∃ N : ℤ, ∀ j, p ∈ A j → j ≤ N}ᶜ ∩ {_p | i = 0}) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter, mem_ofPred_eq,
      mem_compl_iff]
    constructor
    · intro hp
      by_cases hg : (∃ j, p ∈ A j) ∧ ∃ N : ℤ, ∀ j, p ∈ A j → j ≤ N
      · left
        obtain ⟨⟨j₀, hj₀⟩, N, hN⟩ := hg
        have hne : ({j | chainMass p.1 p.2 j ≤ m} : Set ℤ).Nonempty := ⟨j₀, hj₀⟩
        have hbdd : BddAbove ({j | chainMass p.1 p.2 j ≤ m} : Set ℤ) := ⟨N, fun j hj => hN j hj⟩
        have hmem := Int.csSup_mem hne hbdd
        rw [← hp]
        exact ⟨hmem, fun j hj => le_csSup hbdd hj⟩
      · right
        refine ⟨hg, ?_⟩
        rw [← hp]
        refine int_sSup_eq_zero fun h => hg ⟨?_, ?_⟩
        · obtain ⟨j, hj⟩ := h.1
          exact ⟨j, hj⟩
        · obtain ⟨N, hN⟩ := h.2
          exact ⟨N, fun j hj => hN hj⟩
    · rintro (⟨hi, hmax⟩ | ⟨hg, rfl⟩)
      · show sSup {j : ℤ | chainMass p.1 p.2 j ≤ m} = i
        exact le_antisymm (csSup_le ⟨i, hi⟩ fun j hj => hmax j hj) (le_csSup ⟨i, fun j hj => hmax j hj⟩ hi)
      · show sSup {j : ℤ | chainMass p.1 p.2 j ≤ m} = 0
        refine int_sSup_eq_zero fun h => hg ⟨?_, ?_⟩
        · obtain ⟨j, hj⟩ := h.1
          exact ⟨j, hj⟩
        · obtain ⟨N, hN⟩ := h.2
          exact ⟨N, fun j hj => hN hj⟩
  rw [hpre]
  exact ((hAm i).inter (MeasurableSet.iInter fun j => himp j _)).union
    (hgood.compl.inter (MeasurableSet.const _))

/-- The point `corner + side · (u₁ + i u₂)` of the square of generation `j` of the chain at the origin. -/
def chainPoint (q : DyCoord) (j : ℤ) (u : ℝ × ℝ) : ℂ :=
  ((gridFloor q.1 q.2.1 j 0 + (2 : ℝ) ^ (q.1 + (j : ℝ)) * u.1 : ℝ) : ℂ) +
    ((gridFloor q.1 q.2.2 j 0 + (2 : ℝ) ^ (q.1 + (j : ℝ)) * u.2 : ℝ) : ℂ) * Complex.I

theorem measurable_chainPoint (j : ℤ) : Measurable fun x : DyCoord × (ℝ × ℝ) => chainPoint x.1 j x.2 := by
  have hs : Measurable fun x : DyCoord × (ℝ × ℝ) => x.1.1 := measurable_fst.fst
  have ho₁ : Measurable fun x : DyCoord × (ℝ × ℝ) => x.1.2.1 := measurable_fst.snd.fst
  have ho₂ : Measurable fun x : DyCoord × (ℝ × ℝ) => x.1.2.2 := measurable_fst.snd.snd
  have hside : Measurable fun x : DyCoord × (ℝ × ℝ) => (2 : ℝ) ^ (x.1.1 + (j : ℝ)) :=
    measurable_const.pow (hs.add_const _)
  have h₁ : Measurable fun x : DyCoord × (ℝ × ℝ) =>
      gridFloor x.1.1 x.1.2.1 j 0 + (2 : ℝ) ^ (x.1.1 + (j : ℝ)) * x.2.1 :=
    (measurable_gridFloor j hs ho₁ measurable_const).add (hside.mul measurable_snd.fst)
  have h₂ : Measurable fun x : DyCoord × (ℝ × ℝ) =>
      gridFloor x.1.1 x.1.2.2 j 0 + (2 : ℝ) ^ (x.1.1 + (j : ℝ)) * x.2.2 :=
    (measurable_gridFloor j hs ho₂ measurable_const).add (hside.mul measurable_snd.snd)
  exact (Complex.measurable_ofReal.comp h₁).add ((Complex.measurable_ofReal.comp h₂).mul_const _)

/-- **The uniform root sampler**: the point `corner + side · (u₁ + i u₂)` of the root square, the square of
generation `rootGen ν q m` of the chain at the origin. For `u` uniform on `[0, 1)²` it is uniform on that square. -/
def rootSample (ν : Measure ℂ) (q : DyCoord) (m : ℝ≥0∞) (u : ℝ × ℝ) : ℂ :=
  chainPoint q (rootGen ν q m) u

theorem measurable_rootSample (m : ℝ≥0∞) :
    Measurable fun x : Measure ℂ × DyCoord × (ℝ × ℝ) => rootSample x.1 x.2.1 m x.2.2 := by
  have hG : Measurable fun r : ℤ × (DyCoord × (ℝ × ℝ)) => chainPoint r.2.1 r.1 r.2.2 := by
    refine measurable_from_prod_countable_right fun j => ?_
    exact measurable_chainPoint j
  have hgen := (measurable_rootGen m).comp
    (measurable_fst.prodMk measurable_snd.fst : Measurable fun x : Measure ℂ × DyCoord × (ℝ × ℝ) => (x.1, x.2.1))
  have h := hG.comp (hgen.prodMk measurable_snd)
  simp only [Function.comp_def] at h
  unfold rootSample
  exact h

theorem measurable_rootSample_comp {β : Type*} [MeasurableSpace β] {N : β → Measure ℂ} {q : β → DyCoord}
    {u : β → ℝ × ℝ} (hN : Measurable N) (hq : Measurable q) (hu : Measurable u) (m : ℝ≥0∞) :
    Measurable fun x => rootSample (N x) (q x) m (u x) := by
  have h := (measurable_rootSample m).comp (hN.prodMk (hq.prodMk hu))
  simp only [Function.comp_def] at h
  exact h

end Root

/-! ### The root square and the escape of the uniform root -/

section Escape

open LatticeProb.DyadicOffset (gridFloor unifIco offsetLaw squareAt IsOffGrid eq_squareAt_of_mem
  squareAt_mem_dyadicSquares mem_squareAt dyadicSquares cornerSquare isCompact_cornerSquare)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

instance isProbabilityMeasure_unifIco_one : IsProbabilityMeasure (unifIco 1) :=
  LatticeProb.DyadicOffset.isProbabilityMeasure_unifIco one_pos

/-- A closed square contained in another closed square has a side at most the side of the other. -/
theorem side_le_of_cornerSquare_subset {a b ℓ a' b' ℓ' : ℝ} (hℓ : 0 ≤ ℓ)
    (h : cornerSquare a b ℓ ⊆ cornerSquare a' b' ℓ') : ℓ ≤ ℓ' := by
  have h₁ : (⟨a, b⟩ : ℂ) ∈ cornerSquare a b ℓ :=
    ⟨le_rfl, le_add_of_nonneg_right hℓ, le_rfl, le_add_of_nonneg_right hℓ⟩
  have h₂ : (⟨a + ℓ, b⟩ : ℂ) ∈ cornerSquare a b ℓ :=
    ⟨le_add_of_nonneg_right hℓ, le_rfl, le_rfl, le_add_of_nonneg_right hℓ⟩
  have e₁ : a' ≤ a := (h h₁).1
  have e₂ : a + ℓ ≤ a' + ℓ' := (h h₂).2.1
  linarith

/-- **The root square at an off-grid origin.** If the capped square `Ŝ_m` (the largest square of the dyadic
system containing `0` of mass at most `m`) of a locally finite measure exists and the origin lies on no grid line,
the generations of the chain at the origin of mass at most `m` have the largest element `rootGen ν q m`, and
`Ŝ_m` is the square of that generation. -/
theorem rootGen_spec {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) {q : DyCoord}
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0) {m : ℝ≥0∞} {S : Set ℂ}
    (hS : IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 S) :
    IsGreatest {j : ℤ | chainMass ν q j ≤ m} (rootGen ν q m) ∧
      cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 = squareAt q.1 q.2.1 q.2.2 (rootGen ν q m) 0 := by
  have hcm : ∀ j : ℤ, chainMass ν q j = ν (squareAt q.1 q.2.1 q.2.2 j 0) := by
    intro j
    rw [chainMass, sqMass_eq hν, squareAt, Complex.zero_re, Complex.zero_im]
  obtain ⟨j₀, hj₀⟩ := eq_squareAt_of_mem hw hS.mem_family hS.mem
  have hgr : IsGreatest {j : ℤ | chainMass ν q j ≤ m} j₀ := by
    refine ⟨?_, fun j hj => ?_⟩
    · show chainMass ν q j₀ ≤ m
      rw [hcm, ← hj₀]
      exact hS.mass_le
    · have hj' : ν (squareAt q.1 q.2.1 q.2.2 j 0) ≤ m := by
        rw [← hcm]
        exact hj
      have hsub := hS.subset (squareAt_mem_dyadicSquares j 0) (mem_squareAt j 0) hj'
      rw [hj₀] at hsub
      have hside := side_le_of_cornerSquare_subset (by positivity) hsub
      have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 hside
      have hjr : (j : ℝ) ≤ j₀ := by linarith
      exact_mod_cast hjr
  have hroot : rootGen ν q m = j₀ := hgr.csSup_eq
  refine ⟨by rw [hroot]; exact hgr, ?_⟩
  rw [hroot, hS.cappedSquare_eq, hj₀]

/-- **A uniform point of a square of side `ℓ` is rarely close to the origin**: the point
`(x + ℓ u₁) + i (y + ℓ u₂)`, `u` uniform on `[0, 1)²`, lies in the closed disc of radius `R` with probability at
most `2R/ℓ` (its real part has to lie in an interval of length `2R`). -/
theorem unifSquareLaw_norm_le (x y ℓ R : ℝ) (hℓ : 0 < ℓ) :
    unifSquareLaw {u : ℝ × ℝ | ‖(((x + ℓ * u.1 : ℝ) : ℂ) + ((y + ℓ * u.2 : ℝ) : ℂ) * Complex.I)‖ ≤ R} ≤
      ENNReal.ofReal (2 * R / ℓ) := by
  have hsub : {u : ℝ × ℝ | ‖(((x + ℓ * u.1 : ℝ) : ℂ) + ((y + ℓ * u.2 : ℝ) : ℂ) * Complex.I)‖ ≤ R} ⊆
      Icc ((-R - x) / ℓ) ((R - x) / ℓ) ×ˢ (univ : Set ℝ) := by
    intro u hu
    have hre := (Complex.abs_re_le_norm
      (((x + ℓ * u.1 : ℝ) : ℂ) + ((y + ℓ * u.2 : ℝ) : ℂ) * Complex.I)).trans hu
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    obtain ⟨h₁, h₂⟩ := abs_le.1 hre
    refine Set.mem_prod.2 ⟨⟨?_, ?_⟩, mem_univ _⟩
    · rw [div_le_iff₀ hℓ]
      linarith
    · rw [le_div_iff₀ hℓ]
      linarith
  calc unifSquareLaw {u : ℝ × ℝ | ‖(((x + ℓ * u.1 : ℝ) : ℂ) + ((y + ℓ * u.2 : ℝ) : ℂ) * Complex.I)‖ ≤ R}
      ≤ unifSquareLaw (Icc ((-R - x) / ℓ) ((R - x) / ℓ) ×ˢ (univ : Set ℝ)) := measure_mono hsub
    _ = unifIco 1 (Icc ((-R - x) / ℓ) ((R - x) / ℓ)) := by
      rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ volume (Icc ((-R - x) / ℓ) ((R - x) / ℓ)) := by
      simp only [unifIco, ENNReal.ofReal_one, inv_one, one_smul]
      exact Measure.restrict_apply_le _ _
    _ = ENNReal.ofReal (2 * R / ℓ) := by
      rw [Real.volume_Icc, div_sub_div_same]
      congr 1
      ring

/-- The probability that the uniform root `rootSample ν q m u`, `u` uniform on `[0, 1)²`, lies in the closed disc
of radius `R`. -/
def nearMass (ν : Measure ℂ) (q : DyCoord) (m : ℝ≥0∞) (R : ℝ) : ℝ≥0∞ :=
  unifSquareLaw {u : ℝ × ℝ | ‖rootSample ν q m u‖ ≤ R}

theorem nearMass_le (ν : Measure ℂ) (q : DyCoord) (m : ℝ≥0∞) (R : ℝ) :
    nearMass ν q m R ≤ ENNReal.ofReal (2 * R / (2 : ℝ) ^ (q.1 + ((rootGen ν q m : ℤ) : ℝ))) := by
  unfold nearMass rootSample chainPoint
  exact unifSquareLaw_norm_le _ _ _ R (by positivity)

/-- **Escape of the uniform root**: if the measure is locally finite, the origin lies on no grid line and the
capped squares `Ŝ_m` exist for all masses, the generation of `Ŝ_{m+1}` tends to infinity (every fixed square of the
chain has finite mass), and the probability that the uniform root of `Ŝ_{m+1}` lies in a fixed disc tends to `0`. -/
theorem tendsto_nearMass {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) {q : DyCoord}
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hcap : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∃ S, IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 S)
    (R : ℝ) :
    Tendsto (fun m : ℕ => nearMass ν q ((m : ℝ≥0∞) + 1) R) atTop (𝓝 0) := by
  have hm0 : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) ≠ 0 := fun m => (zero_lt_one.trans_le le_add_self).ne'
  have hmtop : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) ≠ ∞ := fun m =>
    ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩
  have hj : Tendsto (fun m : ℕ => rootGen ν q ((m : ℝ≥0∞) + 1)) atTop atTop := by
    refine tendsto_atTop.2 fun J => ?_
    have hJ : chainMass ν q J ≠ ⊤ := by
      rw [chainMass, sqMass_eq hν]
      exact (hν _ (isCompact_cornerSquare _ _ _)).ne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hJ
    refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
    obtain ⟨S, hS⟩ := hcap _ (hm0 m) (hmtop m)
    refine (rootGen_spec hν hw hS).1.2 ?_
    show chainMass ν q J ≤ (m : ℝ≥0∞) + 1
    have hnm : (n : ℝ≥0∞) ≤ m := by exact_mod_cast hm
    exact hn.le.trans (hnm.trans le_self_add)
  have hside : Tendsto (fun m : ℕ => (2 : ℝ) ^ (q.1 + ((rootGen ν q ((m : ℝ≥0∞) + 1) : ℤ) : ℝ)))
      atTop atTop := by
    have hl : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have h1 : Tendsto (fun m : ℕ => q.1 + ((rootGen ν q ((m : ℝ≥0∞) + 1) : ℤ) : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ q.1 (tendsto_intCast_atTop_atTop.comp hj)
    have h2 := Real.tendsto_exp_atTop.comp (h1.const_mul_atTop hl)
    refine h2.congr fun m => ?_
    exact (Real.rpow_def_of_pos two_pos _).symm
  have hreal : Tendsto (fun m : ℕ => 2 * R / (2 : ℝ) ^ (q.1 + ((rootGen ν q ((m : ℝ≥0∞) + 1) : ℤ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hside
  have hup := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
    fun m => nearMass_le ν q _ R

/-- Almost every point of a product measure has first coordinate in an almost sure set of the first factor. -/
theorem ae_prod_fst_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ z ∂μ.prod ν, p z.1 :=
  ae_iff.mpr (measure_mono_null (t := {x | ¬p x} ×ˢ univ) (fun _ hz => ⟨hz, trivial⟩)
    (by rw [Measure.prod_prod, ae_iff.mp h, zero_mul]))

/-- Almost every point of a product measure has second coordinate in an almost sure set of the second factor. -/
theorem ae_prod_snd_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {p : β → Prop} (h : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ z ∂μ.prod ν, p z.2 :=
  ae_iff.mpr (measure_mono_null (t := univ ×ˢ {y | ¬p y}) (fun _ hz => ⟨trivial, hz⟩)
    (by rw [Measure.prod_prod, ae_iff.mp h, mul_zero]))

end Escape

/-! ### A Borel area map of the zero-cone field -/

section AreaMap

open Classical in
/-- **The `γ`-LQG area measure as a Borel function of the field**: the vague limit `lqgArea γ h` of the dyadic
area approximations when they carry the countable certificate `AreaCertUniv` (vague convergence on `ℂ` with
eventual finiteness on compacts), and `0` otherwise. -/
def fieldArea (γ : ℝ) (h : Field) : Measure ℂ :=
  if AreaCertUniv (MoTPort.areaApproxC γ h) then CellScaling.lqgArea γ h else 0

theorem measurable_fieldArea (γ : ℝ) : Measurable (fieldArea γ) := by
  classical
  set S := {h : Field | AreaCertUniv (MoTPort.areaApproxC γ h)} with hSdef
  have hS : MeasurableSet S := measurableSet_areaCertUniv γ
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have hlim : ∀ y : S, ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ y.1) μ := by
      intro y
      have hy : AreaCertUniv (MoTPort.areaApproxC γ y.1) := y.2
      obtain ⟨⟨μ, hμ⟩, -⟩ := areaGood_univ_of_areaCertUniv hy
      exact ⟨μ, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.2 hμ⟩
    have hinc : Measurable fun y : S => (⟨y.1, hlim y⟩ :
        {h : LQGMetric.DistC | ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ}) :=
      measurable_subtype_coe.subtype_mk
    convert (LatticeProb.LQG.measurable_lqgArea_subtype γ).comp hinc using 1
    funext y
    have hy : AreaCertUniv (MoTPort.areaApproxC γ y.1) := y.2
    simp only [Set.domRestrict_apply, Function.comp_apply, fieldArea]
    exact ite_eq_left hy
  · convert (measurable_const : Measurable fun _ : (Sᶜ : Set Field) => (0 : Measure ℂ)) using 1
    funext y
    have hy : ¬ AreaCertUniv (MoTPort.areaApproxC γ y.1) := y.2
    simp only [Set.domRestrict_apply, fieldArea]
    exact ite_eq_right hy

/-- **The circle-average embedding of the `0`-quantum cone is almost everywhere measurable** (the measurable cone
process of the radial Brownian motions, `MoTPort.ConeMeas2.aemeasurable_coneField`). -/
theorem aemeasurable_zeroConeFieldOf {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} (γ : ℝ)
    {X₀' : Ω' → Field} {b b' : ℝ≥0 → Ω' → ℝ} (hX : LQGMetric.IsWholePlaneGFF X₀' P')
    (hb : IsBrownianReal b P') (hb' : IsBrownianReal b' P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P') :
    AEMeasurable (zeroConeFieldOf γ X₀' b b') P' := by
  have : IsProbabilityMeasure P' := hX.gaussian.isProbabilityMeasure
  have hA := LQGCone.isConeProcess_motConeRadial (γ := γ) (α := 0) hb hb' hbb'
  have hm := MoTPort.ConeMeas2.aemeasurable_coneField hX hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  show _ = CellScaling.coneField (X₀' ω) (CellScaling.coneRadial γ 0 (fun t => b t ω) (fun t => b' t ω))
  exact (LQGCone.coneField_eq_motConeField γ 0 (X₀' ω) (fun t => b t ω) (fun t => b' t ω)).symm

/-- **`fieldArea` is almost surely the area measure of the `0`-quantum cone**: for the circle-average embedding of
the `0`-quantum cone, almost surely the area approximations converge vaguely on `ℂ` and are eventually finite on
compacts (`ae_areaGood_coneField`), so they carry the certificate `AreaCertUniv` and `fieldArea γ h` is their vague
limit. -/
theorem ae_isVagueLimitC_fieldArea {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {X₀' : Ω' → Field} {b b' : ℝ≥0 → Ω' → ℝ} [IsProbabilityMeasure P']
    (hX : LQGMetric.IsWholePlaneGFF X₀' P') (hb : IsBrownianReal b P') (hb' : IsBrownianReal b' P')
    (hXbb : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P') :
    ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (fieldArea γ h) := by
  have hQc : 0 < QuantumZipper.Qc γ := by
    unfold QuantumZipper.Qc
    have := hγ.1
    positivity
  have hXA := MesoModel.FrozenIdentities.indepFun_motConeRadial_of_indep γ 0 hb hb' hXbb
  have hgood := ae_areaGood_coneField hγ.1 hγ.2 hQc hX hb hb' hbb' hXA
  have hG : MeasurableSet {h : Field | AreaCertUniv (MoTPort.areaApproxC γ h)} :=
    measurableSet_areaCertUniv γ
  have hmem : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), AreaCertUniv (MoTPort.areaApproxC γ h) := by
    refine (ae_map_iff (aemeasurable_zeroConeFieldOf γ hX hb hb' hbb') hG).2 ?_
    filter_upwards [hgood] with ω hω
    exact areaCertUniv_of_areaGood hω.2
  filter_upwards [hmem] with h hh
  have hex : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ := by
    obtain ⟨⟨μ, hμ⟩, -⟩ := areaGood_univ_of_areaCertUniv hh
    exact ⟨μ, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.2 hμ⟩
  have hv := CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex
  unfold fieldArea
  rw [ite_eq_left hh]
  exact hv

end AreaMap

/-! ### The uniform roots and their escape on the good pairs -/

section Assembly

open LatticeProb.DyadicOffset (unifIco dyadicSquares cornerSquare gridFloor squareAt IsOffGrid
  ae_isCompatible_isOffGrid_system)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- **The good pairs**: for almost every pair `(h, q)` of a field and an independent uniform dyadic system, the area
measure `M h` is finite on compacts, the origin lies on no grid line of `q`, and the capped squares `Ŝ_m` of (A.2)
exist for all masses `m ∈ (0, ∞)`. -/
theorem ae_goodPair {μ : Measure Field} [SFinite μ] {M : Field → Measure ℂ}
    (hloc : ∀ᵐ h ∂μ, ∀ K : Set ℂ, IsCompact K → M h K < ⊤)
    (hA2 : ∀ᵐ p ∂μ.prod uniformDyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S) :
    ∀ᵐ p ∂μ.prod uniformDyadicLaw, (∀ K : Set ℂ, IsCompact K → M p.1 K < ⊤) ∧
      IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 ∧
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
        ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S := by
  have h1 : ∀ᵐ p ∂μ.prod uniformDyadicLaw, ∀ K : Set ℂ, IsCompact K → M p.1 K < ⊤ :=
    ae_prod_fst_of_ae hloc
  have h2 : ∀ᵐ p ∂μ.prod uniformDyadicLaw, IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 :=
    ae_prod_snd_of_ae ((ae_isCompatible_isOffGrid_system 0).mono fun _ hq => hq.2.2)
  filter_upwards [h1, h2, hA2] with p hp1 hp2 hp3
  exact ⟨hp1, hp2, hp3⟩

/-- **The uniform root is the affine parametrization of the capped square**: on the good pairs, the square of
generation `rootGen` of the chain at the origin is the capped square `Ŝ_m = [a, a + ℓ] × [c, c + ℓ]`, and the root
sampler is `u ↦ (a + ℓ u₁) + i (c + ℓ u₂)`. -/
theorem ae_rootSample_affine {μ : Measure Field} {M : Field → Measure ℂ}
    (hgood : ∀ᵐ p ∂μ.prod uniformDyadicLaw, (∀ K : Set ℂ, IsCompact K → M p.1 K < ⊤) ∧
      IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 ∧
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
        ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) :
    ∀ᵐ p ∂μ.prod uniformDyadicLaw, ∃ a c ℓ : ℝ, 0 < ℓ ∧
      cappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 = cornerSquare a c ℓ ∧
      ∀ u : ℝ × ℝ, rootSample (M p.1) p.2 m u =
        ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I := by
  filter_upwards [hgood] with p hp
  obtain ⟨S, hS⟩ := hp.2.2 _ hm0 hmtop
  have hspec := rootGen_spec hp.1 hp.2.1 hS
  refine ⟨gridFloor p.2.1 p.2.2.1 (rootGen (M p.1) p.2 m) 0, gridFloor p.2.1 p.2.2.2 (rootGen (M p.1) p.2 m) 0,
    (2 : ℝ) ^ (p.2.1 + ((rootGen (M p.1) p.2 m : ℤ) : ℝ)), by positivity, ?_, fun u => rfl⟩
  rw [hspec.2, squareAt, Complex.zero_re, Complex.zero_im]

theorem measurable_nearMass {M : Field → Measure ℂ} (hM : Measurable M) (m : ℝ≥0∞) (R : ℝ) :
    Measurable fun x : Field × DyCoord => nearMass (M x.1) x.2 m R := by
  have hs : MeasurableSet {y : (Field × DyCoord) × (ℝ × ℝ) | ‖rootSample (M y.1.1) y.1.2 m y.2‖ ≤ R} :=
    measurableSet_le (measurable_rootSample_comp (hM.comp measurable_fst.fst) measurable_fst.snd
      measurable_snd m).norm measurable_const
  have h := measurable_measure_prodMk_left (ν := unifSquareLaw) hs
  exact h

/-- The probability that the uniform root lies in the closed disc of radius `R` is the mean over the pairs
`(h, q)` of the conditional probability `nearMass`. -/
theorem measure_rootSample_le_eq {μ : Measure Field} [SFinite μ] {M : Field → Measure ℂ}
    (hM : Measurable M) (m : ℝ≥0∞) (R : ℝ) :
    (μ.prod (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1))))
        {p | ‖rootSample (M p.1) p.2.1 m p.2.2.1‖ ≤ R} =
      ∫⁻ x, nearMass (M x.1) x.2 m R ∂(μ.prod uniformDyadicLaw) := by
  have hs : MeasurableSet {p : Field × DyCoord × (ℝ × ℝ) × ℝ | ‖rootSample (M p.1) p.2.1 m p.2.2.1‖ ≤ R} :=
    measurableSet_le (measurable_rootSample_comp (hM.comp measurable_fst) measurable_snd.fst
      measurable_snd.snd.fst m).norm measurable_const
  rw [Measure.prod_apply hs, lintegral_prod _ (measurable_nearMass hM m R).aemeasurable]
  refine lintegral_congr fun h => ?_
  rw [Measure.prod_apply (measurable_prodMk_left hs)]
  refine lintegral_congr fun q => ?_
  have hset : Prod.mk q ⁻¹' (Prod.mk h ⁻¹' {p : Field × DyCoord × (ℝ × ℝ) × ℝ |
      ‖rootSample (M p.1) p.2.1 m p.2.2.1‖ ≤ R}) =
      {u : ℝ × ℝ | ‖rootSample (M h) q m u‖ ≤ R} ×ˢ (univ : Set ℝ) := by
    ext w
    exact ⟨fun hw => Set.mem_prod.2 ⟨hw, mem_univ _⟩, fun hw => (Set.mem_prod.1 hw).1⟩
  show _ = unifSquareLaw {u : ℝ × ℝ | ‖rootSample (M h) q m u‖ ≤ R}
  rw [hset, Measure.prod_prod, measure_univ, mul_one]

/-- **Escape of the uniform roots**: on the good
pairs the conditional probability that the root of `Ŝ_{m+1}` lies in the closed disc of radius `R` tends to `0`
(`tendsto_nearMass`), hence so does the probability, by dominated convergence. -/
theorem tendsto_measure_rootSample_le {μ : Measure Field} [IsProbabilityMeasure μ] {M : Field → Measure ℂ}
    (hM : Measurable M)
    (hgood : ∀ᵐ p ∂μ.prod uniformDyadicLaw, (∀ K : Set ℂ, IsCompact K → M p.1 K < ⊤) ∧
      IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 ∧
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
        ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S) (R : ℝ) :
    Tendsto (fun m : ℕ => (μ.prod (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1))))
      {p | ‖rootSample (M p.1) p.2.1 ((m : ℝ≥0∞) + 1) p.2.2.1‖ ≤ R}) atTop (𝓝 0) := by
  have hpt : ∀ᵐ x ∂μ.prod uniformDyadicLaw,
      Tendsto (fun m : ℕ => nearMass (M x.1) x.2 ((m : ℝ≥0∞) + 1) R) atTop (𝓝 0) := by
    filter_upwards [hgood] with p hp
    exact tendsto_nearMass hp.1 hp.2.1 hp.2.2 R
  have hfin : ∫⁻ _, (1 : ℝ≥0∞) ∂(μ.prod uniformDyadicLaw) ≠ ∞ := by
    rw [lintegral_const, measure_univ, one_mul]
    exact ENNReal.one_ne_top
  have hle : ∀ (m : ℕ) (x : Field × DyCoord), nearMass (M x.1) x.2 ((m : ℝ≥0∞) + 1) R ≤ 1 := by
    intro _ _
    unfold nearMass
    exact prob_le_one
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := μ.prod uniformDyadicLaw)
    (F := fun (m : ℕ) (x : Field × DyCoord) => nearMass (M x.1) x.2 ((m : ℝ≥0∞) + 1) R)
    (f := fun _ => 0) (fun _ => (1 : ℝ≥0∞)) (fun m => measurable_nearMass hM _ R)
    (fun m => ae_of_all _ (hle m)) hfin hpt
  simp only [lintegral_zero] at hlim
  exact hlim.congr fun m => (measure_rootSample_le_eq hM _ R).symm

/-- **The re-rooted fields at the uniform roots**: if Lemma A.4 holds at the uniform roots of the capped squares
`Ŝ_{m+1}` (a random constant `C_m` with `h(C_m · + z_m) + Q log C_m =d h`) and the pairs `(h, q)` are almost surely
good, then the auxiliary space `(q, u, v)` with the roots `z_m = rootSample (M h) q (m + 1) u` gives the
conclusion of `ZeroConeLemmaA4`: the roots escape to infinity in probability. -/
theorem exists_reroot_of_uniformRoot (γ : ℝ) {μ : Measure Field} [IsProbabilityMeasure μ]
    {M : Field → Measure ℂ} (hM : Measurable M)
    (hgood : ∀ᵐ p ∂μ.prod uniformDyadicLaw, (∀ K : Set ℂ, IsCompact K → M p.1 K < ⊤) ∧
      IsOffGrid p.2.1 p.2.2.1 p.2.2.2 0 ∧
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
        ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S)
    (hlaw : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ Z : Field × DyCoord × (ℝ × ℝ) → ℂ, Measurable Z →
      (∀ᵐ p ∂μ.prod uniformDyadicLaw, ∃ a c ℓ : ℝ, 0 < ℓ ∧
          cappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 = cornerSquare a c ℓ ∧
          ∀ u : ℝ × ℝ, Z (p.1, p.2, u) = ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) →
        ∃ C : Field × DyCoord × (ℝ × ℝ) × ℝ → ℝ, Measurable C ∧ (∀ x, 0 < C x) ∧
          (μ.prod (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1)))).map
            (fun x => lqgSimilarityField γ (C x) (Z (x.1, x.2.1, x.2.2.1)) x.1) = μ) :
    ∃ (E : Type) (_ : MeasurableSpace E) (κ : Measure E) (_ : IsProbabilityMeasure κ)
      (C : ℕ → Field × E → ℝ) (z : ℕ → Field × E → ℂ),
      (∀ m, Measurable (C m)) ∧ (∀ m, Measurable (z m)) ∧ (∀ m p, 0 < C m p) ∧
      (∀ m, (μ.prod κ).map (fun p => lqgSimilarityField γ (C m p) (z m p) p.1) = μ) ∧
      ∀ R : ℝ, Tendsto (fun m => (μ.prod κ) {p | ‖z m p‖ ≤ R}) atTop (𝓝 0) := by
  have hm0 : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) ≠ 0 := fun m => (zero_lt_one.trans_le le_add_self).ne'
  have hmtop : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) ≠ ∞ := fun m =>
    ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩
  have hZm : ∀ m : ℕ, Measurable fun x : Field × DyCoord × (ℝ × ℝ) =>
      rootSample (M x.1) x.2.1 ((m : ℝ≥0∞) + 1) x.2.2 := fun m =>
    measurable_rootSample_comp (hM.comp measurable_fst) measurable_snd.fst measurable_snd.snd _
  have key : ∀ m : ℕ, ∃ C : Field × DyCoord × (ℝ × ℝ) × ℝ → ℝ, Measurable C ∧ (∀ x, 0 < C x) ∧
      (μ.prod (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1)))).map
        (fun x => lqgSimilarityField γ (C x) (rootSample (M x.1) x.2.1 ((m : ℝ≥0∞) + 1) x.2.2.1) x.1) = μ :=
    fun m => hlaw ((m : ℝ≥0∞) + 1) (hm0 m) (hmtop m)
      (fun x => rootSample (M x.1) x.2.1 ((m : ℝ≥0∞) + 1) x.2.2) (hZm m)
      (ae_rootSample_affine hgood (hm0 m) (hmtop m))
  choose C hCm hCpos hClaw using key
  have hzm : ∀ m : ℕ, Measurable fun p : Field × DyCoord × (ℝ × ℝ) × ℝ =>
      rootSample (M p.1) p.2.1 ((m : ℝ≥0∞) + 1) p.2.2.1 := fun m =>
    measurable_rootSample_comp (hM.comp measurable_fst) measurable_snd.fst measurable_snd.snd.fst _
  exact ⟨DyCoord × (ℝ × ℝ) × ℝ, inferInstance, uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1)),
    inferInstance, C, fun m p => rootSample (M p.1) p.2.1 ((m : ℝ≥0∞) + 1) p.2.2.1, hCm, hzm, hCpos, hClaw,
    tendsto_measure_rootSample_le hM hgood⟩

end Assembly

end ZeroConeRoot

open ZeroConeRoot
open LatticeProb.DyadicOffset (unifIco dyadicSquares cornerSquare gridFloor squareAt IsOffGrid
  ae_isCompatible_isOffGrid_system)
open LatticeProb.CappedSquare (IsCappedSquare cappedSquare)

/-- **Lemma A.4 of Gwynne–Miller–Sheffield, with the existence of the square (A.2)** (arXiv:1705.11161v5, p. 38, (A.2)
and Lemma A.4: "For `m > 0`, let `Ŝ_m` be as in (A.2) and let `z_m` be
sampled uniformly from Lebesgue measure on `Ŝ_m`, normalized to be a probability measure. Then `(ℂ, h, z_m, ∞)`
agrees in law with `(ℂ, h, 0, ∞)` as a quantum surface, i.e., there is a random constant `C_m > 0` such that
`h(C_m · + z_m) + Q log C_m =d h`"; the Lean field is the circle-average embedding of the `0`-quantum cone,
Duplantier–Miller–Sheffield, arXiv:1409.7055, Remark 4.4 and Definition 4.10). This form holds for every
`0 < γ < 2`: the existence of `Ŝ_m` follows from local finiteness, infinite total mass and zero mass at the origin,
and the measurable constant is obtained by sampling the conditional law of the scale given the field and the root
with the independent variable `v`. Its law clause needs Duplantier–Miller–Sheffield, arXiv:1409.7055,
Proposition 4.13(ii) (local total-variation convergence to the `0`-quantum cone), which is not formalized. Hence the
statement is a named printed input of the theorems that use it; no Lean proof of it is claimed.

**Differences from the printed statement.** (A.2) only defines `Ŝ_m`; its existence for every `m ∈ (0, ∞)`
simultaneously, almost surely, is included here (the first conjunct). GMS give a random constant `C_m` on some
probability space; here `C_m` is a Borel function of `(h, q, u, v)` for each prescribed measurable sampler `Z(h, q, u)`
which is almost surely the affine parametrization of `Ŝ_m`, with `v` an independent uniform variable. The area
measure is any Borel version of the vague limit of the area approximations.

Let `h = coneField X₀' (coneRadial γ 0 b b')` be the circle-average embedding of the `0`-quantum cone built from a
whole-plane GFF `X₀'` and two independent standard Brownian motions independent of it (`zeroConeFieldOf`), with law
`μ`, let `M` be a Borel map from fields to measures which is `μ`-almost surely the vague limit of the area
approximations (the area measure `μ_h = M h`), and let `q = (s, o¹, o²)` be an independent uniform dyadic system
(`uniformDyadicLaw`). Then:

* (A.2) almost surely, for every `m ∈ (0, ∞)`, the largest square `Ŝ_m` of the system containing `0` with
  `μ_h(Ŝ_m) ≤ m` exists (`IsCappedSquare`);
* (Lemma A.4) for every `m ∈ (0, ∞)` and every measurable sampler `Z(h, q, u)` which, for almost every `(h, q)`,
  is the affine parametrization `u ↦ (a + ℓ u₁) + i (c + ℓ u₂)` of `Ŝ_m = [a, a + ℓ] × [c, c + ℓ]` (so that `Z` is
  a uniform point of `Ŝ_m` for `u` uniform on `[0, 1)²`), there is a measurable `C_m > 0` of `(h, q, u, v)`, with
  `v` an independent uniform variable on `[0, 1)` (an extension of the probability space carrying the random
  constant), such that `h(C_m · + Z) + Q log C_m` has law `μ` under
  `μ ⊗ uniformDyadicLaw ⊗ unifSquareLaw ⊗ unif[0, 1)`. -/
def ZeroConeUniformRootLemmaA4 (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∀ M : Field → Measure ℂ, Measurable M →
      (∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), IsVagueLimitC (lqgAreaApprox γ h) (M h)) →
      (∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
          ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S) ∧
      ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ Z : Field × DyCoord × (ℝ × ℝ) → ℂ, Measurable Z →
        (∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod uniformDyadicLaw, ∃ a c ℓ : ℝ, 0 < ℓ ∧
          cappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 = cornerSquare a c ℓ ∧
          ∀ u : ℝ × ℝ, Z (p.1, p.2, u) = ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) →
        ∃ C : Field × DyCoord × (ℝ × ℝ) × ℝ → ℝ, Measurable C ∧ (∀ x, 0 < C x) ∧
          ((P'.map (zeroConeFieldOf γ X₀' b b')).prod
              (uniformDyadicLaw.prod (unifSquareLaw.prod (unifIco 1)))).map
            (fun x => lqgSimilarityField γ (C x) (Z (x.1, x.2.1, x.2.2.1)) x.1) =
            P'.map (zeroConeFieldOf γ X₀' b b')

/-- **Lemma A.4 of Gwynne–Miller–Sheffield for the circle-average embedding of the `0`-quantum cone**
(`ZeroConeLemmaA4`), from Lemma A.4 at uniform roots of the capped squares (`ZeroConeUniformRootLemmaA4`). The escape
`P(|z_m| ≤ R) → 0` and the measurable parameters on `Field × E` are additions to the printed lemma, proved in this
file. The auxiliary space carries an independent
uniform dyadic system `q`, a uniform point `u` of `[0, 1)²` and a uniform variable `v`; the area measure is the
Borel map `fieldArea γ`, almost surely the vague limit of the area approximations. The root `z_m` is the point
`corner + side · (u₁ + i u₂)` of the square of generation `rootGen` of the chain of dyadic squares at the origin,
which is almost surely the capped square `Ŝ_{m+1}` (`rootGen_spec`, at the off-grid origin of almost every dyadic
system). Since every fixed square of the chain has finite mass, the generation of `Ŝ_{m+1}` tends to infinity, the
probability that `z_m` lies in a fixed disc tends to `0` for almost every `(h, q)` (`tendsto_nearMass`), and
`P(|z_m| ≤ R) → 0` by dominated convergence. -/
theorem zeroConeLemmaA4 (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) :
    ZeroConeLemmaA4 γ hγ := by
  intro Ω' _ P' X₀' b b' hP hX hb hb' hXbb hbb'
  have hHm := aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hMv := ae_isVagueLimitC_fieldArea hγ hX hb hb' hXbb hbb'
  obtain ⟨hA2, hlaw⟩ :=
    hA4 P' X₀' b b' hP hX hb hb' hXbb hbb' (fieldArea γ) (measurable_fieldArea γ) hMv
  /- the good pairs (field, dyadic system) -/
  have hgood := ae_goodPair (M := fieldArea γ) (hMv.mono fun _ hh => hh.1) hA2
  exact exists_reroot_of_uniformRoot γ (measurable_fieldArea γ) hgood hlaw

end MatedCRT
