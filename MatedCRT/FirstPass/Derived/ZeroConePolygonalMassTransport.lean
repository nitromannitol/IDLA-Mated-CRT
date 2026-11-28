import MatedCRT.FirstPass.Derived.ZeroConePolygonalPremises
import MatedCRT.FirstPass.Derived.CappedSquareResamplingMassTransport

/-!
# Mass transport from an exact rerooting identity over random squares

Let `H` be a random cell configuration on a probability space, let `U_n = [a_n, a_n + ℓ_n] × [b_n, b_n + ℓ_n]`
be random closed squares which almost surely eventually contain every ball around the origin, and let
`C_n = exp c_n > 0` be random scale factors depending on everything and on a point `z`. Suppose that the
rerooting is *exact* at every level: if `z` is sampled uniformly from Lebesgue measure on `U_n` given everything,
then `C_n (H - z)` has the law `μ` for every `n` (`ExactSquareRerooting μ`). This is the identity given at each level
by the uniform roots of the capped squares of Gwynne–Miller–Sheffield, arXiv:1705.11161v5, Lemma A.4 (p. 38).

This file proves that `μ` has the dyadic-system re-sampling property of Gwynne–Miller–Sheffield,
arXiv:1807.07515v3, Lemma 2.3, condition 5 (`CappedSquareResampling μ`), and hence satisfies the mass-transport
principle (`massTransport_of_exactSquareRerooting`, through `massTransport_of_cappedSquareResampling`). The argument
is the direct form of the last step of Appendix B of arXiv:1807.07515v3 (paragraph "Condition 2 ⇒ Condition 5",
(B.3)-(B.4), p. 51) available when the identity is exact:

* by the exact identity, the invariance of the test function and the invariance of the law of a uniform dyadic
  system under similarities (Lemma 2.1 there), both sides of the re-sampling identity are, at each level `n`, the
  averages over `z ∈ U_n` of the expectations of `G(H, D, z)` and of its average over the capped square `B_n` of a
  fresh independent dyadic system `D` at `z` (`lintegral_eq_lintegral_window`);
* the capped squares partition the plane up to grid lines, so the two window averages differ by at most
  `2 sup G · P(B_n ⊄ U_n)` (`lintegral_window_le_add`, `lintegral_window_le_add'`);
* `P(B_n ⊄ U_n) → 0`: the rescaled cap `C_n (B_n - z)` has a fixed law, and the rescaled window `C_n (U_n - z)`
  becomes large, since the cell mass of `U_n` tends to infinity while the cell mass of a fixed ball has a fixed
  finite law; the area fraction of a square within `δ ℓ_n` of its boundary is at most `4 δ`
  (`tendsto_zero_errorBound`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare LatticeProb.CellMass
  LatticeProb.CappedSquare LatticeProb.DyadicOffset

/-- **Exact rerooting over random squares**: `μ` is the law of the configuration `C_n (H - z)` rerooted at a point
`z` sampled uniformly from Lebesgue measure on a random square `U_n = [a_n, a_n + ℓ_n] × [b_n, b_n + ℓ_n]`, at every
level `n`, where `C_n = exp c_n` depends on everything and on `z`, and the squares eventually contain every ball
around the origin almost surely. The identity is stated for every measurable test function `F ≥ 0`. -/
def ExactSquareRerooting (μ : Measure GMSSpace) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (H : Ω → GMSSpace),
    IsProbabilityMeasure P ∧ AEMeasurable H P ∧
    ∃ a b ℓ : ℕ → Ω → ℝ, (∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n)) ∧
      (∀ n ω, 0 < ℓ n ω) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ, ∀ᶠ n in atTop,
        Metric.ball (0 : ReflectedGMS.Plane) r ⊆ planeSquare (a n ω) (b n ω) (ℓ n ω)) ∧
      ∃ c : ℕ → Ω × ReflectedGMS.Plane → ℝ, (∀ n, Measurable (c n)) ∧
        ∀ n (F : GMSSpace → ℝ≥0∞), Measurable F →
          ∫⁻ ω, (⨍⁻ z in planeSquare (a n ω) (b n ω) (ℓ n ω),
            F (similarityConfig (c n (ω, z)) z (H ω)) ∂volume) ∂P = ∫⁻ H', F H' ∂μ

/-! ### Squares of the plane in the coordinates `ℂ` -/

theorem planeCoord_apply_zero (v : ℂ) : planeCoord v 0 = v.re := rfl

theorem planeCoord_apply_one (v : ℂ) : planeCoord v 1 = v.im := rfl

theorem preimage_planeSquare (a b ℓ : ℝ) :
    planeCoordMeas ⁻¹' planeSquare a b ℓ = cornerSquare a b ℓ := by
  ext v
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

theorem volume_cornerSquare_ne_zero (a b : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    volume (cornerSquare a b ℓ) ≠ 0 := by
  rw [volume_cornerSquare]
  exact mul_ne_zero (ENNReal.ofReal_pos.2 hℓ).ne' (ENNReal.ofReal_pos.2 hℓ).ne'

theorem volume_cornerSquare_ne_top (a b ℓ : ℝ) : volume (cornerSquare a b ℓ) ≠ ∞ := by
  rw [volume_cornerSquare]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The uniform average over a square of the plane, read in the coordinates `ℂ`. -/
theorem setLAverage_planeSquare_eq (a b ℓ : ℝ) (f : Plane → ℝ≥0∞) :
    ⨍⁻ z in planeSquare a b ℓ, f z ∂volume = (volume (cornerSquare a b ℓ))⁻¹ *
      ∫⁻ v : ℂ, (cornerSquare a b ℓ).indicator (fun _ => (1 : ℝ≥0∞)) v * f (planeCoord v) := by
  have hmp := measurePreserving_planeCoordMeas
  have hint : ∫⁻ z in planeSquare a b ℓ, f z =
      ∫⁻ v : ℂ, (cornerSquare a b ℓ).indicator (fun _ => (1 : ℝ≥0∞)) v * f (planeCoord v) := by
    rw [← hmp.setLIntegral_comp_preimage_emb planeCoordMeas.measurableEmbedding, preimage_planeSquare,
      ← lintegral_indicator (measurableSet_cornerSquare a b ℓ)]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ cornerSquare a b ℓ
    · rw [indicator_of_mem hv, indicator_of_mem hv, one_mul]
      rfl
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
  have hvol : volume (planeSquare a b ℓ) = volume (cornerSquare a b ℓ) := by
    rw [← preimage_planeSquare, hmp.measure_preimage_equiv]
  rw [setLAverage_eq, hint, hvol, div_eq_mul_inv, mul_comm]

/-- The volume of a closed rectangle of `ℂ`. -/
theorem volume_rect (a a' b b' : ℝ) :
    volume {z : ℂ | z.re ∈ Icc a a' ∧ z.im ∈ Icc b b'} = ENNReal.ofReal (a' - a) * ENNReal.ofReal (b' - b) := by
  have hset : {z : ℂ | z.re ∈ Icc a a' ∧ z.im ∈ Icc b b'} =
      Complex.measurableEquivRealProd ⁻¹' (Icc a a' ×ˢ Icc b b') := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod]
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Icc a a' ×ˢ Icc b b') (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc] at h
  rw [hset]
  exact h

/-- The margin condition: `z` lies at distance at least `ρ` inside each side of the square
`[a, a + ℓ] × [b, b + ℓ]`. -/
def InnerMargin (a b ℓ ρ : ℝ) (z : ℂ) : Prop :=
  a + ρ ≤ z.re ∧ z.re + ρ ≤ a + ℓ ∧ b + ρ ≤ z.im ∧ z.im + ρ ≤ b + ℓ

theorem InnerMargin.mem_cornerSquare {a b ℓ ρ : ℝ} {z w : ℂ} (h : InnerMargin a b ℓ ρ z)
    (hw : ‖w - z‖ ≤ ρ) : w ∈ cornerSquare a b ℓ := by
  have h1 := (abs_le.1 ((Complex.abs_re_le_norm (w - z)).trans hw))
  have h2 := (abs_le.1 ((Complex.abs_im_le_norm (w - z)).trans hw))
  rw [Complex.sub_re] at h1
  rw [Complex.sub_im] at h2
  obtain ⟨m1, m2, m3, m4⟩ := h
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

theorem InnerMargin.mono {a b ℓ ρ ρ' : ℝ} {z : ℂ} (h : InnerMargin a b ℓ ρ z) (hρ : ρ' ≤ ρ) :
    InnerMargin a b ℓ ρ' z := by
  obtain ⟨m1, m2, m3, m4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem measurableSet_innerMargin_graph :
    MeasurableSet {p : (ℝ × ℝ × ℝ × ℝ) × ℂ | InnerMargin p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2} := by
  have hre : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.2.re := Complex.measurable_re.comp measurable_snd
  have him : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.2.im := Complex.measurable_im.comp measurable_snd
  have ha : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.1.1 := measurable_fst.fst
  have hb : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.1.2.1 := measurable_fst.snd.fst
  have hl : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.1.2.2.1 := measurable_fst.snd.snd.fst
  have hr : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × ℂ => p.1.2.2.2 := measurable_fst.snd.snd.snd
  exact (measurableSet_le (ha.add hr) hre).inter ((measurableSet_le (hre.add hr) (ha.add hl)).inter
    ((measurableSet_le (hb.add hr) him).inter (measurableSet_le (him.add hr) (hb.add hl))))

/-- **The boundary strip of a square**: the points of `[a, a + ℓ] × [b, b + ℓ]` within `δ ℓ` of its boundary have
area at most `4 δ` times the area of the square. -/
theorem volume_cornerSquare_diff_innerMargin_le (a b : ℝ) {ℓ δ : ℝ} (hδ : 0 ≤ δ) :
    volume (cornerSquare a b ℓ ∩ {z | ¬ InnerMargin a b ℓ (δ * ℓ) z}) ≤
      ENNReal.ofReal (4 * δ) * volume (cornerSquare a b ℓ) := by
  have hsub : cornerSquare a b ℓ ∩ {z | ¬ InnerMargin a b ℓ (δ * ℓ) z} ⊆
      ({z : ℂ | z.re ∈ Icc a (a + δ * ℓ) ∧ z.im ∈ Icc b (b + ℓ)} ∪
        {z : ℂ | z.re ∈ Icc (a + ℓ - δ * ℓ) (a + ℓ) ∧ z.im ∈ Icc b (b + ℓ)}) ∪
      ({z : ℂ | z.re ∈ Icc a (a + ℓ) ∧ z.im ∈ Icc b (b + δ * ℓ)} ∪
        {z : ℂ | z.re ∈ Icc a (a + ℓ) ∧ z.im ∈ Icc (b + ℓ - δ * ℓ) (b + ℓ)}) := by
    rintro z ⟨⟨h1, h2, h3, h4⟩, hz⟩
    simp only [InnerMargin, mem_ofPred_eq, not_and_or, not_le] at hz
    simp only [mem_union, mem_ofPred_eq, mem_Icc]
    rcases hz with hz | hz | hz | hz
    · exact Or.inl (Or.inl ⟨⟨h1, by linarith⟩, h3, h4⟩)
    · exact Or.inl (Or.inr ⟨⟨by linarith, h2⟩, h3, h4⟩)
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, h3, by linarith⟩)
    · exact Or.inr (Or.inr ⟨⟨h1, h2⟩, by linarith, h4⟩)
  have e1 : ENNReal.ofReal (a + δ * ℓ - a) = ENNReal.ofReal (δ * ℓ) := by congr 1; ring
  have e2 : ENNReal.ofReal (a + ℓ - (a + ℓ - δ * ℓ)) = ENNReal.ofReal (δ * ℓ) := by congr 1; ring
  have e3 : ENNReal.ofReal (b + δ * ℓ - b) = ENNReal.ofReal (δ * ℓ) := by congr 1; ring
  have e4 : ENNReal.ofReal (b + ℓ - (b + ℓ - δ * ℓ)) = ENNReal.ofReal (δ * ℓ) := by congr 1; ring
  have e5 : ENNReal.ofReal (a + ℓ - a) = ENNReal.ofReal ℓ := by congr 1; ring
  have e6 : ENNReal.ofReal (b + ℓ - b) = ENNReal.ofReal ℓ := by congr 1; ring
  calc volume (cornerSquare a b ℓ ∩ {z | ¬ InnerMargin a b ℓ (δ * ℓ) z})
      ≤ ENNReal.ofReal (δ * ℓ) * ENNReal.ofReal ℓ + ENNReal.ofReal (δ * ℓ) * ENNReal.ofReal ℓ +
          (ENNReal.ofReal ℓ * ENNReal.ofReal (δ * ℓ) + ENNReal.ofReal ℓ * ENNReal.ofReal (δ * ℓ)) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (le_of_eq ?_)) ((measure_union_le _ _).trans (le_of_eq ?_))))
        · rw [volume_rect, volume_rect, e1, e2, e6]
        · rw [volume_rect, volume_rect, e3, e4, e5]
    _ = ENNReal.ofReal (4 * δ) * volume (cornerSquare a b ℓ) := by
        rw [volume_cornerSquare, ENNReal.ofReal_mul hδ, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        have h4 : ENNReal.ofReal 4 = 4 := by norm_num
        rw [h4]
        ring

/-! ### The uniform-average kernel at a good dyadic system -/

/-- A dyadic system with compatible offset sequences whose squares around every point exhaust the plane (an
almost sure property of the uniform dyadic system). -/
def IsExhaustingSystem (q : DyadicCoord) : Prop :=
  IsCompatible q.2.1 ∧ IsCompatible q.2.2 ∧ ∀ w : ℂ, ⋃ j, squareAt q.1 q.2.1 q.2.2 j w = univ

theorem ae_isExhaustingSystem : ∀ᵐ q ∂dyadicLaw, IsExhaustingSystem q := by
  filter_upwards [ae_isCompatible_system, ae_iUnion_squareAt_eq_univ] with q hq hexh
  exact ⟨hq.1, hq.2, hexh⟩

theorem volume_squareAt_ne_zero_of (q : DyadicCoord) (j : ℤ) (w : ℂ) :
    volume (squareAt q.1 q.2.1 q.2.2 j w) ≠ 0 := by
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ (q.1 + (j : ℝ)) := Real.rpow_pos_of_pos two_pos _
  rw [volume_squareAt]
  exact mul_ne_zero (ENNReal.ofReal_pos.2 hℓ).ne' (ENNReal.ofReal_pos.2 hℓ).ne'

theorem volume_squareAt_ne_top_of (q : DyadicCoord) (j : ℤ) (w : ℂ) :
    volume (squareAt q.1 q.2.1 q.2.2 j w) ≠ ∞ :=
  (isCompact_squareAt j w).measure_lt_top.ne

variable {m : ℝ≥0∞}

/-- At an exhausting system and an off-grid root `z`, a generation is selected and the kernel rooted at `z` is the
uniform density of the square of that generation. -/
theorem exists_averageKernel_eq (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {z : ℂ} (hz : IsOffGrid q.1 q.2.1 q.2.2 z) :
    ∃ j ∈ selectionSet (complexCells H.1) m q z, ∀ w : ℂ,
      averageKernel m (H, (q, z), w) = (volume (squareAt q.1 q.2.1 q.2.2 j z))⁻¹ *
        (squareAt q.1 q.2.1 q.2.2 j z).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have := countable_cells H.2
  obtain ⟨j, hj1, hj2, -⟩ := exists_isCappedSquare_squareAt_cellMass hq.1 hq.2.1 hz (hq.2.2 z)
    (locallyFinite_complexCells H.2) (iUnion_complexCells H.2) isCompact_complexCells
    (volume_complexCells_ne_zero H.2) hm0 hmtop
  refine ⟨j, ⟨hj1, hj2⟩, fun w => ?_⟩
  exact selectedSum_eq_of_mem (c := complexCells H.1)
    (monotone_cellMass_squareAt hq.1 hq.2.1 hz) ⟨hj1, hj2⟩ _

/-- **Symmetry of the kernel**: at an exhausting system, for off-grid `z` and `w`,
`|Ŝ^z|⁻¹ 1(w ∈ Ŝ^z) = |Ŝ^w|⁻¹ 1(z ∈ Ŝ^w)` (arXiv:1807.07515, Lemma 2.2: the capped squares partition the plane up
to grid lines). -/
theorem averageKernel_symm (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {z w : ℂ} (hz : IsOffGrid q.1 q.2.1 q.2.2 z)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 w) :
    averageKernel m (H, (q, z), w) = averageKernel m (H, (q, w), z) := by
  obtain ⟨j, hj, hK⟩ := exists_averageKernel_eq hm0 hmtop H hq hz
  obtain ⟨j', hj', hK'⟩ := exists_averageKernel_eq hm0 hmtop H hq hw
  by_cases hwz : w ∈ squareAt q.1 q.2.1 q.2.2 j z
  · rw [averageKernel_eq_of_mem_squareAt hq.1 hq.2.1 hz hw hj hwz z, hK, hK, indicator_of_mem hwz,
      indicator_of_mem (mem_squareAt (s := q.1) (o₁ := q.2.1) (o₂ := q.2.2) j z)]
  · by_cases hzw : z ∈ squareAt q.1 q.2.1 q.2.2 j' w
    · exfalso
      have h0 : averageKernel m (H, (q, z), w) = 0 := by
        rw [hK, indicator_of_notMem hwz, mul_zero]
      rw [averageKernel_eq_of_mem_squareAt hq.1 hq.2.1 hw hz hj' hzw w, hK',
        indicator_of_mem (mem_squareAt (s := q.1) (o₁ := q.2.1) (o₂ := q.2.2) j' w), mul_one] at h0
      exact ENNReal.inv_ne_zero.2 (volume_squareAt_ne_top_of q j' w) h0
    · rw [hK, hK', indicator_of_notMem hwz, indicator_of_notMem hzw, mul_zero, mul_zero]

/-- At an exhausting system and an off-grid root, the kernel has total mass `1`. -/
theorem lintegral_averageKernel_right (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {z : ℂ} (hz : IsOffGrid q.1 q.2.1 q.2.2 z) :
    ∫⁻ w, averageKernel m (H, (q, z), w) = 1 := by
  obtain ⟨j, -, hK⟩ := exists_averageKernel_eq hm0 hmtop H hq hz
  rw [lintegral_congr hK, lintegral_const_mul _ (measurable_const.indicator (measurableSet_squareAt j z)),
    lintegral_indicator_const (measurableSet_squareAt j z), one_mul]
  exact ENNReal.inv_mul_cancel (volume_squareAt_ne_zero_of q j z) (volume_squareAt_ne_top_of q j z)

/-- At an exhausting system and an off-grid point `w`, the kernel integrated over its root is `1`. -/
theorem lintegral_averageKernel_left (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {w : ℂ} (hw : IsOffGrid q.1 q.2.1 q.2.2 w) :
    ∫⁻ z, averageKernel m (H, (q, z), w) = 1 := by
  rw [← lintegral_averageKernel_right hm0 hmtop H hq hw]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz
  exact averageKernel_symm hm0 hmtop H hq hz hw

theorem measurable_averageKernel_uncurry (m : ℝ≥0∞) (H : GMSSpace) (q : DyadicCoord) :
    Measurable fun x : ℂ × ℂ => averageKernel m (H, (q, x.1), x.2) :=
  (measurable_averageKernel m).comp (measurable_const.prodMk
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))

/-! ### The two averages over a window -/

/-- The kernel mass leaving `V` from roots in `V`: `∫_V |Ŝ^z|⁻¹ |Ŝ^z \ V| dz`. -/
def windowLeak (m : ℝ≥0∞) (H : GMSSpace) (q : DyadicCoord) (V : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z *
    ∫⁻ w, averageKernel m (H, (q, z), w) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w

section Window

variable (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord} (hq : IsExhaustingSystem q)
  {V : Set ℂ} (hV : MeasurableSet V) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
  {M : ℝ≥0∞} (hGM : ∀ p, G p ≤ M)

include hm0 hmtop hq hV hG in
/-- Integrating the window function against the kernel in the root gives back its integral. -/
theorem lintegral_lintegral_averageKernel_window :
    ∫⁻ z, ∫⁻ w, averageKernel m (H, (q, z), w) * (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) =
      ∫⁻ w, V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w) := by
  have hmeas : Measurable fun x : ℂ × ℂ => averageKernel m (H, (q, x.1), x.2) *
      (V.indicator (fun _ => (1 : ℝ≥0∞)) x.2 * G (H, q, x.2)) :=
    (measurable_averageKernel_uncurry m H q).mul (((measurable_const.indicator hV).comp measurable_snd).mul
      (hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))))
  calc ∫⁻ z, ∫⁻ w, averageKernel m (H, (q, z), w) * (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w))
      = ∫⁻ w, ∫⁻ z, averageKernel m (H, (q, z), w) * (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ w, V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w) := by
        refine lintegral_congr_ae ((ae_isOffGrid_volume q.1 q.2.1 q.2.2).mono fun w hw => ?_)
        dsimp only
        have hKw : Measurable fun z => averageKernel m (H, (q, z), w) :=
          (measurable_averageKernel m).comp
            (measurable_const.prodMk ((measurable_const.prodMk measurable_id).prodMk measurable_const))
        rw [lintegral_mul_const _ hKw, lintegral_averageKernel_left hm0 hmtop H hq hw, one_mul]

include hm0 hmtop hq hV hG hGM in
/-- **The window average of the capped-square average is at most the window average plus the leak**. -/
theorem lintegral_window_le_add :
    ∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z) ≤
      (∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z)) + M * windowLeak m H q V := by
  have hKz : ∀ z, Measurable fun w => averageKernel m (H, (q, z), w) := fun _ =>
    (measurable_averageKernel m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hg : Measurable fun w => G (H, q, w) :=
    hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h1 : Measurable (V.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hV
  have h1c : Measurable (Vᶜ.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hV.compl
  have hpt : ∀ z w, averageKernel m (H, (q, z), w) * G (H, q, w) ≤
      averageKernel m (H, (q, z), w) * (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) +
        M * (averageKernel m (H, (q, z), w) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w) := by
    intro z w
    by_cases hw : w ∈ V
    · simp only [indicator_of_mem hw, indicator_of_notMem (fun h : w ∈ Vᶜ => h hw), one_mul, mul_zero,
        add_zero, le_refl]
    · simp only [indicator_of_notMem hw, indicator_of_mem (show w ∈ Vᶜ from hw), zero_mul, mul_zero,
        zero_add, mul_one]
      rw [mul_comm M]
      exact mul_le_mul_right (hGM _) _
  have hA : Measurable fun z => ∫⁻ w, averageKernel m (H, (q, z), w) *
      (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) :=
    Measurable.lintegral_prod_right' (f := fun x : ℂ × ℂ => averageKernel m (H, (q, x.1), x.2) *
      (V.indicator (fun _ => (1 : ℝ≥0∞)) x.2 * G (H, q, x.2)))
      ((measurable_averageKernel_uncurry m H q).mul ((h1.comp measurable_snd).mul (hg.comp measurable_snd)))
  have hB : Measurable fun z => V.indicator (fun _ => (1 : ℝ≥0∞)) z *
      ∫⁻ w, averageKernel m (H, (q, z), w) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w :=
    h1.mul (Measurable.lintegral_prod_right' (f := fun x : ℂ × ℂ => averageKernel m (H, (q, x.1), x.2) *
      Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x.2)
      ((measurable_averageKernel_uncurry m H q).mul (h1c.comp measurable_snd)))
  calc ∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z)
      ≤ ∫⁻ z, ((∫⁻ w, averageKernel m (H, (q, z), w) *
            (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w))) +
          M * (V.indicator (fun _ => (1 : ℝ≥0∞)) z *
            ∫⁻ w, averageKernel m (H, (q, z), w) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w)) := by
        refine lintegral_mono fun z => ?_
        have hle : kernelAverage m G (H, q, z) ≤
            (∫⁻ w, averageKernel m (H, (q, z), w) *
              (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w))) +
            M * ∫⁻ w, averageKernel m (H, (q, z), w) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w := by
          have hm1 : Measurable fun w => averageKernel m (H, (q, z), w) *
              (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) := (hKz z).mul (h1.mul hg)
          have hm2 : Measurable fun w => averageKernel m (H, (q, z), w) *
              Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w := (hKz z).mul h1c
          refine (lintegral_mono (hpt z)).trans_eq ?_
          rw [lintegral_add_left hm1, lintegral_const_mul _ hm2]
        by_cases hz : z ∈ V
        · rw [indicator_of_mem hz, one_mul, one_mul]
          exact hle
        · rw [indicator_of_notMem hz, zero_mul, zero_mul, mul_zero, add_zero]
          exact zero_le
    _ = (∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z)) + M * windowLeak m H q V := by
        rw [lintegral_add_left hA, lintegral_const_mul _ hB,
          lintegral_lintegral_averageKernel_window hm0 hmtop H hq hV hG, windowLeak]

include hm0 hmtop hq hV hG hGM in
/-- **The window average is at most the window average of the capped-square average plus the leak**. -/
theorem lintegral_window_le_add' :
    ∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z) ≤
      (∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z)) +
        M * windowLeak m H q V := by
  have hKz : ∀ z, Measurable fun w => averageKernel m (H, (q, z), w) := fun _ =>
    (measurable_averageKernel m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hg : Measurable fun w => G (H, q, w) :=
    hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h1 : Measurable (V.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hV
  have h1c : Measurable (Vᶜ.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hV.compl
  have hKA : Measurable fun z => V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z) :=
    h1.mul ((measurable_kernelAverage m hG).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hC : Measurable fun z => Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
      ∫⁻ w, averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w :=
    h1c.mul (Measurable.lintegral_prod_right' (f := fun x : ℂ × ℂ => averageKernel m (H, (q, x.1), x.2) *
      V.indicator (fun _ => (1 : ℝ≥0∞)) x.2)
      ((measurable_averageKernel_uncurry m H q).mul (h1.comp measurable_snd)))
  have hY : ∫⁻ z, Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
      ∫⁻ w, averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w = windowLeak m H q V := by
    have hmeas : Measurable fun x : ℂ × ℂ => Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x.1 *
        (averageKernel m (H, (q, x.2), x.1) * V.indicator (fun _ => (1 : ℝ≥0∞)) x.2) :=
      (h1c.comp measurable_fst).mul (((measurable_averageKernel m).comp (measurable_const.prodMk
        ((measurable_const.prodMk measurable_snd).prodMk measurable_fst))).mul (h1.comp measurable_snd))
    calc ∫⁻ z, Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
          ∫⁻ w, averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w
        = ∫⁻ z, ∫⁻ w, Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
            (averageKernel m (H, (q, w), z) * V.indicator (fun _ => (1 : ℝ≥0∞)) w) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz
          have hm1 : Measurable fun w => averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w :=
            (hKz z).mul h1
          rw [← lintegral_const_mul _ hm1]
          refine lintegral_congr_ae ?_
          filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with w hw
          rw [averageKernel_symm hm0 hmtop H hq hz hw]
      _ = ∫⁻ w, ∫⁻ z, Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
            (averageKernel m (H, (q, w), z) * V.indicator (fun _ => (1 : ℝ≥0∞)) w) :=
          lintegral_lintegral_swap (f := fun z w => Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
            (averageKernel m (H, (q, w), z) * V.indicator (fun _ => (1 : ℝ≥0∞)) w)) hmeas.aemeasurable
      _ = windowLeak m H q V := by
          rw [windowLeak]
          refine lintegral_congr fun w => ?_
          have hm1 : Measurable fun z => averageKernel m (H, (q, w), z) * Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z :=
            (hKz w).mul h1c
          rw [← lintegral_const_mul _ hm1]
          refine lintegral_congr fun z => ?_
          ring
  calc ∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z)
      = ∫⁻ z, ∫⁻ w, averageKernel m (H, (q, z), w) *
          (V.indicator (fun _ => (1 : ℝ≥0∞)) w * G (H, q, w)) :=
        (lintegral_lintegral_averageKernel_window hm0 hmtop H hq hV hG).symm
    _ ≤ ∫⁻ z, (V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z) +
          M * (Vᶜ.indicator (fun _ => (1 : ℝ≥0∞)) z *
            ∫⁻ w, averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w)) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ V
        · rw [indicator_of_mem hz, indicator_of_notMem (fun h : z ∈ Vᶜ => h hz), one_mul, zero_mul, mul_zero,
            add_zero]
          refine lintegral_mono fun w => mul_le_mul_right ?_ _
          by_cases hw : w ∈ V
          · rw [indicator_of_mem hw, one_mul]
          · rw [indicator_of_notMem hw, zero_mul]
            exact zero_le
        · have hm1 : Measurable fun w => averageKernel m (H, (q, z), w) * V.indicator (fun _ => (1 : ℝ≥0∞)) w :=
            (hKz z).mul h1
          rw [indicator_of_notMem hz, indicator_of_mem (show z ∈ Vᶜ from hz), zero_mul, one_mul, zero_add,
            ← lintegral_const_mul _ hm1]
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ V
          · rw [indicator_of_mem hw, one_mul, mul_one, mul_comm M]
            exact mul_le_mul_right (hGM _) _
          · simp only [indicator_of_notMem hw, zero_mul, mul_zero, le_refl]
    _ = (∫⁻ z, V.indicator (fun _ => (1 : ℝ≥0∞)) z * kernelAverage m G (H, q, z)) +
          M * windowLeak m H q V := by
        rw [lintegral_add_left hKA, lintegral_const_mul _ hC, hY]

end Window

/-! ### Rescaling the root and the dyadic system -/

/-- Invariance of a function of the rooted configuration and the dyadic system under the joint similarity, at
every dyadic system with compatible offset sequences (the hypothesis on the test functions of
`CappedSquareResampling`). -/
def IsJointlyInvariant (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
    ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
      G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)

theorem smul_add_similarityOffset_self (s : ℝ) (z : Plane) : s • planeCoord.symm z + similarityOffset s z = 0 := by
  rw [similarityOffset, add_neg_cancel]

theorem isSimilar_similarityConfig (c : ℝ) (z : Plane) (H : GMSSpace) :
    IsSimilar (Real.exp c) z (Real.exp_pos c) H (similarityConfig c z H) := rfl

/-- **Rerooting the dyadic system** (the law of the uniform dyadic system is invariant under similarities,
arXiv:1807.07515, Lemma 2.1): if `F₂` at `C (H - z)`, the transformed system and the origin is `F₁` at `H`, the
system and the root `z`, then the expectations over the dyadic system agree. -/
theorem lintegral_dyadic_similarityConfig {F₁ F₂ : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hF₂ : Measurable F₂)
    (c : ℝ) (z : Plane) (H : GMSSpace)
    (hcov : ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 →
      F₂ (similarityConfig c z H, similarityCoord (Real.exp c) z q, 0) = F₁ (H, q, planeCoord.symm z)) :
    ∫⁻ q, F₂ (similarityConfig c z H, q, 0) ∂dyadicLaw = ∫⁻ q, F₁ (H, q, planeCoord.symm z) ∂dyadicLaw := by
  have hf : Measurable fun q : DyadicCoord => F₂ (similarityConfig c z H, q, 0) :=
    hF₂.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  refine ((measurePreserving_similarityCoord (Real.exp c) z).lintegral_comp hf).symm.trans ?_
  refine lintegral_congr_ae ?_
  filter_upwards [ae_isCompatible_system] with q hq
  exact hcov q hq.1 hq.2

theorem lintegral_dyadic_similarityConfig_of_invariant {F : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hF : Measurable F) (hinv : IsJointlyInvariant F) (c : ℝ) (z : Plane) (H : GMSSpace) :
    ∫⁻ q, F (similarityConfig c z H, q, 0) ∂dyadicLaw = ∫⁻ q, F (H, q, planeCoord.symm z) ∂dyadicLaw :=
  lintegral_dyadic_similarityConfig hF c z H fun q h₁ h₂ => by
    have h := hinv (Real.exp c) z (Real.exp_pos c) H _ (isSimilar_similarityConfig c z H) q h₁ h₂
      (planeCoord.symm z)
    rwa [smul_add_similarityOffset_self] at h

/-! ### The far part of the capped square -/

/-- The triples `((ρ, z), w)` with `‖w - z‖ > ρ`. -/
def farSet : Set ((ℝ × ℂ) × ℂ) := {y | y.1.1 < ‖y.2 - y.1.2‖}

theorem measurableSet_farSet : MeasurableSet farSet :=
  measurableSet_lt measurable_fst.fst (continuous_snd.sub continuous_fst.snd).norm.measurable

/-- The fraction `|Ŝ^z \ B̄(z, ρ)| / |Ŝ^z|` of the capped square around `z` lying farther than `ρ` from `z`; the
argument is `(H, q, z)`. -/
def capTail (m : ℝ≥0∞) (ρ : ℝ) (p : GMSSpace × DyadicCoord × ℂ) : ℝ≥0∞ :=
  ∫⁻ w, averageKernel m (p.1, (p.2.1, p.2.2), w) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ, p.2.2), w)

theorem measurable_capTail_uncurry (m : ℝ≥0∞) :
    Measurable fun x : ℝ × (GMSSpace × DyadicCoord × ℂ) => capTail m x.1 x.2 :=
  Measurable.lintegral_prod_right' (f := fun y : (ℝ × (GMSSpace × DyadicCoord × ℂ)) × ℂ =>
      averageKernel m (y.1.2.1, (y.1.2.2.1, y.1.2.2.2), y.2) *
        farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((y.1.1, y.1.2.2.2), y.2))
    (((measurable_averageKernel m).comp (measurable_fst.snd.fst.prodMk
      ((measurable_fst.snd.snd.fst.prodMk measurable_fst.snd.snd.snd).prodMk measurable_snd))).mul
      ((measurable_const.indicator measurableSet_farSet).comp
        ((measurable_fst.fst.prodMk measurable_fst.snd.snd.snd).prodMk measurable_snd)))

theorem measurable_capTail (m : ℝ≥0∞) (ρ : ℝ) : Measurable (capTail m ρ) :=
  Measurable.lintegral_prod_right' (f := fun y : (GMSSpace × DyadicCoord × ℂ) × ℂ =>
      averageKernel m (y.1.1, (y.1.2.1, y.1.2.2), y.2) *
        farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ, y.1.2.2), y.2))
    (((measurable_averageKernel m).comp (measurable_fst.fst.prodMk
      ((measurable_fst.snd.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd))).mul
      ((measurable_const.indicator measurableSet_farSet).comp
        ((measurable_const.prodMk measurable_fst.snd.snd).prodMk measurable_snd)))

theorem measurable_capTail_section (m : ℝ≥0∞) (H₁ : GMSSpace) {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable fun y : DyadicCoord × ℂ => capTail m (ρ y.2) (H₁, y.1, y.2) :=
  Measurable.lintegral_prod_right' (f := fun z : (DyadicCoord × ℂ) × ℂ =>
      averageKernel m (H₁, (z.1.1, z.1.2), z.2) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ z.1.2, z.1.2), z.2))
    (((measurable_averageKernel m).comp (measurable_const.prodMk
      ((measurable_fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd))).mul
      ((measurable_const.indicator measurableSet_farSet).comp
        (((hρ.comp measurable_fst.snd).prodMk measurable_fst.snd).prodMk measurable_snd)))

/-- **Covariance of the far part**: the far part beyond `s ρ` of the capped square of `C(H - u)` around `T z`, for the
transformed system, is the far part beyond `ρ` of the capped square of `H` around `z`, `T z = s • z + b`. -/
theorem capTail_similarity (m : ℝ≥0∞) {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H') {q : DyadicCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (ρ : ℝ) (z : ℂ) :
    capTail m (s * ρ) (H', similarityCoord s u q, s • z + similarityOffset s u) = capTail m ρ (H, q, z) := by
  have hF : Measurable fun w : ℂ =>
      averageKernel m (H', (similarityCoord s u q, s • z + similarityOffset s u), w) *
        farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((s * ρ, s • z + similarityOffset s u), w) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      ((measurable_const.indicator measurableSet_farSet).comp (measurable_const.prodMk measurable_id))
  have hFH : Measurable fun w : ℂ =>
      averageKernel m (H, (q, z), w) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ, z), w) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      ((measurable_const.indicator measurableSet_farSet).comp (measurable_const.prodMk measurable_id))
  have hfar : ∀ w : ℂ, farSet.indicator (fun _ => (1 : ℝ≥0∞))
      ((s * ρ, s • z + similarityOffset s u), s • w + similarityOffset s u) =
      farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ, z), w) := by
    intro w
    have hn : ‖s • w + similarityOffset s u - (s • z + similarityOffset s u)‖ = s * ‖w - z‖ := by
      rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hiff : ((s * ρ, s • z + similarityOffset s u), s • w + similarityOffset s u) ∈ farSet ↔
        ((ρ, z), w) ∈ farSet := by
      show s * ρ < ‖s • w + similarityOffset s u - (s • z + similarityOffset s u)‖ ↔ ρ < ‖w - z‖
      rw [hn]
      exact ⟨fun h => lt_of_mul_lt_mul_left h hs.le, fun h => mul_lt_mul_of_pos_left h hs⟩
    by_cases h : ((ρ, z), w) ∈ farSet
    · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.1 h'))]
  have key : ENNReal.ofReal ((s ^ 2)⁻¹) *
        capTail m (s * ρ) (H', similarityCoord s u q, s • z + similarityOffset s u) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * capTail m ρ (H, q, z) := by
    dsimp only [capTail]
    rw [← lintegral_comp_smul_add_complex hF hs (similarityOffset s u), ← lintegral_const_mul _ hFH]
    refine lintegral_congr fun w => ?_
    rw [averageKernel_similarity hHH' q h₁ h₂ m z w, hfar w, mul_assoc]
  have hc0 : ENNReal.ofReal ((s ^ 2)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hs 2))).ne'
  exact (ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top).1 key

/-- The far part beyond `r / C` around `z`, in expectation over the dyadic system, is the far part beyond `r` around
the origin of `C (H - z)`. -/
theorem lintegral_capTail_similarityConfig (m : ℝ≥0∞) (r c : ℝ) (z : Plane) (H : GMSSpace) :
    ∫⁻ q, capTail m r (similarityConfig c z H, q, 0) ∂dyadicLaw =
      ∫⁻ q, capTail m (r / Real.exp c) (H, q, planeCoord.symm z) ∂dyadicLaw :=
  lintegral_dyadic_similarityConfig
    ((measurable_capTail_uncurry m).comp (measurable_const.prodMk measurable_id)) c z H fun _ h₁ h₂ => by
      have h := capTail_similarity m (isSimilar_similarityConfig c z H) h₁ h₂ (r / Real.exp c)
        (planeCoord.symm z)
      have hr : Real.exp c * (r / Real.exp c) = r := by field_simp [(Real.exp_pos c).ne']
      rw [smul_add_similarityOffset_self, hr] at h
      exact h

/-- At an exhausting system and an off-grid root, the far part is at most `1`. -/
theorem capTail_le_one (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {z : ℂ} (hz : IsOffGrid q.1 q.2.1 q.2.2 z) (ρ : ℝ) :
    capTail m ρ (H, q, z) ≤ 1 := by
  rw [← lintegral_averageKernel_right hm0 hmtop H hq hz]
  dsimp only [capTail]
  refine lintegral_mono fun w => ?_
  by_cases h : ((ρ, z), w) ∈ farSet
  · rw [indicator_of_mem h, mul_one]
  · rw [indicator_of_notMem h, mul_zero]
    exact zero_le

/-- At an exhausting system and an off-grid root, the far part vanishes beyond a finite radius. -/
theorem eventually_capTail_eq_zero (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) {z : ℂ} (hz : IsOffGrid q.1 q.2.1 q.2.2 z) :
    ∀ᶠ r : ℕ in atTop, capTail m r (H, q, z) = 0 := by
  obtain ⟨j, -, hK⟩ := exists_averageKernel_eq hm0 hmtop H hq hz
  obtain ⟨R, hR⟩ :=
    (isCompact_squareAt (s := q.1) (o₁ := q.2.1) (o₂ := q.2.2) j z).isBounded.subset_closedBall z
  filter_upwards [eventually_gt_atTop ⌈R⌉₊] with r hr
  have hRr : R < r := (Nat.le_ceil R).trans_lt (by exact_mod_cast hr)
  dsimp only [capTail]
  refine (lintegral_congr fun w => ?_).trans lintegral_zero
  show averageKernel m (H, (q, z), w) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) (((r : ℝ), z), w) = 0
  rw [hK]
  by_cases hw : w ∈ squareAt q.1 q.2.1 q.2.2 j z
  · have hle : ‖w - z‖ ≤ R := by
      have h := hR hw
      rwa [Metric.mem_closedBall, dist_eq_norm] at h
    have hnot : (((r : ℝ), z), w) ∉ farSet := fun h => lt_irrefl _ ((hle.trans_lt hRr).trans h)
    rw [indicator_of_notMem hnot, mul_zero]
  · rw [indicator_of_notMem hw, mul_zero, zero_mul]

/-! ### The leak through the boundary of a window -/

theorem measurable_indicator_of_graph {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] {A : β → Set γ}
    (hA : MeasurableSet {x : β × γ | x.2 ∈ A x.1}) :
    Measurable fun x : β × γ => (A x.1).indicator (fun _ => (1 : ℝ≥0∞)) x.2 := by
  have h : (fun x : β × γ => (A x.1).indicator (fun _ => (1 : ℝ≥0∞)) x.2) =
      {x : β × γ | x.2 ∈ A x.1}.indicator (fun _ => 1) := by
    funext x
    by_cases hx : x.2 ∈ A x.1
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ {x : β × γ | x.2 ∈ A x.1} from hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ {x : β × γ | x.2 ∈ A x.1} from hx)]
  rw [h]
  exact measurable_const.indicator hA

theorem inv_mul_mul_cancel {v x : ℝ≥0∞} (h0 : v ≠ 0) (ht : v ≠ ∞) : v⁻¹ * (x * v) = x := by
  rw [mul_comm x v, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- **The leak through the boundary**: at an exhausting system, the kernel mass leaving the square
`V = [a, a + ℓ] × [b, b + ℓ]` from a root `v ∈ V` is at most the far part of the capped square beyond `ρ(v)`, plus
`1` when `v` is within `ρ(v)` of the boundary of `V`. -/
theorem windowLeak_le (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H : GMSSpace) {q : DyadicCoord}
    (hq : IsExhaustingSystem q) (a b ℓ : ℝ) (ρ : ℂ → ℝ) :
    windowLeak m H q (cornerSquare a b ℓ) ≤ ∫⁻ v : ℂ, (cornerSquare a b ℓ).indicator (fun _ => (1 : ℝ≥0∞)) v *
      (capTail m (ρ v) (H, q, v) + {v | ¬ InnerMargin a b ℓ (ρ v) v}.indicator (fun _ => (1 : ℝ≥0∞)) v) := by
  unfold windowLeak
  refine lintegral_mono_ae ?_
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with v hv
  refine mul_le_mul_right ?_ _
  have hKv : Measurable fun w => averageKernel m (H, (q, v), w) :=
    (measurable_averageKernel m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hfm : Measurable fun w => averageKernel m (H, (q, v), w) *
      farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ v, v), w) :=
    hKv.mul ((measurable_const.indicator measurableSet_farSet).comp (measurable_const.prodMk measurable_id))
  calc ∫⁻ w, averageKernel m (H, (q, v), w) * (cornerSquare a b ℓ)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w
      ≤ ∫⁻ w, (averageKernel m (H, (q, v), w) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ v, v), w) +
          {v | ¬ InnerMargin a b ℓ (ρ v) v}.indicator (fun _ => (1 : ℝ≥0∞)) v *
            averageKernel m (H, (q, v), w)) := by
        refine lintegral_mono fun w => ?_
        by_cases hI : InnerMargin a b ℓ (ρ v) v
        · rw [indicator_of_notMem (show v ∉ {v | ¬ InnerMargin a b ℓ (ρ v) v} from not_not.2 hI), zero_mul,
            add_zero]
          by_cases hw : w ∈ cornerSquare a b ℓ
          · rw [indicator_of_notMem (show w ∉ (cornerSquare a b ℓ)ᶜ from not_not.2 hw), mul_zero]
            exact zero_le
          · have hfar : ((ρ v, v), w) ∈ farSet := not_le.1 fun h => hw (hI.mem_cornerSquare h)
            simp only [indicator_of_mem (show w ∈ (cornerSquare a b ℓ)ᶜ from hw), indicator_of_mem hfar,
              le_refl]
        · rw [indicator_of_mem (show v ∈ {v | ¬ InnerMargin a b ℓ (ρ v) v} from hI), one_mul]
          have h1 : averageKernel m (H, (q, v), w) * (cornerSquare a b ℓ)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) w ≤
              averageKernel m (H, (q, v), w) := by
            by_cases hw : w ∈ (cornerSquare a b ℓ)ᶜ
            · rw [indicator_of_mem hw, mul_one]
            · rw [indicator_of_notMem hw, mul_zero]
              exact zero_le
          exact h1.trans (self_le_add_left _ _)
    _ = (∫⁻ w, averageKernel m (H, (q, v), w) * farSet.indicator (fun _ => (1 : ℝ≥0∞)) ((ρ v, v), w)) +
          {v | ¬ InnerMargin a b ℓ (ρ v) v}.indicator (fun _ => (1 : ℝ≥0∞)) v *
            ∫⁻ w, averageKernel m (H, (q, v), w) := by
        rw [lintegral_add_left hfm, lintegral_const_mul _ hKv]
    _ = capTail m (ρ v) (H, q, v) + {v | ¬ InnerMargin a b ℓ (ρ v) v}.indicator (fun _ => (1 : ℝ≥0∞)) v := by
        rw [lintegral_averageKernel_right hm0 hmtop H hq hv, mul_one]
        rfl

/-- **The cell mass of the window seen from the rescaled configuration**: if `v ∈ V = [a, a + ℓ] × [b, b + ℓ]` and
`C ℓ < R`, `C = exp c`, the closed ball of radius `2R` around the origin of `C (H - v)` carries at least the cell
mass of `V` in `H`. -/
theorem cellMass_cornerSquare_le_similarityConfig {H : GMSSpace} {c a b ℓ R : ℝ} {v : ℂ}
    (hv : v ∈ cornerSquare a b ℓ) (hR : Real.exp c * ℓ < R) :
    cellMass volume (complexCells H.1) (cornerSquare a b ℓ) ≤
      cellMass volume (complexCells (similarityConfig c (planeCoord v) H).1) (Metric.closedBall 0 (2 * R)) := by
  have hs := Real.exp_pos c
  rw [← cellMass_complexCells_similarity_image (H := H.1) (Real.exp c) (planeCoord v) hs (cornerSquare a b ℓ)]
  refine cellMass_mono volume _ ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h0 : Real.exp c • v + similarityOffset (Real.exp c) (planeCoord v) = 0 := by
    have h := smul_add_similarityOffset_self (Real.exp c) (planeCoord v)
    rwa [LinearIsometryEquiv.symm_apply_apply] at h
  have hwv : ‖w - v‖ ≤ 2 * ℓ := by
    obtain ⟨h1, h2, h3, h4⟩ := hw
    obtain ⟨g1, g2, g3, g4⟩ := hv
    have hre : |(w - v).re| ≤ ℓ := by
      rw [Complex.sub_re]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have him : |(w - v).im| ≤ ℓ := by
      rw [Complex.sub_im]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    linarith [Complex.norm_le_abs_re_add_abs_im (w - v)]
  calc ‖Real.exp c • w + similarityOffset (Real.exp c) (planeCoord v)‖
      = ‖Real.exp c • w + similarityOffset (Real.exp c) (planeCoord v) -
          (Real.exp c • v + similarityOffset (Real.exp c) (planeCoord v))‖ := by rw [h0, sub_zero]
    _ = Real.exp c * ‖w - v‖ := by
        rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    _ ≤ Real.exp c * (2 * ℓ) := mul_le_mul_of_nonneg_left hwv hs.le
    _ ≤ 2 * R := by nlinarith

/-- From `B(0, r + 1) ⊆ [a, a + ℓ] × [b, b + ℓ]` (in the plane), the origin satisfies the margin condition at `r`. -/
theorem innerMargin_zero_of_ball_subset {a b ℓ : ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : Metric.ball (0 : Plane) (r + 1) ⊆ planeSquare a b ℓ) : InnerMargin a b ℓ r 0 := by
  have hmem : ∀ x : ℂ, ‖x‖ = r → x.re ∈ Icc a (a + ℓ) ∧ x.im ∈ Icc b (b + ℓ) := by
    intro x hx
    have hb : planeCoord x ∈ Metric.ball (0 : Plane) (r + 1) := by
      rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, hx]
      linarith
    exact h hb
  have h1 := hmem (r : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr])
  have h2 := hmem (-(r : ℂ)) (by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr])
  have h3 := hmem ((r : ℂ) * Complex.I)
    (by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr])
  have h4 := hmem (-((r : ℂ) * Complex.I))
    (by rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr])
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    neg_zero, mem_Icc] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith [h1.1.2, h2.1.1, h3.2.2, h4.2.1]

/-- The margin indicator at a root `v` of the window is dominated by the four events of the error bound: `v` is
within `δ ℓ` of the boundary, the window misses the ball of radius `r'`, the cell mass of that ball is below `k`,
or the ball of radius `2 r / δ` of the rescaled configuration has cell mass at least `k`. -/
theorem margin_indicator_le {H : GMSSpace} {a b ℓ cc r δ : ℝ} (hδ : 0 < δ) {r' k : ℕ} {v : ℂ}
    (hv : v ∈ cornerSquare a b ℓ) {ρ : ℂ → ℝ} (hρ : ρ v = r / Real.exp cc) {x : ℝ≥0∞}
    (hB : ¬ InnerMargin a b ℓ r' 0 → 1 ≤ x)
    (hC : cellMass volume (complexCells H.1) (Metric.closedBall 0 r') < k → 1 ≤ x) :
    {v : ℂ | ¬ InnerMargin a b ℓ (ρ v) v}.indicator (fun _ => (1 : ℝ≥0∞)) v ≤
      {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1) (Metric.closedBall 0 (2 * (r / δ)))}.indicator
          (fun _ => (1 : ℝ≥0∞)) (similarityConfig cc (planeCoord v) H) +
        ({v : ℂ | ¬ InnerMargin a b ℓ (δ * ℓ) v}.indicator (fun _ => (1 : ℝ≥0∞)) v + x) := by
  by_cases hI : InnerMargin a b ℓ (ρ v) v
  · rw [indicator_of_notMem (show v ∉ {v : ℂ | ¬ InnerMargin a b ℓ (ρ v) v} from not_not.2 hI)]
    exact zero_le
  rw [indicator_of_mem (show v ∈ {v : ℂ | ¬ InnerMargin a b ℓ (ρ v) v} from hI)]
  by_cases h1 : InnerMargin a b ℓ (δ * ℓ) v
  swap
  · rw [indicator_of_mem (show v ∈ {v : ℂ | ¬ InnerMargin a b ℓ (δ * ℓ) v} from h1)]
    exact (self_le_add_right 1 x).trans (self_le_add_left _ _)
  by_cases h2 : InnerMargin a b ℓ r' 0
  swap
  · exact (hB h2).trans ((self_le_add_left _ _).trans (self_le_add_left _ _))
  by_cases h3 : cellMass volume (complexCells H.1) (Metric.closedBall 0 r') < k
  · exact (hC h3).trans ((self_le_add_left _ _).trans (self_le_add_left _ _))
  have hlt : δ * ℓ < ρ v := not_le.1 fun h => hI (h1.mono h)
  rw [hρ, lt_div_iff₀ (Real.exp_pos cc)] at hlt
  have hR : Real.exp cc * ℓ < r / δ := by
    rw [lt_div_iff₀ hδ]
    calc Real.exp cc * ℓ * δ = δ * ℓ * Real.exp cc := by ring
      _ < r := hlt
  have hsub : Metric.closedBall (0 : ℂ) r' ⊆ cornerSquare a b ℓ := fun _ hw => h2.mem_cornerSquare (by
    rw [sub_zero]
    rwa [Metric.mem_closedBall, dist_zero_right] at hw)
  have hk : (k : ℝ≥0∞) ≤ cellMass volume (complexCells (similarityConfig cc (planeCoord v) H).1)
      (Metric.closedBall 0 (2 * (r / δ))) :=
    (not_lt.1 h3).trans ((cellMass_mono volume _ hsub).trans (cellMass_cornerSquare_le_similarityConfig hv hR))
  rw [indicator_of_mem (show similarityConfig cc (planeCoord v) H ∈ {H' : GMSSpace | (k : ℝ≥0∞) ≤
    cellMass volume (complexCells H'.1) (Metric.closedBall 0 (2 * (r / δ)))} from hk)]
  exact self_le_add_right _ _

/-! ### The exact rerooting -/

theorem measurable_cornerSquare_indicator_prod {β : Type*} [MeasurableSpace β] {a b ℓ : β → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hl : Measurable ℓ) :
    Measurable fun x : β × ℂ => (cornerSquare (a x.1) (b x.1) (ℓ x.1)).indicator (fun _ => (1 : ℝ≥0∞)) x.2 :=
  measurable_indicator_of_graph (A := fun y => cornerSquare (a y) (b y) (ℓ y))
    (measurableSet_cornerSquare_graph.preimage
      (((ha.comp measurable_fst).prodMk ((hb.comp measurable_fst).prodMk (hl.comp measurable_fst))).prodMk
        measurable_snd))

theorem measurable_inv_volume_cornerSquare {β : Type*} [MeasurableSpace β] (a b : β → ℝ) {ℓ : β → ℝ}
    (hl : Measurable ℓ) : Measurable fun x => (volume (cornerSquare (a x) (b x) (ℓ x)))⁻¹ := by
  simp_rw [volume_cornerSquare]
  exact ((ENNReal.measurable_ofReal.comp hl).mul (ENNReal.measurable_ofReal.comp hl)).inv

/-- The exact identity at every level, in test-function form (the last clause of `ExactSquareRerooting`). -/
def ExactIdentity {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → GMSSpace) (a b ℓ : ℕ → Ω → ℝ)
    (c : ℕ → Ω × Plane → ℝ) (μ : Measure GMSSpace) : Prop :=
  ∀ n (F : GMSSpace → ℝ≥0∞), Measurable F →
    ∫⁻ ω, (⨍⁻ z in planeSquare (a n ω) (b n ω) (ℓ n ω), F (similarityConfig (c n (ω, z)) z (H ω)) ∂volume) ∂P =
      ∫⁻ H', F H' ∂μ

/-- The mean leak through the boundary of the window. -/
def windowLeakMean {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → GMSSpace) (a b ℓ : Ω → ℝ)
    (m : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (volume (cornerSquare (a ω) (b ω) (ℓ ω)))⁻¹ *
    ∫⁻ q, windowLeak m (H ω) q (cornerSquare (a ω) (b ω) (ℓ ω)) ∂dyadicLaw ∂P

/-- The error bound for the mean leak. -/
def errorBound {Ω : Type} [MeasurableSpace Ω] (μ : Measure GMSSpace) (P : Measure Ω) (H : Ω → GMSSpace)
    (a b ℓ : Ω → ℝ) (m : ℝ≥0∞) (r δ : ℝ) (k r' : ℕ) : ℝ≥0∞ :=
  (∫⁻ H', ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw ∂μ +
      μ {H' | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1) (Metric.closedBall 0 (2 * (r / δ)))}) +
    (ENNReal.ofReal (4 * δ) + (P {ω | ¬ InnerMargin (a ω) (b ω) (ℓ ω) r' 0} +
      P {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k}))

section Exact

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : Ω → GMSSpace} {a b ℓ : ℕ → Ω → ℝ}
  {c : ℕ → Ω × Plane → ℝ} {μ : Measure GMSSpace}

/-- The exact identity read in the coordinates `ℂ`. -/
theorem exact_complex (hexact : ExactIdentity P H a b ℓ c μ) (n : ℕ) {F : GMSSpace → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, (volume (cornerSquare (a n ω) (b n ω) (ℓ n ω)))⁻¹ *
        ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
          F (similarityConfig (c n (ω, planeCoord v)) (planeCoord v) (H ω)) ∂volume ∂P = ∫⁻ H', F H' ∂μ := by
  rw [← hexact n F hF]
  refine lintegral_congr fun ω => ?_
  rw [setLAverage_planeSquare_eq]

/-- The law of the rerooted configuration is a probability measure. -/
theorem isProbabilityMeasure_of_exactIdentity (hexact : ExactIdentity P H a b ℓ c μ) [IsProbabilityMeasure P]
    (hℓ : ∀ n ω, 0 < ℓ n ω) : IsProbabilityMeasure μ := by
  have h := exact_complex hexact 0 (F := fun _ => (1 : ℝ≥0∞)) measurable_const
  have hone : ∀ ω, (volume (cornerSquare (a 0 ω) (b 0 ω) (ℓ 0 ω)))⁻¹ *
      ∫⁻ v : ℂ, (cornerSquare (a 0 ω) (b 0 ω) (ℓ 0 ω)).indicator (fun _ => (1 : ℝ≥0∞)) v * 1 = 1 := by
    intro ω
    simp_rw [mul_one]
    rw [lintegral_indicator_const (measurableSet_cornerSquare _ _ _), one_mul]
    exact ENNReal.inv_mul_cancel (volume_cornerSquare_ne_zero _ _ (hℓ 0 ω)) (volume_cornerSquare_ne_top _ _ _)
  rw [lintegral_congr hone] at h
  simp only [lintegral_const, measure_univ, one_mul] at h
  exact ⟨h.symm⟩

theorem measurable_window_lintegral {a b ℓ : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hl : Measurable ℓ) (hH : Measurable H) {F : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun ω => (volume (cornerSquare (a ω) (b ω) (ℓ ω)))⁻¹ *
      ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a ω) (b ω) (ℓ ω)).indicator (fun _ => (1 : ℝ≥0∞)) v * F (H ω, q, v)
        ∂volume ∂dyadicLaw := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  refine (measurable_inv_volume_cornerSquare a b hl).mul ?_
  have hf : Measurable fun x : (Ω × DyadicCoord) × ℂ =>
      (cornerSquare (a x.1.1) (b x.1.1) (ℓ x.1.1)).indicator (fun _ => (1 : ℝ≥0∞)) x.2 *
        F (H x.1.1, x.1.2, x.2) :=
    (measurable_cornerSquare_indicator_prod (ha.comp measurable_fst) (hb.comp measurable_fst)
      (hl.comp measurable_fst)).mul
      (hF.comp ((hH.comp measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd)))
  exact (hf.lintegral_prod_right' (ν := volume)).lintegral_prod_right' (ν := dyadicLaw)

/-- **The window identity** (exact rerooting and the invariance of the uniform dyadic system, arXiv:1807.07515,
Lemma 2.1): for a measurable jointly invariant `F ≥ 0`, at every level `n`, `E_μ ∫ F(H, D, 0) dD` is the average
over the root `v ∈ U_n` of `E ∫ F(H, D, v) dD`. -/
theorem lintegral_eq_lintegral_window (hexact : ExactIdentity P H a b ℓ c μ) {F : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hF : Measurable F) (hinv : IsJointlyInvariant F) (n : ℕ) :
    ∫⁻ H', ∫⁻ q, F (H', q, 0) ∂dyadicLaw ∂μ =
      ∫⁻ ω, (volume (cornerSquare (a n ω) (b n ω) (ℓ n ω)))⁻¹ *
        ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v * F (H ω, q, v)
          ∂volume ∂dyadicLaw ∂P := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hΨ : Measurable fun H' : GMSSpace => ∫⁻ q, F (H', q, 0) ∂dyadicLaw :=
    Measurable.lintegral_prod_right' (f := fun x : GMSSpace × DyadicCoord => F (x.1, x.2, 0))
      (hF.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  rw [← exact_complex hexact n hΨ]
  refine lintegral_congr fun ω => ?_
  congr 1
  have hm : Measurable fun x : ℂ × DyadicCoord =>
      (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) x.1 * F (H ω, x.2, x.1) :=
    ((measurable_const.indicator (measurableSet_cornerSquare _ _ _)).comp measurable_fst).mul
      (hF.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
  rw [← lintegral_lintegral_swap (f := fun v q =>
    (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v * F (H ω, q, v)) hm.aemeasurable]
  refine lintegral_congr fun v => ?_
  have hFv : Measurable fun q : DyadicCoord => F (H ω, q, v) :=
    hF.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  rw [lintegral_dyadic_similarityConfig_of_invariant hF hinv, LinearIsometryEquiv.symm_apply_apply,
    lintegral_const_mul _ hFv]

end Exact

section ExactBounds

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : Ω → GMSSpace} {a b ℓ : ℕ → Ω → ℝ}
  {c : ℕ → Ω × Plane → ℝ} {μ : Measure GMSSpace}

theorem isJointlyInvariant_kernelAverage {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : IsJointlyInvariant G) : IsJointlyInvariant (kernelAverage m G) :=
  fun s u hs H H' hHH' q h₁ h₂ w =>
    kernelAverage_similarity m hG hHH' h₁ h₂ (fun z => hinv s u hs H H' hHH' q h₁ h₂ z) w

theorem measurable_lintegral_window_section {V : Set ℂ} (hV : MeasurableSet V) (H₁ : GMSSpace)
    {F : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun q : DyadicCoord => ∫⁻ v, V.indicator (fun _ => (1 : ℝ≥0∞)) v * F (H₁, q, v) :=
  Measurable.lintegral_prod_right' (f := fun x : DyadicCoord × ℂ =>
      V.indicator (fun _ => (1 : ℝ≥0∞)) x.2 * F (H₁, x.1, x.2))
    (((measurable_const.indicator hV).comp measurable_snd).mul
      (hF.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))))

/-- **The comparison at a level**: the expected capped-square average exceeds the expected value of a bounded test
function by at most `sup G` times the mean leak through the boundary of the window, and conversely. -/
theorem lintegral_kernelAverage_le_add_and (hexact : ExactIdentity P H a b ℓ c μ) (hH : Measurable H)
    (habℓ : ∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n)) (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G) (hinv : IsJointlyInvariant G) {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hGM : ∀ p, G p ≤ M) (n : ℕ) :
    (∫⁻ H', ∫⁻ q, kernelAverage m G (H', q, 0) ∂dyadicLaw ∂μ ≤
        ∫⁻ H', ∫⁻ q, G (H', q, 0) ∂dyadicLaw ∂μ + M * windowLeakMean P H (a n) (b n) (ℓ n) m) ∧
      (∫⁻ H', ∫⁻ q, G (H', q, 0) ∂dyadicLaw ∂μ ≤
        ∫⁻ H', ∫⁻ q, kernelAverage m G (H', q, 0) ∂dyadicLaw ∂μ + M * windowLeakMean P H (a n) (b n) (ℓ n) m) := by
  have hGK := measurable_kernelAverage m hG
  rw [lintegral_eq_lintegral_window hexact hGK (isJointlyInvariant_kernelAverage hG hinv) n,
    lintegral_eq_lintegral_window hexact hG hinv n, windowLeakMean, ← lintegral_const_mul' _ _ hM]
  constructor
  · rw [← lintegral_add_left (measurable_window_lintegral (habℓ n).1 (habℓ n).2.1 (habℓ n).2.2 hH hG)]
    refine lintegral_mono fun ω => ?_
    have hq : ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
          kernelAverage m G (H ω, q, v) ∂volume ∂dyadicLaw ≤
        ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
          G (H ω, q, v) ∂volume ∂dyadicLaw +
          M * ∫⁻ q, windowLeak m (H ω) q (cornerSquare (a n ω) (b n ω) (ℓ n ω)) ∂dyadicLaw := by
      rw [← lintegral_const_mul' _ _ hM,
        ← lintegral_add_left (measurable_lintegral_window_section (measurableSet_cornerSquare _ _ _) _ hG)]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_isExhaustingSystem] with q hq
      exact lintegral_window_le_add hm0 hmtop (H ω) hq (measurableSet_cornerSquare _ _ _) hG hGM
    calc _ ≤ (volume (cornerSquare (a n ω) (b n ω) (ℓ n ω)))⁻¹ *
          (∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
            G (H ω, q, v) ∂volume ∂dyadicLaw +
          M * ∫⁻ q, windowLeak m (H ω) q (cornerSquare (a n ω) (b n ω) (ℓ n ω)) ∂dyadicLaw) :=
          mul_le_mul_right hq _
      _ = _ := by ring
  · rw [← lintegral_add_left (measurable_window_lintegral (habℓ n).1 (habℓ n).2.1 (habℓ n).2.2 hH hGK)]
    refine lintegral_mono fun ω => ?_
    have hq : ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
          G (H ω, q, v) ∂volume ∂dyadicLaw ≤
        ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
          kernelAverage m G (H ω, q, v) ∂volume ∂dyadicLaw +
          M * ∫⁻ q, windowLeak m (H ω) q (cornerSquare (a n ω) (b n ω) (ℓ n ω)) ∂dyadicLaw := by
      rw [← lintegral_const_mul' _ _ hM,
        ← lintegral_add_left (measurable_lintegral_window_section (measurableSet_cornerSquare _ _ _) _ hGK)]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_isExhaustingSystem] with q hq
      exact lintegral_window_le_add' hm0 hmtop (H ω) hq (measurableSet_cornerSquare _ _ _) hG hGM
    calc _ ≤ (volume (cornerSquare (a n ω) (b n ω) (ℓ n ω)))⁻¹ *
          (∫⁻ q, ∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
            kernelAverage m G (H ω, q, v) ∂volume ∂dyadicLaw +
          M * ∫⁻ q, windowLeak m (H ω) q (cornerSquare (a n ω) (b n ω) (ℓ n ω)) ∂dyadicLaw) :=
          mul_le_mul_right hq _
      _ = _ := by ring

end ExactBounds

section LeakBound

/-- The mean leak through the boundary of `V = [a, a + ℓ] × [b, b + ℓ]`, root by root: the far part of the capped
square beyond `r / exp (cf v)` plus the margin event at `v`. -/
theorem lintegral_windowLeak_le (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H₁ : GMSSpace) (a₀ b₀ ℓ₀ : ℝ) {cf : ℂ → ℝ}
    (hcf : Measurable cf) (r : ℝ) :
    ∫⁻ q, windowLeak m H₁ q (cornerSquare a₀ b₀ ℓ₀) ∂dyadicLaw ≤
      ∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
        (∫⁻ q, capTail m (r / Real.exp (cf v)) (H₁, q, v) ∂dyadicLaw +
          {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) v) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hVm : MeasurableSet (cornerSquare a₀ b₀ ℓ₀) := measurableSet_cornerSquare _ _ _
  have hρm : Measurable fun v : ℂ => r / Real.exp (cf v) :=
    measurable_const.div (Real.measurable_exp.comp hcf)
  have hIm : MeasurableSet {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v} :=
    (measurableSet_innerMargin_graph.preimage (f := fun v : ℂ => ((a₀, b₀, ℓ₀, r / Real.exp (cf v)), v))
      ((measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk hρm))).prodMk
        measurable_id)).compl
  have hcapm : Measurable fun y : DyadicCoord × ℂ => capTail m (r / Real.exp (cf y.2)) (H₁, y.1, y.2) :=
    measurable_capTail_section m H₁ hρm
  have hVi : Measurable fun y : DyadicCoord × ℂ => (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) y.2 :=
    (measurable_const.indicator hVm).comp measurable_snd
  have hIi : Measurable fun y : DyadicCoord × ℂ =>
      {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) y.2 :=
    (measurable_const.indicator hIm).comp measurable_snd
  have hm2 : Measurable fun y : DyadicCoord × ℂ =>
      (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) y.2 *
        (capTail m (r / Real.exp (cf y.2)) (H₁, y.1, y.2) +
          {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) y.2) :=
    hVi.mul (hcapm.add hIi)
  calc ∫⁻ q, windowLeak m H₁ q (cornerSquare a₀ b₀ ℓ₀) ∂dyadicLaw
      ≤ ∫⁻ q, ∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          (capTail m (r / Real.exp (cf v)) (H₁, q, v) +
            {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) v)
            ∂volume ∂dyadicLaw :=
        lintegral_mono_ae (ae_isExhaustingSystem.mono fun q hq =>
          windowLeak_le hm0 hmtop H₁ hq a₀ b₀ ℓ₀ (fun v => r / Real.exp (cf v)))
    _ = ∫⁻ v : ℂ, ∫⁻ q, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          (capTail m (r / Real.exp (cf v)) (H₁, q, v) +
            {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) v)
            ∂dyadicLaw ∂volume :=
        lintegral_lintegral_swap hm2.aemeasurable
    _ = _ := by
        refine lintegral_congr fun v => ?_
        have hcq' : Measurable fun q : DyadicCoord => capTail m (r / Real.exp (cf v)) (H₁, q, v) :=
          (measurable_capTail m _).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
        have hcq : Measurable fun q : DyadicCoord => capTail m (r / Real.exp (cf v)) (H₁, q, v) +
            {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) v :=
          hcq'.add_const _
        rw [lintegral_const_mul _ hcq, lintegral_add_left hcq', lintegral_const, measure_univ, mul_one]

/-- The margin events at a root `v` of the window, after the far part is read in the rescaled configuration. -/
theorem margin_root_le (H₁ : GMSSpace) {a₀ b₀ ℓ₀ : ℝ} (cf : ℂ → ℝ) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (k r' : ℕ)
    {x : ℝ≥0∞} (hB : ¬ InnerMargin a₀ b₀ ℓ₀ r' 0 → 1 ≤ x)
    (hC : cellMass volume (complexCells H₁.1) (Metric.closedBall 0 r') < k → 1 ≤ x) (v : ℂ) :
    (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
      (∫⁻ q, capTail m (r / Real.exp (cf v)) (H₁, q, v) ∂dyadicLaw +
        {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (r / Real.exp (cf v)) v}.indicator (fun _ => (1 : ℝ≥0∞)) v) ≤
      (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          (∫⁻ q, capTail m r (similarityConfig (cf v) (planeCoord v) H₁, q, 0) ∂dyadicLaw +
            {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
              (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞))
              (similarityConfig (cf v) (planeCoord v) H₁)) +
        ((cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
            {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v +
          (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * x) := by
  by_cases hv : v ∈ cornerSquare a₀ b₀ ℓ₀
  · simp only [indicator_of_mem hv, one_mul]
    have hcap : ∫⁻ q, capTail m (r / Real.exp (cf v)) (H₁, q, v) ∂dyadicLaw =
        ∫⁻ q, capTail m r (similarityConfig (cf v) (planeCoord v) H₁, q, 0) ∂dyadicLaw := by
      rw [lintegral_capTail_similarityConfig, LinearIsometryEquiv.symm_apply_apply]
    have hmar := margin_indicator_le (H := H₁) (cc := cf v) (r := r) hδ (r' := r') (k := k) hv
      (ρ := fun v => r / Real.exp (cf v)) rfl hB hC
    rw [hcap]
    calc _ ≤ ∫⁻ q, capTail m r (similarityConfig (cf v) (planeCoord v) H₁, q, 0) ∂dyadicLaw +
          ({H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
              (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞))
              (similarityConfig (cf v) (planeCoord v) H₁) +
            ({v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v + x)) :=
          add_le_add le_rfl hmar
      _ = _ := by ring
  · simp only [indicator_of_notMem hv, zero_mul, add_zero, le_refl]

/-- Integrating the margin events over the window. -/
theorem window_average_le {a₀ b₀ ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {δ : ℝ} (hδ : 0 < δ) (x : ℝ≥0∞) (A : ℂ → ℝ≥0∞) :
    (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ * ∫⁻ v : ℂ,
        ((cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * A v +
          ((cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
              {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v +
            (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * x)) ≤
      (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ *
          (∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * A v) +
        (ENNReal.ofReal (4 * δ) + x) := by
  have hVm : MeasurableSet (cornerSquare a₀ b₀ ℓ₀) := measurableSet_cornerSquare _ _ _
  have hV0 := volume_cornerSquare_ne_zero a₀ b₀ hℓ₀
  have hVt := volume_cornerSquare_ne_top a₀ b₀ ℓ₀
  have hJm : MeasurableSet {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v} :=
    (measurableSet_innerMargin_graph.preimage (f := fun v : ℂ => ((a₀, b₀, ℓ₀, δ * ℓ₀), v))
      (measurable_const.prodMk measurable_id)).compl
  have hVi : Measurable fun v : ℂ => (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v :=
    measurable_const.indicator hVm
  have hJi : Measurable fun v : ℂ => {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v :=
    measurable_const.indicator hJm
  have hBm : Measurable fun v : ℂ => (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
      {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v := hVi.mul hJi
  have hCm : Measurable fun v : ℂ => (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * x :=
    hVi.mul_const x
  have hBCm : Measurable fun v : ℂ =>
      (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v +
        (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * x := hBm.add hCm
  have hJ : ∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
      {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v ≤
      ENNReal.ofReal (4 * δ) * volume (cornerSquare a₀ b₀ ℓ₀) := by
    have heq : (fun v : ℂ => (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
        {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v) =
        (cornerSquare a₀ b₀ ℓ₀ ∩ {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}).indicator (fun _ => 1) := by
      funext v
      by_cases hv : v ∈ cornerSquare a₀ b₀ ℓ₀
      · by_cases hw : v ∈ {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}
        · rw [indicator_of_mem hv, indicator_of_mem hw, indicator_of_mem (mem_inter hv hw), one_mul]
        · rw [indicator_of_mem hv, indicator_of_notMem hw, indicator_of_notMem (show v ∉ cornerSquare a₀ b₀ ℓ₀ ∩
            {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v} from fun h => hw h.2), mul_zero]
      · rw [indicator_of_notMem hv, indicator_of_notMem (show v ∉ cornerSquare a₀ b₀ ℓ₀ ∩
          {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v} from fun h => hv h.1), zero_mul]
    rw [heq, lintegral_indicator_const (hVm.inter hJm), one_mul]
    exact volume_cornerSquare_diff_innerMargin_le a₀ b₀ hδ.le
  have hconst : ∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v * x =
      volume (cornerSquare a₀ b₀ ℓ₀) * x := by
    rw [lintegral_mul_const _ hVi, lintegral_indicator_const hVm, one_mul]
  rw [lintegral_add_right' _ hBCm.aemeasurable, lintegral_add_left hBm, hconst, mul_add, mul_add,
    mul_comm (volume (cornerSquare a₀ b₀ ℓ₀)) x, inv_mul_mul_cancel hV0 hVt]
  refine add_le_add le_rfl (add_le_add ?_ le_rfl)
  calc (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ * ∫⁻ v : ℂ,
        (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          {v : ℂ | ¬ InnerMargin a₀ b₀ ℓ₀ (δ * ℓ₀) v}.indicator (fun _ => (1 : ℝ≥0∞)) v
      ≤ (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ * (ENNReal.ofReal (4 * δ) * volume (cornerSquare a₀ b₀ ℓ₀)) :=
        mul_le_mul_right hJ _
    _ = ENNReal.ofReal (4 * δ) := inv_mul_mul_cancel hV0 hVt

/-- **The leak at one sample**: the mean leak through the boundary of the window `V = [a, a + ℓ] × [b, b + ℓ]` is at
most the window average of the far part beyond `r` of the capped square around the origin of the rescaled
configuration `exp (cf v) (H - v)`, plus the cell-mass event of the rescaled ball of radius `2 r / δ`, plus `4 δ`
and the window events collected in `x`. -/
theorem windowLeak_mean_le_pointwise (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (H₁ : GMSSpace) {a₀ b₀ ℓ₀ : ℝ}
    (hℓ₀ : 0 < ℓ₀) {cf : ℂ → ℝ} (hcf : Measurable cf) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (k r' : ℕ) {x : ℝ≥0∞}
    (hB : ¬ InnerMargin a₀ b₀ ℓ₀ r' 0 → 1 ≤ x)
    (hC : cellMass volume (complexCells H₁.1) (Metric.closedBall 0 r') < k → 1 ≤ x) :
    (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ * ∫⁻ q, windowLeak m H₁ q (cornerSquare a₀ b₀ ℓ₀) ∂dyadicLaw ≤
      (volume (cornerSquare a₀ b₀ ℓ₀))⁻¹ * (∫⁻ v : ℂ, (cornerSquare a₀ b₀ ℓ₀).indicator (fun _ => (1 : ℝ≥0∞)) v *
          (∫⁻ q, capTail m r (similarityConfig (cf v) (planeCoord v) H₁, q, 0) ∂dyadicLaw +
            {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
              (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞))
              (similarityConfig (cf v) (planeCoord v) H₁))) +
        (ENNReal.ofReal (4 * δ) + x) :=
  (mul_le_mul_right ((lintegral_windowLeak_le hm0 hmtop H₁ a₀ b₀ ℓ₀ hcf r).trans
    (lintegral_mono (margin_root_le H₁ cf r hδ k r' hB hC))) _).trans (window_average_le hℓ₀ hδ x _)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : Ω → GMSSpace} {a b ℓ : ℕ → Ω → ℝ}
  {c : ℕ → Ω × Plane → ℝ} {μ : Measure GMSSpace}

/-- **The mean leak is at most the error bound** at every level, for every far radius `r`, margin fraction
`δ > 0`, cell-mass threshold `k` and window radius `r'`. -/
theorem windowLeakMean_le_errorBound (hexact : ExactIdentity P H a b ℓ c μ) [IsProbabilityMeasure P]
    (hH : Measurable H) (habℓ : ∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n))
    (hℓ : ∀ n ω, 0 < ℓ n ω) (hc : ∀ n, Measurable (c n)) (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (n : ℕ) {r δ : ℝ}
    (hδ : 0 < δ) (k r' : ℕ) :
    windowLeakMean P H (a n) (b n) (ℓ n) m ≤ errorBound μ P H (a n) (b n) (ℓ n) m r δ k r' := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hKm : MeasurableSet {H' : GMSSpace | (k : ℝ≥0∞) ≤
      cellMass volume (complexCells H'.1) (Metric.closedBall 0 (2 * (r / δ)))} :=
    measurableSet_le measurable_const (measurable_cellMass_complexCells measurableSet_closedBall)
  have hBm : MeasurableSet {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0} :=
    (measurableSet_innerMargin_graph.preimage (f := fun ω : Ω => ((a n ω, b n ω, ℓ n ω, (r' : ℝ)), (0 : ℂ)))
      (((habℓ n).1.prodMk ((habℓ n).2.1.prodMk ((habℓ n).2.2.prodMk measurable_const))).prodMk
        measurable_const)).compl
  have hCm : MeasurableSet {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k} :=
    measurableSet_lt ((measurable_cellMass_complexCells measurableSet_closedBall).comp hH) measurable_const
  have hΨ : Measurable fun H' : GMSSpace => ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw :=
    Measurable.lintegral_prod_right' (f := fun y : GMSSpace × DyadicCoord => capTail m r (y.1, y.2, 0))
      ((measurable_capTail m r).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  have hF'm : Measurable fun H' : GMSSpace => ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw +
      {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
        (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞)) H' := by
    have hKi : Measurable fun H' : GMSSpace => {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume
        (complexCells H'.1) (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞)) H' :=
      measurable_const.indicator hKm
    exact hΨ.add hKi
  have hgm : Measurable fun ω => ENNReal.ofReal (4 * δ) +
      ({ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω +
        {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω) := by
    have hBi : Measurable fun ω =>
        {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator hBm
    have hCi : Measurable fun ω =>
        {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator hCm
    exact (hBi.add hCi).const_add _
  calc windowLeakMean P H (a n) (b n) (ℓ n) m
      ≤ ∫⁻ ω, ((volume (cornerSquare (a n ω) (b n ω) (ℓ n ω)))⁻¹ *
          (∫⁻ v : ℂ, (cornerSquare (a n ω) (b n ω) (ℓ n ω)).indicator (fun _ => (1 : ℝ≥0∞)) v *
            (∫⁻ q, capTail m r (similarityConfig (c n (ω, planeCoord v)) (planeCoord v) (H ω), q, 0)
                ∂dyadicLaw +
              {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
                (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞))
                (similarityConfig (c n (ω, planeCoord v)) (planeCoord v) (H ω)))) +
          (ENNReal.ofReal (4 * δ) +
            ({ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω +
              {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k}.indicator
                (fun _ => (1 : ℝ≥0∞)) ω))) ∂P := by
        unfold windowLeakMean
        refine lintegral_mono fun ω => ?_
        exact windowLeak_mean_le_pointwise hm0 hmtop (H ω) (hℓ n ω) (cf := fun v => c n (ω, planeCoord v))
          ((hc n).comp (measurable_const.prodMk planeCoord.continuous.measurable)) r hδ k r'
          (fun h => by
            rw [indicator_of_mem (show ω ∈ {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0} from h)]
            exact self_le_add_right _ _)
          (fun h => by
            rw [indicator_of_mem (show ω ∈ {ω | cellMass volume (complexCells (H ω).1)
              (Metric.closedBall 0 r') < k} from h)]
            exact self_le_add_left _ _)
    _ = (∫⁻ H', (∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw +
          {H' : GMSSpace | (k : ℝ≥0∞) ≤ cellMass volume (complexCells H'.1)
            (Metric.closedBall 0 (2 * (r / δ)))}.indicator (fun _ => (1 : ℝ≥0∞)) H') ∂μ) +
        ∫⁻ ω, (ENNReal.ofReal (4 * δ) +
          ({ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω +
            {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω)) ∂P := by
        rw [lintegral_add_right' _ hgm.aemeasurable, exact_complex hexact n hF'm]
    _ = errorBound μ P H (a n) (b n) (ℓ n) m r δ k r' := by
        rw [lintegral_add_left hΨ, lintegral_indicator_const hKm, one_mul, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one, lintegral_add_left (measurable_const.indicator hBm),
          lintegral_indicator_const hBm, lintegral_indicator_const hCm, one_mul, one_mul]
        rfl

end LeakBound

/-! ### The error bound tends to zero -/

/-- The expected far part of the capped square at the origin beyond `r` tends to `0`. -/
theorem tendsto_lintegral_capTail (hm0 : m ≠ 0) (hmtop : m ≠ ∞) (μ : Measure GMSSpace) [IsFiniteMeasure μ] :
    Tendsto (fun r : ℕ => ∫⁻ H', ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw ∂μ) atTop (𝓝 0) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hmeasq : ∀ (r : ℕ) (H' : GMSSpace), Measurable fun q : DyadicCoord => capTail m r (H', q, 0) :=
    fun r _ => (measurable_capTail m r).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hmeas : ∀ r : ℕ, Measurable fun H' : GMSSpace => ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw := fun r =>
    Measurable.lintegral_prod_right' (f := fun x : GMSSpace × DyadicCoord => capTail m r (x.1, x.2, 0))
      ((measurable_capTail m r).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  have hle : ∀ (r : ℕ) (H' : GMSSpace), ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw ≤ 1 := by
    intro r H'
    calc ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw ≤ ∫⁻ _q, 1 ∂dyadicLaw := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_isExhaustingSystem, ae_isOffGrid_system 0] with q hq h0
          exact capTail_le_one hm0 hmtop H' hq h0 r
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have hinner : ∀ H' : GMSSpace,
      Tendsto (fun r : ℕ => ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw) atTop (𝓝 0) := by
    intro H'
    have h := tendsto_lintegral_of_dominated_convergence (μ := dyadicLaw)
      (F := fun (r : ℕ) q => capTail m r (H', q, 0)) (f := fun _ => 0) (fun _ => 1) (fun r => hmeasq r H')
      (fun r => by
        filter_upwards [ae_isExhaustingSystem, ae_isOffGrid_system 0] with q hq h0
        exact capTail_le_one hm0 hmtop H' hq h0 r)
      (by rw [lintegral_const, measure_univ, one_mul]; exact ENNReal.one_ne_top)
      (by
        filter_upwards [ae_isExhaustingSystem, ae_isOffGrid_system 0] with q hq h0
        exact tendsto_const_nhds.congr'
          ((eventually_capTail_eq_zero hm0 hmtop H' hq h0).mono fun r hr => hr.symm))
    rwa [lintegral_zero] at h
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun (r : ℕ) H' => ∫⁻ q, capTail m r (H', q, 0) ∂dyadicLaw) (f := fun _ => 0) (fun _ => 1) hmeas
    (fun r => Eventually.of_forall (hle r)) (by rw [lintegral_const, one_mul]; exact measure_ne_top μ _)
    (Eventually.of_forall hinner)
  rwa [lintegral_zero] at h

/-- The probability that the cell mass of a fixed ball is at least `k` tends to `0` as `k → ∞`. -/
theorem tendsto_measure_le_cellMass (μ : Measure GMSSpace) [IsFiniteMeasure μ] (R : ℝ) :
    Tendsto (fun k : ℕ => μ {H' : GMSSpace | (k : ℝ≥0∞) ≤
      cellMass volume (complexCells H'.1) (Metric.closedBall 0 R)}) atTop (𝓝 0) := by
  have hm : ∀ k : ℕ, MeasurableSet {H' : GMSSpace | (k : ℝ≥0∞) ≤
      cellMass volume (complexCells H'.1) (Metric.closedBall 0 R)} :=
    fun _ => measurableSet_le measurable_const (measurable_cellMass_complexCells measurableSet_closedBall)
  have hanti : Antitone fun k : ℕ => {H' : GMSSpace | (k : ℝ≥0∞) ≤
      cellMass volume (complexCells H'.1) (Metric.closedBall 0 R)} :=
    fun k k' hkk' H' hH' => by
      change (k' : ℝ≥0∞) ≤ _ at hH'
      change (k : ℝ≥0∞) ≤ _
      exact (Nat.cast_le.2 hkk').trans hH'
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hm k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  have hempty : (⋂ k : ℕ, {H' : GMSSpace | (k : ℝ≥0∞) ≤
      cellMass volume (complexCells H'.1) (Metric.closedBall 0 R)}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun H' hH' => ?_
    have hfin := cellMass_ne_top volume (complexCells H'.1) (locallyFinite_complexCells H'.2)
      (isCompact_closedBall (0 : ℂ) R)
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hfin
    exact absurd (mem_iInter.1 hH' k) (not_le.2 hk)
  rw [hempty, measure_empty] at h
  exact h

/-- The probability that the cell mass of the ball of radius `r'` is below `k` tends to `0` as `r' → ∞`. -/
theorem tendsto_measure_cellMass_lt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {H : Ω → GMSSpace} (hH : Measurable H) (k : ℕ) :
    Tendsto (fun r' : ℕ => P {ω | cellMass volume (complexCells (H ω).1) (Metric.closedBall 0 r') < k})
      atTop (𝓝 0) := by
  have hm : ∀ r' : ℕ, MeasurableSet {ω | cellMass volume (complexCells (H ω).1)
      (Metric.closedBall (0 : ℂ) r') < k} :=
    fun _ => measurableSet_lt ((measurable_cellMass_complexCells measurableSet_closedBall).comp hH)
      measurable_const
  have hanti : Antitone fun r' : ℕ => {ω | cellMass volume (complexCells (H ω).1)
      (Metric.closedBall (0 : ℂ) r') < k} :=
    fun r₁ r₂ h ω hω => by
      change cellMass volume (complexCells (H ω).1) (Metric.closedBall (0 : ℂ) r₂) < k at hω
      change cellMass volume (complexCells (H ω).1) (Metric.closedBall (0 : ℂ) r₁) < k
      exact lt_of_le_of_lt
        (cellMass_mono volume _ (Metric.closedBall_subset_closedBall (by exact_mod_cast h))) hω
  have h := tendsto_measure_iInter_atTop (μ := P) (fun r' => (hm r').nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ r' : ℕ, {ω | cellMass volume (complexCells (H ω).1)
      (Metric.closedBall (0 : ℂ) r') < k}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    have := infinite_of_iUnion_eq_univ (iUnion_complexCells (H ω).2) isCompact_complexCells
    have hexh : ⋃ j : ℤ, Metric.closedBall (0 : ℂ) j = univ := by
      refine eq_univ_of_forall fun w => mem_iUnion.2 ⟨⌈‖w‖⌉, ?_⟩
      rw [mem_closedBall_zero_iff]
      exact Int.le_ceil _
    have ht := tendsto_cellMass_atTop volume (complexCells (H ω).1)
      (C := fun j : ℤ => Metric.closedBall (0 : ℂ) j)
      (fun _ _ hij => Metric.closedBall_subset_closedBall (by exact_mod_cast hij)) hexh
      (volume_complexCells_ne_zero (H ω).2) (fun K => (isCompact_complexCells K).measure_lt_top.ne)
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (ht.eventually (lt_mem_nhds (ENNReal.natCast_ne_top k).lt_top))
    have hJk := hJ (J.toNat : ℤ) (Int.self_le_toNat J)
    have hω' := mem_iInter.1 hω J.toNat
    simp only [mem_ofPred_eq] at hω'
    simp only [Int.cast_natCast] at hJk
    exact absurd hJk (not_lt.2 hω'.le)
  rw [hempty, measure_empty] at h
  exact h

/-- The probability that the origin violates the margin condition at `r'` in the `n`-th window tends to `0`. -/
theorem tendsto_measure_not_innerMargin {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {a b ℓ : ℕ → Ω → ℝ} (habℓ : ∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n))
    (hexh : ∀ᵐ ω ∂P, ∀ r : ℝ, ∀ᶠ n in atTop,
      Metric.ball (0 : Plane) r ⊆ planeSquare (a n ω) (b n ω) (ℓ n ω)) (r' : ℕ) :
    Tendsto (fun n => P {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}) atTop (𝓝 0) := by
  have hm : ∀ n, MeasurableSet {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0} := fun n =>
    (measurableSet_innerMargin_graph.preimage (f := fun ω : Ω => ((a n ω, b n ω, ℓ n ω, (r' : ℝ)), (0 : ℂ)))
      (((habℓ n).1.prodMk ((habℓ n).2.1.prodMk ((habℓ n).2.2.prodMk measurable_const))).prodMk
        measurable_const)).compl
  have h := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun n ω => {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω)
    (f := fun _ => 0) (fun _ => 1) (fun n => measurable_const.indicator (hm n))
    (fun _ => Eventually.of_forall fun ω => Set.indicator_le (fun _ _ => le_rfl) ω)
    (by rw [lintegral_const, one_mul]; exact measure_ne_top P _)
    (by
      filter_upwards [hexh] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω ((r' : ℝ) + 1)] with n hn
      rw [indicator_of_notMem (show ω ∉ {ω | ¬ InnerMargin (a n ω) (b n ω) (ℓ n ω) r' 0} from
        not_not.2 (innerMargin_zero_of_ball_subset (Nat.cast_nonneg r') hn))])
  rw [lintegral_zero] at h
  exact h.congr fun n => by rw [lintegral_indicator_const (hm n), one_mul]

/-! ### Conclusion -/

theorem lintegral_lintegral_iSup {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite ν] {f : ℕ → α × β → ℝ≥0∞} (hf : ∀ N, Measurable (f N)) (hmono : Monotone f) :
    ∫⁻ x, ∫⁻ y, ⨆ N, f N (x, y) ∂ν ∂μ = ⨆ N, ∫⁻ x, ∫⁻ y, f N (x, y) ∂ν ∂μ := by
  have h1 : ∀ x, ∫⁻ y, ⨆ N, f N (x, y) ∂ν = ⨆ N, ∫⁻ y, f N (x, y) ∂ν := fun x =>
    lintegral_iSup (fun N => (hf N).comp (measurable_const.prodMk measurable_id)) (fun _ _ h y => hmono h (x, y))
  simp_rw [h1]
  exact lintegral_iSup (fun N => (hf N).lintegral_prod_right') (fun _ _ h x => lintegral_mono fun y => hmono h (x, y))

section Final

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : Ω → GMSSpace} {a b ℓ : ℕ → Ω → ℝ}
  {c : ℕ → Ω × Plane → ℝ} {μ : Measure GMSSpace}

/-- **The re-sampling identity for bounded test functions**: under the exact rerooting, the expected
capped-square average of a bounded measurable jointly invariant `G ≥ 0` is its expected value at the origin. -/
theorem lintegral_kernelAverage_eq_of_le (hexact : ExactIdentity P H a b ℓ c μ) [IsProbabilityMeasure P]
    (hH : Measurable H) (habℓ : ∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n))
    (hℓ : ∀ n ω, 0 < ℓ n ω)
    (hexh : ∀ᵐ ω ∂P, ∀ r : ℝ, ∀ᶠ n in atTop,
      Metric.ball (0 : Plane) r ⊆ planeSquare (a n ω) (b n ω) (ℓ n ω))
    (hc : ∀ n, Measurable (c n)) (hm0 : m ≠ 0) (hmtop : m ≠ ∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G) (hinv : IsJointlyInvariant G) {M : ℝ≥0∞} (hM : M ≠ ∞) (hGM : ∀ p, G p ≤ M) :
    ∫⁻ H', ∫⁻ q, kernelAverage m G (H', q, 0) ∂dyadicLaw ∂μ = ∫⁻ H', ∫⁻ q, G (H', q, 0) ∂dyadicLaw ∂μ := by
  have hμ := isProbabilityMeasure_of_exactIdentity hexact hℓ
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, windowLeakMean P H (a n) (b n) (ℓ n) m ≤
      (ENNReal.ofReal ε + ENNReal.ofReal ε) + (ENNReal.ofReal ε + (ENNReal.ofReal ε + ENNReal.ofReal ε)) := by
    intro ε hε
    have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
    obtain ⟨r, hr⟩ := ((tendsto_order.1 (tendsto_lintegral_capTail hm0 hmtop μ)).2 _ hε').exists
    have hδ : (0 : ℝ) < ε / 4 := by positivity
    obtain ⟨k, hk⟩ := ((tendsto_order.1 (tendsto_measure_le_cellMass μ (2 * ((r : ℝ) / (ε / 4))))).2 _
      hε').exists
    obtain ⟨r', hr'⟩ := ((tendsto_order.1 (tendsto_measure_cellMass_lt P hH k)).2 _ hε').exists
    obtain ⟨n, hn⟩ := ((tendsto_order.1 (tendsto_measure_not_innerMargin P habℓ hexh r')).2 _ hε').exists
    refine ⟨n, (windowLeakMean_le_errorBound hexact hH habℓ hℓ hc hm0 hmtop n (r := r) hδ k r').trans ?_⟩
    have h4 : ENNReal.ofReal (4 * (ε / 4)) = ENNReal.ofReal ε := by congr 1; ring
    rw [errorBound, h4]
    exact add_le_add (add_le_add hr.le hk.le) (add_le_add le_rfl (add_le_add hn.le hr'.le))
  have hlim : ∀ B : ℝ≥0∞, Tendsto (fun j : ℕ => B + M *
      ((ENNReal.ofReal (1 / ((j : ℝ) + 1)) + ENNReal.ofReal (1 / ((j : ℝ) + 1))) +
        (ENNReal.ofReal (1 / ((j : ℝ) + 1)) + (ENNReal.ofReal (1 / ((j : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((j : ℝ) + 1)))))) atTop (𝓝 B) := by
    intro B
    have he : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [ENNReal.ofReal_zero] at h
    have hs := (he.add he).add (he.add (he.add he))
    simp only [add_zero] at hs
    have hm := ENNReal.Tendsto.const_mul hs (Or.inr hM)
    rw [mul_zero] at hm
    have h := (tendsto_const_nhds (x := B)).add hm
    rwa [add_zero] at h
  have hle : ∀ A B : ℝ≥0∞, (∀ n, A ≤ B + M * windowLeakMean P H (a n) (b n) (ℓ n) m) → A ≤ B := by
    intro A B h
    refine ge_of_tendsto' (hlim B) fun j => ?_
    obtain ⟨n, hn⟩ := hsmall (1 / ((j : ℝ) + 1)) (by positivity)
    exact (h n).trans (add_le_add le_rfl (mul_le_mul_right hn _))
  exact le_antisymm
    (hle _ _ fun n => (lintegral_kernelAverage_le_add_and hexact hH habℓ hm0 hmtop hG hinv hM hGM n).1)
    (hle _ _ fun n => (lintegral_kernelAverage_le_add_and hexact hH habℓ hm0 hmtop hG hinv hM hGM n).2)

/-- **Condition 5 under the exact rerooting**: the dyadic-system re-sampling property, for all measurable jointly
invariant test functions, by truncation. -/
theorem cappedSquareResampling_of_exactIdentity (hexact : ExactIdentity P H a b ℓ c μ) [IsProbabilityMeasure P]
    (hH : Measurable H) (habℓ : ∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n))
    (hℓ : ∀ n ω, 0 < ℓ n ω)
    (hexh : ∀ᵐ ω ∂P, ∀ r : ℝ, ∀ᶠ n in atTop,
      Metric.ball (0 : Plane) r ⊆ planeSquare (a n ω) (b n ω) (ℓ n ω))
    (hc : ∀ n, Measurable (c n)) : CappedSquareResampling μ := by
  intro m hm0 hmtop G hG hinv
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hGN : ∀ N : ℕ, Measurable fun p => min (G p) (N : ℝ≥0∞) := fun _ => hG.min measurable_const
  have hinvN : ∀ N : ℕ, IsJointlyInvariant fun p => min (G p) (N : ℝ≥0∞) :=
    fun N s u hs H₁ H₂ hHH' q h₁ h₂ w =>
      congrArg (fun x => min x (N : ℝ≥0∞)) (hinv s u hs H₁ H₂ hHH' q h₁ h₂ w)
  have heqN : ∀ N : ℕ, ∫⁻ H', ∫⁻ q, kernelAverage m (fun p => min (G p) (N : ℝ≥0∞)) (H', q, 0) ∂dyadicLaw ∂μ =
      ∫⁻ H', ∫⁻ q, min (G (H', q, 0)) (N : ℝ≥0∞) ∂dyadicLaw ∂μ := fun N =>
    lintegral_kernelAverage_eq_of_le hexact hH habℓ hℓ hexh hc hm0 hmtop (hGN N) (hinvN N)
      (ENNReal.natCast_ne_top N) (fun p => min_le_right _ _)
  have hmono : ∀ p, Monotone fun N : ℕ => min (G p) (N : ℝ≥0∞) :=
    fun _ _ _ h => min_le_min_left _ (by exact_mod_cast h)
  have hsup : ∀ p, ⨆ N : ℕ, min (G p) (N : ℝ≥0∞) = G p := by
    intro p
    refine le_antisymm (iSup_le fun N => min_le_left _ _) ?_
    by_cases htop : G p = ∞
    · rw [htop]
      simp only [min_eq_right le_top]
      rw [ENNReal.iSup_natCast]
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt htop
      exact le_iSup_of_le N (le_of_eq (min_eq_left hN.le).symm)
  have hKsup : ∀ p, ⨆ N : ℕ, kernelAverage m (fun p => min (G p) (N : ℝ≥0∞)) p = kernelAverage m G p := by
    intro p
    simp only [kernelAverage]
    rw [← lintegral_iSup (f := fun (N : ℕ) z => averageKernel m (p.1, (p.2.1, p.2.2), z) *
        min (G (p.1, p.2.1, z)) (N : ℝ≥0∞)) (fun N => ((measurable_averageKernel m).comp (measurable_const.prodMk
        (measurable_const.prodMk measurable_id))).mul ((hGN N).comp (measurable_const.prodMk
          (measurable_const.prodMk measurable_id))))
      (fun _ _ h _ => mul_le_mul_right (hmono _ h) _)]
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.mul_iSup, hsup]
  have hL : ∫⁻ H', ∫⁻ q, cappedSquareAverage m G H' q ∂dyadicLaw ∂μ =
      ∫⁻ H', ∫⁻ q, kernelAverage m G (H', q, 0) ∂dyadicLaw ∂μ :=
    lintegral_congr fun H' => lintegral_congr_ae
      ((ae_kernelAverage_origin_eq hm0 hmtop G H').mono fun _ hq => hq.symm)
  rw [hL]
  calc ∫⁻ H', ∫⁻ q, kernelAverage m G (H', q, 0) ∂dyadicLaw ∂μ
      = ∫⁻ H', ∫⁻ q, ⨆ N : ℕ, kernelAverage m (fun p => min (G p) (N : ℝ≥0∞)) (H', q, 0) ∂dyadicLaw ∂μ := by
        simp_rw [hKsup]
    _ = ⨆ N : ℕ, ∫⁻ H', ∫⁻ q, kernelAverage m (fun p => min (G p) (N : ℝ≥0∞)) (H', q, 0) ∂dyadicLaw ∂μ :=
        lintegral_lintegral_iSup (f := fun N x => kernelAverage m (fun p => min (G p) (N : ℝ≥0∞)) (x.1, x.2, 0))
          (fun N => (measurable_kernelAverage m (hGN N)).comp
            (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
          (fun _ _ h _ => lintegral_mono fun _ => mul_le_mul_right (hmono _ h) _)
    _ = ⨆ N : ℕ, ∫⁻ H', ∫⁻ q, min (G (H', q, 0)) (N : ℝ≥0∞) ∂dyadicLaw ∂μ := by simp_rw [heqN]
    _ = ∫⁻ H', ∫⁻ q, ⨆ N : ℕ, min (G (H', q, 0)) (N : ℝ≥0∞) ∂dyadicLaw ∂μ :=
        (lintegral_lintegral_iSup (f := fun N x => min (G (x.1, x.2, 0)) (N : ℝ≥0∞))
          (fun N => (hGN N).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
          (fun _ _ h _ => hmono _ h)).symm
    _ = ∫⁻ H', ∫⁻ q, G (H', q, 0) ∂dyadicLaw ∂μ := by simp_rw [hsup]

end Final

/-- **The dyadic-system re-sampling property from exact rerooting over random squares** (Gwynne–Miller–Sheffield,
arXiv:1807.07515v3, Lemma 2.3, condition 5, in the test-function form `CappedSquareResampling`): if the law `μ` is
exactly attained, at every level, by rerooting a random configuration at a uniform point of a random square, the
squares eventually containing every ball around the origin, then `μ` has the re-sampling property. -/
theorem cappedSquareResampling_of_exactSquareRerooting {μ : Measure GMSSpace} (h : ExactSquareRerooting μ) :
    CappedSquareResampling μ := by
  obtain ⟨Ω, _, P, H, hP, hHm, a, b, ℓ, habℓ, hℓ, hexh, c, hc, hexact⟩ := h
  have := hP
  have hexact' : ExactIdentity P (hHm.mk H) a b ℓ c μ := by
    intro n F hF
    rw [← hexact n F hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hHm.ae_eq_mk] with ω hω
    rw [hω]
  exact cappedSquareResampling_of_exactIdentity hexact' hHm.measurable_mk habℓ hℓ hexh hc

/-- **The mass-transport principle from exact rerooting over random squares** (Gwynne–Miller–Sheffield,
arXiv:1807.07515v3, Definition 1.2, condition 4): Condition 5 ⇒ Condition 4 (Appendix B, (B.7)-(B.8)) applied to
`cappedSquareResampling_of_exactSquareRerooting`. -/
theorem massTransport_of_exactSquareRerooting {μ : Measure GMSSpace} (h : ExactSquareRerooting μ) :
    MassTransport μ :=
  massTransport_of_cappedSquareResampling (cappedSquareResampling_of_exactSquareRerooting h)

end MatedCRT.ZeroConePolygonal
