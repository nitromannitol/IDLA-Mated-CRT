import LatticeProb.Prob.CellConfigOriginSquares
import LatticeProb.Prob.CellConfigKernelExactCovariance
import LatticeProb.Prob.CellConfigKernelAverage

/-!
# Mass transport from the dyadic-system re-sampling property

Gwynne, Miller and Sheffield (*An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515) give equivalent forms of translation invariance modulo scaling of
a random cell configuration `H` (Definition 1.2 and Lemma 2.3). Condition 5 of Lemma 2.3, the
*dyadic system re-sampling property*, reads: let `D` be a uniform dyadic system independent of `H`
and `Ŝ_m = Ŝ_m^0` the capped square of cell mass `m` around the origin, (2.1); conditional on
`(H, D)` let `z` be sampled uniformly from Lebesgue measure on `Ŝ_m`; then `(H - z, D - z)` agrees
in law with `(H, D)` modulo scaling. In test-function form (`CappedSquareResampling`): for every
measurable `G(H, D, w) ≥ 0` invariant under the joint similarity of the configuration, the dyadic
system and the root, `E[|Ŝ_m|⁻¹ ∫_{Ŝ_m} G(H, D, z) dz] = E[G(H, D, 0)]`.

This file proves Condition 5 ⇒ Condition 4, the mass-transport principle `MassTransport`
(arXiv 1807.07515, Appendix B, (B.7)–(B.8)). For a kernel `F` covariant of degree `-2` the
functions `G₁(H, D, w) = ∫_{Ŝ_m^w} F(H, w, u) du` and `G₂(H, D, w) = ∫_{Ŝ_m^w} F(H, u, w) du` are
invariant under the joint similarity. Since `Ŝ_m^z = Ŝ_m` for almost every `z ∈ Ŝ_m` (Lemma 2.2),
the re-sampling property turns both `E ∫_{Ŝ_m} F(H, 0, u) du` and `E ∫_{Ŝ_m} F(H, u, 0) du` into
`E[|Ŝ_m|⁻¹ ∫_{Ŝ_m × Ŝ_m} F(H, v, u) du dv]`, and letting `m → ∞` (the squares `Ŝ_m` increase to the
plane) gives (1.3). The converse, Condition 4 ⇒ Condition 5, is
`LatticeProb.CellConfigCappedSquare.lintegral_cappedSquare_average_eq_joint`.

## Main results
* `CappedSquareResampling μ`: Condition 5 of Lemma 2.3 of arXiv 1807.07515, test-function form.
* `massTransport_of_cappedSquareResampling`: Condition 5 ⇒ Condition 4.
* `cappedSquareResampling_iff_massTransport`: the two conditions are equivalent.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare LatticeProb.CellMass
  LatticeProb.CappedSquare LatticeProb.DyadicOffset

/-- **The dyadic-system re-sampling property** (Gwynne, Miller and Sheffield, arXiv 1807.07515,
Lemma 2.3, condition 5), in test-function form: for every cell mass `m ∈ (0, ∞)` and every
measurable `G(H, D, w) ≥ 0` invariant under the joint similarity
`(H, D, w) ↦ (C(H - u), C(D - u), C(w - u))` (for every dyadic system with compatible offset
sequences), `E[|Ŝ_m^0|⁻¹ ∫_{Ŝ_m^0} G(H, D, z) dz] = E[G(H, D, 0)]`, the expectations taken over
the configuration and an independent uniform dyadic system `D`. With
`G(H, D, w) = Ψ(C(H - w), C(D - w))` for a scale-invariant `Ψ`, this is the equality in law of
`(H - z, D - z)` and `(H, D)` modulo scaling, `z` uniform on `Ŝ_m^0` given `(H, D)`. -/
def CappedSquareResampling (μ : Measure GMSSpace) : Prop :=
  ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞, Measurable G →
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) →
    ∫⁻ H, ∫⁻ q, cappedSquareAverage m G H q ∂dyadicLaw ∂μ =
      ∫⁻ H, ∫⁻ q, G (H, q, 0) ∂dyadicLaw ∂μ

/-- **Condition 4 ⇒ Condition 5** of Lemma 2.3 of arXiv 1807.07515: the mass-transport principle
implies the dyadic-system re-sampling property ((B.6), joint form). -/
theorem cappedSquareResampling_of_massTransport {μ : Measure GMSSpace} (hMT : MassTransport μ) :
    CappedSquareResampling μ :=
  fun _ hm0 hmtop _ hG hinv => lintegral_cappedSquare_average_eq_joint hMT hm0 hmtop hG hinv

/-! ### The indicator kernel of the capped squares -/

/-- **The indicator kernel of the capped square** `1(w₁ ∈ Ŝ_m^{w₀})` of a cell configuration `H`
and the dyadic system `q`, in the measurable form of a sum over the selected generations; the
argument is `(H, (q, w₀), w₁)`. -/
noncomputable def cappedSquareIndicatorKernel (m : ℝ≥0∞)
    (p : GMSSpace × ((DyadicCoord × ℂ) × ℂ)) : ℝ≥0∞ :=
  selectedSum (complexCells p.1.1) m p.2.1.1 p.2.1.2
    fun S => S.indicator (fun _ => (1 : ℝ≥0∞)) p.2.2

/-- The indicator kernel is measurable in the configuration, the dyadic system and the two
points. -/
theorem measurable_cappedSquareIndicatorKernel (m : ℝ≥0∞) :
    Measurable (cappedSquareIndicatorKernel m) := by
  unfold cappedSquareIndicatorKernel selectedSum
  refine Measurable.tsum fun j => measurable_indicator_apply
    (A := fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) =>
      selectionSet (complexCells p.1.1) m p.2.1.1 p.2.1.2)
    (f := fun p j => (squareAt p.2.1.1.1 p.2.1.1.2.1 p.2.1.1.2.2 j p.2.1.2).indicator
      (fun _ => (1 : ℝ≥0∞)) p.2.2) j ?_ ?_
  · have h := (measurableSet_cellMass_squareAt_le_lt j m).preimage
      (measurable_fst.prodMk measurable_snd.fst :
        Measurable fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) => (p.1, p.2.1))
    exact h
  · have h := ((measurable_const.indicator (measurableSet_squareAt_graph j)).comp measurable_snd :
      Measurable fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) =>
        {p : (DyadicCoord × ℂ) × ℂ | p.2 ∈ squareAt p.1.1.1 p.1.1.2.1 p.1.1.2.2 j p.1.2}.indicator
          (fun _ => (1 : ℝ≥0∞)) p.2)
    exact h

/-- **Exact covariance of the indicator kernel**: if `H'` is `C(H - u)` and the offsets of `q` are
compatible, the kernel of `H'` for the transformed coordinates at `(T w₀, T w₁)` is the kernel of
`H` at `(w₀, w₁)`, where `T z = s • z + b`. -/
theorem cappedSquareIndicatorKernel_similarity {s : ℝ} {u : Plane} {hs : 0 < s}
    {H H' : GMSSpace} (hHH' : IsSimilar s u hs H H') (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w₀ w₁ : ℂ) :
    cappedSquareIndicatorKernel m (H', (similarityCoord s u q, s • w₀ + similarityOffset s u),
        s • w₁ + similarityOffset s u) = cappedSquareIndicatorKernel m (H, (q, w₀), w₁) := by
  have hinj : Function.Injective fun z : ℂ => s • z + similarityOffset s u :=
    injective_smul_add hs.ne' _
  show selectedSum (complexCells H'.1) m (similarityCoord s u q) (s • w₀ + similarityOffset s u)
      (fun S => S.indicator (fun _ => (1 : ℝ≥0∞)) (s • w₁ + similarityOffset s u)) =
    selectedSum (complexCells H.1) m q w₀ (fun S => S.indicator (fun _ => (1 : ℝ≥0∞)) w₁)
  rw [selectedSum_similarity hHH' q h₁ h₂ m w₀]
  congr 1
  funext S
  by_cases hw : w₁ ∈ S
  · rw [indicator_of_mem hw, indicator_of_mem (hinj.mem_set_image.2 hw)]
  · rw [indicator_of_notMem hw, indicator_of_notMem (mt hinj.mem_set_image.1 hw)]

/-- **The capped square is the same from every point of it** (arXiv 1807.07515, Lemma 2.2): for
compatible offsets, if the generation `j` is selected at `w` and the off-grid point `z` lies in the
square of generation `j` at `w`, then the sum over the generations selected at `z` is the value at
that square. -/
theorem selectedSum_eq_of_mem_squareAt {ι : Type*} {c : ι → Set ℂ} {m : ℝ≥0∞}
    {q : DyadicCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {w z : ℂ}
    (hz : IsOffGrid q.1 q.2.1 q.2.2 z) {j : ℤ} (hj : j ∈ selectionSet c m q w)
    (hzw : z ∈ squareAt q.1 q.2.1 q.2.2 j w) (g : Set ℂ → ℝ≥0∞) :
    selectedSum c m q z g = g (squareAt q.1 q.2.1 q.2.2 j w) := by
  have e1 := squareAt_eq_of_mem hz hzw
  have e2 := squareAt_eq_of_mem hz
    (squareAt_mono_of_isCompatible h₁ h₂ w (by omega : j ≤ j + 1) hzw)
  have hjz : j ∈ selectionSet c m q z := by
    simpa only [selectionSet, Set.mem_ofPred_eq, ← e1, ← e2] using hj
  rw [selectedSum_eq_of_mem (monotone_cellMass_squareAt h₁ h₂ hz) hjz g, e1]

/-- The capped squares increase with the cell mass. -/
theorem cappedSquare_mono_mass {E : Type*} {𝒟 : Set (Set E)} {ν : Set E → ℝ≥0∞} {w : E}
    {m m' : ℝ≥0∞} (hm : m ≤ m') : cappedSquare 𝒟 ν m w ⊆ cappedSquare 𝒟 ν m' w :=
  sUnion_mono fun _ hS => mem_candidates.2
    ⟨(mem_candidates.1 hS).1, (mem_candidates.1 hS).2.1, (mem_candidates.1 hS).2.2.trans hm⟩

/-! ### The integral of a kernel over the capped square -/

/-- `∫_{Ŝ_m^w} Φ(H, w, u) du`, the integral of a function of the configuration and two points over
the capped square of mass `m` around the first point, in the measurable form of the indicator
kernel; the argument is `(H, q, w)`. -/
noncomputable def cappedSquareKernelIntegral (m : ℝ≥0∞) (Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞)
    (p : GMSSpace × DyadicCoord × ℂ) : ℝ≥0∞ :=
  ∫⁻ u, cappedSquareIndicatorKernel m (p.1, (p.2.1, p.2.2), u) * Φ (p.1, p.2.2, u)

/-- The capped-square integral of a measurable kernel is measurable. -/
theorem measurable_cappedSquareKernelIntegral (m : ℝ≥0∞) {Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞}
    (hΦ : Measurable Φ) : Measurable (cappedSquareKernelIntegral m Φ) := by
  unfold cappedSquareKernelIntegral
  exact Measurable.lintegral_prod_right'
    (f := fun x : (GMSSpace × DyadicCoord × ℂ) × ℂ =>
      cappedSquareIndicatorKernel m (x.1.1, (x.1.2.1, x.1.2.2), x.2) * Φ (x.1.1, x.1.2.2, x.2))
    (((measurable_cappedSquareIndicatorKernel m).comp (measurable_fst.fst.prodMk
      ((measurable_fst.snd.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd))).mul
      (hΦ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.snd.prodMk measurable_snd))))

/-- **Invariance of the capped-square integral of a covariant kernel**: if `Φ` is covariant of
degree `-2`, `Φ(C(H - u), C(a - u), C(b - u)) = C⁻² Φ(H, a, b)`, then `∫_{Ŝ_m^w} Φ(H, w, u) du` is
invariant under the joint similarity of the configuration, the dyadic system and the point. -/
theorem cappedSquareKernelIntegral_similarity {m : ℝ≥0∞} {Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞}
    (hΦ : Measurable Φ)
    (hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ a b : ℂ, Φ (H', s • a + similarityOffset s u, s • b + similarityOffset s u) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * Φ (H, a, b))
    (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace) (hHH' : IsSimilar s u hs H H')
    (q : DyadicCoord) (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (w : ℂ) :
    cappedSquareKernelIntegral m Φ (H', similarityCoord s u q, s • w + similarityOffset s u) =
      cappedSquareKernelIntegral m Φ (H, q, w) := by
  have hc0 : ENNReal.ofReal ((s ^ 2)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hs 2))).ne'
  have hf : Measurable fun z : ℂ =>
      cappedSquareIndicatorKernel m
          (H', (similarityCoord s u q, s • w + similarityOffset s u), z) *
        Φ (H', s • w + similarityOffset s u, z) :=
    ((measurable_cappedSquareIndicatorKernel m).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hg : Measurable fun z : ℂ =>
      cappedSquareIndicatorKernel m (H, (q, w), z) * Φ (H, w, z) :=
    ((measurable_cappedSquareIndicatorKernel m).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hkey := lintegral_comp_smul_add_complex hf hs (similarityOffset s u)
  have hpt : ∀ z : ℂ,
      cappedSquareIndicatorKernel m (H', (similarityCoord s u q, s • w + similarityOffset s u),
          s • z + similarityOffset s u) *
        Φ (H', s • w + similarityOffset s u, s • z + similarityOffset s u) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * (cappedSquareIndicatorKernel m (H, (q, w), z) * Φ (H, w, z)) := by
    intro z
    rw [cappedSquareIndicatorKernel_similarity hHH' q h₁ h₂ m w z, hcov s u hs H H' hHH' w z]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul _ hg] at hkey
  exact ((ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top).1 hkey).symm

/-- **The uniform average over the capped square of the capped-square integral** (arXiv
1807.07515, (B.7)–(B.8)): if `Ŝ_m^0` is the square of the selected generation `j` around the
origin, then for almost every `z ∈ Ŝ_m^0` the capped square around `z` is `Ŝ_m^0`, so the average
over `z ∈ Ŝ_m^0` of `∫_{Ŝ_m^z} Φ(H, z, u) du` is `|Ŝ_m^0|⁻¹ ∫_{Ŝ_m^0 × Ŝ_m^0} Φ(H, z, u) du dz`. -/
theorem cappedSquareAverage_kernelIntegral_eq {m : ℝ≥0∞} {Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞}
    (hΦ : Measurable Φ) (H : GMSSpace) {q : DyadicCoord} (h₁ : IsCompatible q.2.1)
    (h₂ : IsCompatible q.2.2) {j : ℤ} (hj : j ∈ selectionSet (complexCells H.1) m q 0)
    (hS : originCappedSquare m H q = squareAt q.1 q.2.1 q.2.2 j 0) :
    cappedSquareAverage m (cappedSquareKernelIntegral m Φ) H q =
      (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        ∫⁻ z, ∫⁻ u, (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
          ((squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) u * Φ (H, z, u)) := by
  have hSm : MeasurableSet (squareAt q.1 q.2.1 q.2.2 j 0) := measurableSet_squareAt j 0
  have hinner : Measurable fun z : ℂ => ∫⁻ u,
      (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        ((squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) u * Φ (H, z, u)) :=
    Measurable.lintegral_prod_right'
      (f := fun x : ℂ × ℂ =>
        (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) x.1 *
          ((squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) x.2 *
            Φ (H, x.1, x.2)))
      (((measurable_const.indicator hSm).comp measurable_fst).mul
        (((measurable_const.indicator hSm).comp measurable_snd).mul
          (hΦ.comp (measurable_const.prodMk measurable_id))))
  rw [← lintegral_const_mul _ hinner, cappedSquareAverage, hS]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz
  by_cases hzS : z ∈ squareAt q.1 q.2.1 q.2.2 j 0
  · have hK : ∀ u : ℂ, cappedSquareIndicatorKernel m (H, (q, z), u) =
        (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) u := fun u =>
      selectedSum_eq_of_mem_squareAt h₁ h₂ hz hj hzS
        (fun S' => S'.indicator (fun _ => (1 : ℝ≥0∞)) u)
    simp only [cappedSquareKernelIntegral, hK, indicator_of_mem hzS, one_mul, mul_one]
  · simp only [indicator_of_notMem hzS, mul_zero, zero_mul, lintegral_zero]

/-- Tonelli on a square: exchanging the two points of the kernel does not change its integral over
`S × S`. -/
theorem lintegral_lintegral_square_swap {S : Set ℂ} (hS : MeasurableSet S)
    {Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞} (hΦ : Measurable Φ) (H : GMSSpace) :
    ∫⁻ z, ∫⁻ u, S.indicator (fun _ => (1 : ℝ≥0∞)) z *
        (S.indicator (fun _ => (1 : ℝ≥0∞)) u * Φ (H, u, z)) =
      ∫⁻ z, ∫⁻ u, S.indicator (fun _ => (1 : ℝ≥0∞)) z *
        (S.indicator (fun _ => (1 : ℝ≥0∞)) u * Φ (H, z, u)) := by
  have hm : Measurable fun p : ℂ × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
      (S.indicator (fun _ => (1 : ℝ≥0∞)) p.2 * Φ (H, p.2, p.1)) :=
    ((measurable_const.indicator hS).comp measurable_fst).mul
      (((measurable_const.indicator hS).comp measurable_snd).mul
        (hΦ.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))))
  rw [lintegral_lintegral_swap (f := fun z u => S.indicator (fun _ => (1 : ℝ≥0∞)) z *
      (S.indicator (fun _ => (1 : ℝ≥0∞)) u * Φ (H, u, z))) hm.aemeasurable]
  refine lintegral_congr fun z => lintegral_congr fun u => ?_
  ring

/-! ### Condition 5 ⇒ Condition 4 -/

section Resampling

variable {μ : Measure GMSSpace} {Φ : GMSSpace × ℂ × ℂ → ℝ≥0∞}

/-- **Both marked points carry the same mass on the capped squares** ((B.8) of arXiv 1807.07515):
under the re-sampling property, for every cell mass `m ∈ (0, ∞)` and every measurable `Φ` covariant
of degree `-2`, `E ∫_{Ŝ_m^0} Φ(H, 0, u) du = E ∫_{Ŝ_m^0} Φ(H, u, 0) du`. -/
theorem lintegral_cappedSquareKernelIntegral_swap (h5 : CappedSquareResampling μ)
    (hΦ : Measurable Φ)
    (hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ a b : ℂ, Φ (H', s • a + similarityOffset s u, s • b + similarityOffset s u) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * Φ (H, a, b))
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) :
    ∫⁻ H, ∫⁻ q, cappedSquareKernelIntegral m Φ (H, q, 0) ∂dyadicLaw ∂μ =
      ∫⁻ H, ∫⁻ q, cappedSquareKernelIntegral m (fun p => Φ (p.1, p.2.2, p.2.1)) (H, q, 0)
        ∂dyadicLaw ∂μ := by
  have hΦs : Measurable fun p : GMSSpace × ℂ × ℂ => Φ (p.1, p.2.2, p.2.1) :=
    hΦ.comp (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))
  have hcovs : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ a b : ℂ, Φ (H', s • b + similarityOffset s u, s • a + similarityOffset s u) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * Φ (H, b, a) :=
    fun s u hs H H' hHH' a b => hcov s u hs H H' hHH' b a
  rw [← h5 m hm0 hmtop _ (measurable_cappedSquareKernelIntegral m hΦ)
      (cappedSquareKernelIntegral_similarity hΦ hcov),
    ← h5 m hm0 hmtop _ (measurable_cappedSquareKernelIntegral m hΦs)
      (cappedSquareKernelIntegral_similarity hΦs hcovs)]
  refine lintegral_congr fun H => lintegral_congr_ae ?_
  have := countable_cells H.2
  filter_upwards [ae_isCompatible_system, ae_exists_isCappedSquare_squareAt_cellMass 0
    (locallyFinite_complexCells H.2) (iUnion_complexCells H.2) isCompact_complexCells
    (volume_complexCells_ne_zero H.2)] with q hq hex
  obtain ⟨j, hj1, hj2, hcap⟩ := hex m hm0 hmtop
  have hjS : j ∈ selectionSet (complexCells H.1) m q 0 := ⟨hj1, hj2⟩
  rw [cappedSquareAverage_kernelIntegral_eq hΦ H hq.1 hq.2 hjS hcap.cappedSquare_eq,
    cappedSquareAverage_kernelIntegral_eq hΦs H hq.1 hq.2 hjS hcap.cappedSquare_eq]
  congr 1
  exact (lintegral_lintegral_square_swap (measurableSet_squareAt j 0) hΦ H).symm

/-- **Exhaustion by the capped squares, for a fixed configuration**: the expected integral of `Φ`
over `Ŝ_{n+1}^0` increases with `n` to `∫ Φ(H, 0, u) du`. -/
theorem monotone_tendsto_lintegral_cappedSquareKernelIntegral (hΦ : Measurable Φ)
    (H : GMSSpace) :
    (Monotone fun n : ℕ =>
      ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw)
      atTop (𝓝 (∫⁻ u, Φ (H, 0, u))) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hm0 : ∀ n : ℕ, (n : ℝ≥0∞) + 1 ≠ 0 := fun _ => (lt_of_lt_of_le zero_lt_one le_add_self).ne'
  have hmtop : ∀ n : ℕ, (n : ℝ≥0∞) + 1 ≠ ∞ := fun n =>
    ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩
  have hgood : ∀ᵐ q ∂dyadicLaw,
      (Monotone fun n : ℕ => cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0)) ∧
      Tendsto (fun n : ℕ => cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0)) atTop
        (𝓝 (∫⁻ u, Φ (H, 0, u))) := by
    filter_upwards [ae_selectedSum_eq_cappedSquare_complexCells H.2 0, ae_iUnion_squareAt_eq_univ]
      with q hsel hexh
    have hK : ∀ (n : ℕ) (u : ℂ), cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) =
        (originCappedSquare ((n : ℝ≥0∞) + 1) H q).indicator (fun _ => (1 : ℝ≥0∞)) u :=
      fun n u => hsel _ (hm0 n) (hmtop n) fun S => S.indicator (fun _ => (1 : ℝ≥0∞)) u
    have hmono : ∀ u : ℂ, Monotone fun n : ℕ =>
        cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) * Φ (H, 0, u) := by
      intro u a b hnn'
      have hab : (a : ℝ≥0∞) + 1 ≤ (b : ℝ≥0∞) + 1 := add_le_add (Nat.mono_cast hnn') le_rfl
      simp only [hK]
      gcongr ?_ * _
      exact indicator_le_indicator_of_subset (f := fun _ : ℂ => (1 : ℝ≥0∞))
        (cappedSquare_mono_mass hab) (fun _ => zero_le) u
    have hlim : ∀ u : ℂ, Tendsto (fun n : ℕ =>
        cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) * Φ (H, 0, u)) atTop
        (𝓝 (Φ (H, 0, u))) := by
      intro u
      have hu : u ∈ ⋃ j, squareAt q.1 q.2.1 q.2.2 j 0 := by
        rw [hexh 0]
        exact mem_univ u
      obtain ⟨j, hj⟩ := mem_iUnion.1 hu
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (cellMass_squareAt_ne_top H q j)
      refine tendsto_atTop_of_eventually_const fun n (hn : N ≤ n) => ?_
      show cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) * Φ (H, 0, u) = Φ (H, 0, u)
      have hNn : ((N : ℕ) : ℝ≥0∞) ≤ (n : ℝ≥0∞) + 1 := by
        exact_mod_cast hn.trans (Nat.le_succ n)
      have hmem : u ∈ originCappedSquare ((n : ℝ≥0∞) + 1) H q :=
        mem_sUnion_of_mem hj (mem_candidates.2
          ⟨squareAt_mem_dyadicSquares j 0, mem_squareAt j 0, hN.le.trans hNn⟩)
      rw [hK, indicator_of_mem hmem, one_mul]
    have hmeasu : ∀ n : ℕ, AEMeasurable (fun u : ℂ =>
        cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) * Φ (H, 0, u)) volume :=
      fun _ => (((measurable_cappedSquareIndicatorKernel _).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
        (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).aemeasurable
    have hT : Tendsto (fun n : ℕ => ∫⁻ u,
        cappedSquareIndicatorKernel ((n : ℝ≥0∞) + 1) (H, (q, 0), u) * Φ (H, 0, u)) atTop
        (𝓝 (∫⁻ u, Φ (H, 0, u))) :=
      lintegral_tendsto_of_tendsto_of_monotone hmeasu (Eventually.of_forall hmono)
        (Eventually.of_forall hlim)
    exact ⟨fun _ _ h => lintegral_mono fun u => hmono u h, hT⟩
  have hmeas : ∀ n : ℕ, AEMeasurable (fun q : DyadicCoord =>
      cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0)) dyadicLaw := fun _ =>
    ((measurable_cappedSquareKernelIntegral _ hΦ).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))).aemeasurable
  have hlim : Tendsto (fun n : ℕ =>
      ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw) atTop
      (𝓝 (∫⁻ _q, ∫⁻ u, Φ (H, 0, u) ∂volume ∂dyadicLaw)) :=
    lintegral_tendsto_of_tendsto_of_monotone hmeas (hgood.mono fun _ hq => hq.1)
      (hgood.mono fun _ hq => hq.2)
  rw [lintegral_const, measure_univ, mul_one] at hlim
  exact ⟨fun _ _ h => lintegral_mono_ae (hgood.mono fun _ hq => hq.1 h), hlim⟩

/-- **Exhaustion by the capped squares**: `E ∫_{Ŝ_{n+1}^0} Φ(H, 0, u) du → E ∫ Φ(H, 0, u) du`. -/
theorem tendsto_lintegral_cappedSquareKernelIntegral (ν : Measure GMSSpace) (hΦ : Measurable Φ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ H, ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw ∂ν)
      atTop (𝓝 (∫⁻ H, ∫⁻ u, Φ (H, 0, u) ∂volume ∂ν)) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hmeas : ∀ n : ℕ, AEMeasurable (fun H : GMSSpace =>
      ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw) ν := fun n => by
    have h : Measurable fun H : GMSSpace =>
        ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw :=
      Measurable.lintegral_prod_right'
        (f := fun x : GMSSpace × DyadicCoord =>
          cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (x.1, x.2, 0))
        ((measurable_cappedSquareKernelIntegral _ hΦ).comp
          (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
    exact h.aemeasurable
  exact lintegral_tendsto_of_tendsto_of_monotone hmeas
    (Eventually.of_forall fun H => (monotone_tendsto_lintegral_cappedSquareKernelIntegral hΦ H).1)
    (Eventually.of_forall fun H => (monotone_tendsto_lintegral_cappedSquareKernelIntegral hΦ H).2)

/-- **Mass transport from the re-sampling property, kernel form** (arXiv 1807.07515, Appendix B,
Condition 5 ⇒ Condition 4): for every measurable `Φ ≥ 0` on configurations with two marked points
of `ℂ`, covariant of degree `-2`, `E ∫ Φ(H, 0, u) du = E ∫ Φ(H, u, 0) du`. -/
theorem lintegral_lintegral_eq_of_cappedSquareResampling (h5 : CappedSquareResampling μ)
    (hΦ : Measurable Φ)
    (hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ a b : ℂ, Φ (H', s • a + similarityOffset s u, s • b + similarityOffset s u) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * Φ (H, a, b)) :
    ∫⁻ H, ∫⁻ u, Φ (H, 0, u) ∂volume ∂μ = ∫⁻ H, ∫⁻ u, Φ (H, u, 0) ∂volume ∂μ := by
  have hΦs : Measurable fun p : GMSSpace × ℂ × ℂ => Φ (p.1, p.2.2, p.2.1) :=
    hΦ.comp (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))
  have hstep : ∀ n : ℕ,
      ∫⁻ H, ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1) Φ (H, q, 0) ∂dyadicLaw ∂μ =
        ∫⁻ H, ∫⁻ q, cappedSquareKernelIntegral ((n : ℝ≥0∞) + 1)
          (fun p => Φ (p.1, p.2.2, p.2.1)) (H, q, 0) ∂dyadicLaw ∂μ := fun n =>
    lintegral_cappedSquareKernelIntegral_swap h5 hΦ hcov
      (lt_of_lt_of_le zero_lt_one le_add_self).ne'
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
  exact tendsto_nhds_unique ((tendsto_lintegral_cappedSquareKernelIntegral μ hΦ).congr hstep)
    (tendsto_lintegral_cappedSquareKernelIntegral μ hΦs)

/-- **Condition 5 ⇒ Condition 4** of Lemma 2.3 of arXiv 1807.07515 (Appendix B, (B.7)–(B.8)): the
dyadic-system re-sampling property implies the mass-transport principle. -/
theorem massTransport_of_cappedSquareResampling (h5 : CappedSquareResampling μ) :
    MassTransport μ := by
  intro F hF hcov
  have hpc : Measurable fun z : ℂ => planeCoord z := planeCoord.continuous.measurable
  have hΦ : Measurable fun p : GMSSpace × ℂ × ℂ =>
      ((F (p.1, planeCoord p.2.1, planeCoord p.2.2) : ℝ≥0) : ℝ≥0∞) :=
    (hF.comp (measurable_fst.prodMk ((hpc.comp measurable_snd.fst).prodMk
      (hpc.comp measurable_snd.snd)))).coe_nnreal_ennreal
  have hcovΦ : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ a b : ℂ, ((F (H', planeCoord (s • a + similarityOffset s u),
          planeCoord (s • b + similarityOffset s u)) : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * ((F (H, planeCoord a, planeCoord b) : ℝ≥0) : ℝ≥0∞) := by
    intro s u hs H H' hHH' a b
    have h := congrArg ENNReal.ofReal (hcov s u hs H H' hHH' (planeCoord a) (planeCoord b))
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg s)), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal] at h
    rw [planeCoord_smul_add_similarityOffset, planeCoord_smul_add_similarityOffset]
    exact h
  have key := lintegral_lintegral_eq_of_cappedSquareResampling h5 hΦ hcovΦ
  have hmp : MeasurePreserving (fun z : ℂ => planeCoord z) volume volume :=
    planeCoord.measurePreserving
  have hL : ∀ H : GMSSpace, ∫⁻ w : Plane, ((F (H, 0, w) : ℝ≥0) : ℝ≥0∞) ∂volume =
      ∫⁻ z : ℂ, ((F (H, planeCoord 0, planeCoord z) : ℝ≥0) : ℝ≥0∞) := by
    intro H
    have hf : Measurable fun w : Plane => ((F (H, 0, w) : ℝ≥0) : ℝ≥0∞) :=
      (hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).coe_nnreal_ennreal
    rw [← hmp.lintegral_comp hf, map_zero]
  have hR : ∀ H : GMSSpace, ∫⁻ w : Plane, ((F (H, w, 0) : ℝ≥0) : ℝ≥0∞) ∂volume =
      ∫⁻ z : ℂ, ((F (H, planeCoord z, planeCoord 0) : ℝ≥0) : ℝ≥0∞) := by
    intro H
    have hf : Measurable fun w : Plane => ((F (H, w, 0) : ℝ≥0) : ℝ≥0∞) :=
      (hF.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))).coe_nnreal_ennreal
    rw [← hmp.lintegral_comp hf, map_zero]
  rw [lintegral_congr hL, lintegral_congr hR]
  exact key

end Resampling

/-- **Equivalence of Conditions 4 and 5** of Lemma 2.3 of arXiv 1807.07515: a random cell
configuration satisfies the mass-transport principle if and only if it has the dyadic-system
re-sampling property. -/
theorem cappedSquareResampling_iff_massTransport {μ : Measure GMSSpace} :
    CappedSquareResampling μ ↔ MassTransport μ :=
  ⟨massTransport_of_cappedSquareResampling, cappedSquareResampling_of_massTransport⟩

end MatedCRT
