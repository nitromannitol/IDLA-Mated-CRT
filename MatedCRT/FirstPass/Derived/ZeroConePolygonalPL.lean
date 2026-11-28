import MatedCRT.FirstPass.Derived.ZeroConePolygonalVertices

/-!
# Piecewise affine homeomorphisms of the plane

This file contains the plane geometry behind the homeomorphisms `f_n` of the Borel measurability
argument for the polygonal cell configuration. The topology on cell configurations of
Gwynne–Miller–Sheffield (arXiv:1807.07515v3, (1.14)–(1.15), p. 15) compares two configurations
through a homeomorphism of the plane that carries cells to cells and moves points little. The
measurability argument builds such a homeomorphism from a triangulation whose vertices are moved
slightly: on each triangle the map is the affine interpolation of the displaced vertices; the
derivative of `f_n - id` on each triangle is small, so `f_n - id` is Lipschitz with a small constant,
and once that constant is less than one, `f_n` is a homeomorphism of the plane (solve
`x = y - (f_n - id)(x)` by contraction).

Main declarations:

* `homeomorphAddOfLipschitzWith`: if `g` is `K`-Lipschitz with `K < 1`, then `x ↦ x + g x` is a
  homeomorphism (Mathlib's `ApproximatesLinearOn.toHomeomorph` for the identity), and it and its
  inverse move every point by at most `sup ‖g‖`.
* `lipschitzWith_of_locallyFinite_convex`: a continuous map which is `L`-Lipschitz on each member of
  a locally finite cover by closed convex sets is `L`-Lipschitz (cut segments at the members).
* `triangleInterp`: the affine map taking the vertices `a b c` of a nondegenerate triangle
  (`cross (b - a) (c - a) ≠ 0`, with `cross` from `ZeroConePolygonalVertices`) to `a' b' c'`; it
  moves the points of the triangle by at most the largest vertex displacement `δ`,
  `triangleInterp - id` is `4 δ / minHeight a b c`-Lipschitz, and it maps the triangle onto the
  triangle `a' b' c'`.
* `IsTriangulation`, `plMap`: a locally finite family of nondegenerate triangles covering the plane
  and meeting in common faces, and the glued piecewise affine map for a vertex displacement `σ`.
* `plHomeomorph`, `exists_homeomorph_piecewiseAffine`: the glued map is a homeomorphism of the
  plane when on every triangle `i` the vertex displacements `δ i` satisfy `4 δ i / minHeight ≤ L`
  with `L < 1` (a per-triangle condition, so it applies to infinite triangulations whose heights
  have no positive lower bound); it moves the points of triangle `i` by at most `δ i`, it and its
  inverse move every point by at most `sup δ`, `f - id` is `L`-Lipschitz, it is the identity on the
  triangles with fixed vertices, and it maps each triangle, each segment inside a triangle, and each
  union of triangles onto its counterpart.
* `exists_homeomorph_piecewiseAffine_of_le_minHeight`: the uniform form, with bounds `δ` and
  `4 δ / h` which tend to zero with the vertex displacements.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ### Perturbations of the identity by contractions -/

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → E} {K : ℝ≥0}

/-- `x ↦ x + g x` approximates the identity with constant `K` when `g` is `K`-Lipschitz. -/
theorem approximatesLinearOn_add_of_lipschitzWith (hg : LipschitzWith K g) :
    ApproximatesLinearOn (fun x => x + g x)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) univ K := by
  intro x _ y _
  have h1 : ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (x - y) = x - y := rfl
  have h2 : x + g x - (y + g y) - (x - y) = g x - g y := by abel
  calc ‖x + g x - (y + g y) - ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (x - y)‖
      = dist (g x) (g y) := by rw [h1, h2, dist_eq_norm]
    _ ≤ K * dist x y := hg.dist_le_mul x y
    _ = K * ‖x - y‖ := by rw [dist_eq_norm]

theorem subsingleton_or_lt_inv_nnnorm_refl (hK : K < 1) :
    Subsingleton E ∨
      K < ‖(((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E).symm : E ≃L[ℝ] E) : E →L[ℝ] E)‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Or.inl hE
  · refine Or.inr ?_
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one]
    exact hK

/-- **A perturbation of the identity by a contraction is a homeomorphism**: for `g` `K`-Lipschitz
with `K < 1`, the map `x ↦ x + g x` is a homeomorphism (Mathlib's global inverse function theorem
`ApproximatesLinearOn.toHomeomorph`, applied to the identity). -/
def homeomorphAddOfLipschitzWith [CompleteSpace E] (hK : K < 1) (hg : LipschitzWith K g) :
    E ≃ₜ E :=
  (approximatesLinearOn_add_of_lipschitzWith hg).toHomeomorph (fun x => x + g x)
    (subsingleton_or_lt_inv_nnnorm_refl hK)

@[simp]
theorem homeomorphAddOfLipschitzWith_apply [CompleteSpace E] (hK : K < 1) (hg : LipschitzWith K g)
    (x : E) : homeomorphAddOfLipschitzWith hK hg x = x + g x :=
  rfl

/-- The displacement of `x ↦ x + g x` is bounded by that of `g`. -/
theorem dist_homeomorphAddOfLipschitzWith_le [CompleteSpace E] (hK : K < 1)
    (hg : LipschitzWith K g) {δ : ℝ} (hδ : ∀ x, ‖g x‖ ≤ δ) (x : E) :
    dist x (homeomorphAddOfLipschitzWith hK hg x) ≤ δ := by
  rw [homeomorphAddOfLipschitzWith_apply, dist_eq_norm, show x - (x + g x) = -g x by abel,
    norm_neg]
  exact hδ x

/-- The displacement of the inverse of `x ↦ x + g x` is bounded by that of `g`. -/
theorem dist_symm_homeomorphAddOfLipschitzWith_le [CompleteSpace E] (hK : K < 1)
    (hg : LipschitzWith K g) {δ : ℝ} (hδ : ∀ x, ‖g x‖ ≤ δ) (y : E) :
    dist y ((homeomorphAddOfLipschitzWith hK hg).symm y) ≤ δ := by
  obtain ⟨x, rfl⟩ := (homeomorphAddOfLipschitzWith hK hg).surjective y
  rw [Homeomorph.symm_apply_apply, homeomorphAddOfLipschitzWith_apply, dist_eq_norm,
    show x + g x - x = g x by abel]
  exact hδ x

end Perturbation

/-! ### Lipschitz maps on locally finite closed convex covers -/

section Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} {T : ι → Set E}

/-- Along a segment, near each parameter `t₀ < 1` a single member of a locally finite closed cover
contains both the point of parameter `t₀` and a point of some parameter `t₁ > t₀`. -/
theorem exists_mem_cover_lineMap (hT : LocallyFinite T) (hcl : ∀ i, IsClosed (T i))
    (hcov : ⋃ i, T i = univ) (x y : E) {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ t₁ ∈ Ioc t₀ 1, ∃ i, AffineMap.lineMap x y t₀ ∈ T i ∧ AffineMap.lineMap x y t₁ ∈ T i := by
  set z : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hzc : Continuous z := z.continuous_of_finiteDimensional
  obtain ⟨U, hU, hfin⟩ := hT (z t₀)
  set B : Set ι := {i | (T i ∩ U).Nonempty ∧ z t₀ ∉ T i}
  have hBfin : B.Finite := hfin.subset fun i hi => hi.1
  have hW : U ∩ ⋂ i ∈ B, (T i)ᶜ ∈ nhds (z t₀) :=
    Filter.inter_mem hU
      ((Filter.biInter_mem hBfin).2 fun i hi => (hcl i).isOpen_compl.mem_nhds hi.2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hzc.continuousAt.preimage_mem_nhds hW)
  have ht₀t₁ : t₀ < min 1 (t₀ + ε / 2) := lt_min ht₀ (by linarith)
  have hlt : min 1 (t₀ + ε / 2) ∈ ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right 1 (t₀ + ε / 2)]
  have hmem : z (min 1 (t₀ + ε / 2)) ∈ U ∩ ⋂ i ∈ B, (T i)ᶜ := hball hlt
  have hz1 : z (min 1 (t₀ + ε / 2)) ∈ ⋃ i, T i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz1
  refine ⟨min 1 (t₀ + ε / 2), ⟨ht₀t₁, min_le_left _ _⟩, i, ?_, hi⟩
  by_contra hno
  exact mem_iInter₂.1 hmem.2 i ⟨⟨_, hi, hmem.1⟩, hno⟩ hi

/-- **Lipschitz gluing**: a continuous map which is `L`-Lipschitz on each member of a locally finite
cover by closed convex sets is `L`-Lipschitz (subdivide segments at the members). -/
theorem lipschitzWith_of_locallyFinite_convex {F : Type*} [PseudoMetricSpace F]
    (hT : LocallyFinite T) (hcl : ∀ i, IsClosed (T i)) (hconv : ∀ i, Convex ℝ (T i))
    (hcov : ⋃ i, T i = univ) {g : E → F} (hg : Continuous g) {L : ℝ≥0}
    (hL : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, dist (g x) (g y) ≤ L * dist x y) : LipschitzWith L g := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  set z : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hzc : Continuous z := z.continuous_of_finiteDimensional
  have hdist : ∀ t t', dist (z t) (z t') = dist t t' * dist x y := fun t t' =>
    dist_lineMap_lineMap x y t t'
  set S : Set ℝ := {t | dist (g (z t)) (g x) ≤ L * (t * dist x y)}
  have hSc : IsClosed S :=
    isClosed_le ((hg.comp hzc).dist continuous_const) (by fun_prop)
  have hz0 : z 0 = x := AffineMap.lineMap_apply_zero x y
  have hz1 : z 1 = y := AffineMap.lineMap_apply_one x y
  have hmain : Icc (0 : ℝ) 1 ⊆ S := by
    refine IsClosed.Icc_subset_of_forall_exists_gt (hSc.inter isClosed_Icc) ?_ ?_
    · show dist (g (z 0)) (g x) ≤ L * (0 * dist x y)
      rw [hz0, dist_self, zero_mul, mul_zero]
    · rintro t₀ ⟨ht₀S, -, ht₀1⟩ t' ht'
      obtain ⟨t₁, ht₁, i, hi₀, hi₁⟩ := exists_mem_cover_lineMap hT hcl hcov x y ht₀1
      have htt₀ : t₀ < min t' t₁ := lt_min ht' ht₁.1
      have hti : z (min t' t₁) ∈ T i :=
        (convex_iff_ordConnected.1 ((hconv i).affine_preimage z)).out hi₀ hi₁
          ⟨htt₀.le, min_le_right _ _⟩
      refine ⟨min t' t₁, ?_, htt₀, min_le_left _ _⟩
      have h1 : dist (g (z (min t' t₁))) (g (z t₀)) ≤ L * dist (z (min t' t₁)) (z t₀) :=
        hL i _ hti _ hi₀
      have h2 : dist (g (z t₀)) (g x) ≤ L * (t₀ * dist x y) := ht₀S
      have h3 := hdist (min t' t₁) t₀
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ min t' t₁ - t₀)] at h3
      show dist (g (z (min t' t₁))) (g x) ≤ L * (min t' t₁ * dist x y)
      calc dist (g (z (min t' t₁))) (g x)
          ≤ dist (g (z (min t' t₁))) (g (z t₀)) + dist (g (z t₀)) (g x) := dist_triangle _ _ _
        _ ≤ L * dist (z (min t' t₁)) (z t₀) + L * (t₀ * dist x y) := add_le_add h1 h2
        _ = L * (min t' t₁ * dist x y) := by rw [h3]; ring
  have h1 : dist (g (z 1)) (g x) ≤ L * (1 * dist x y) := hmain ⟨zero_le_one, le_rfl⟩
  rw [hz1, one_mul] at h1
  rw [dist_comm (g x) (g y)]
  exact h1

end Cover

/-! ### Affine interpolation on a triangle -/

theorem abs_cross_le (u v : Plane) : |cross u v| ≤ ‖u‖ * ‖v‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    Fin.sum_univ_two]
  unfold cross
  nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1)]

theorem cross_self (u : Plane) : cross u u = 0 := by
  unfold cross
  ring

theorem cross_decomp (u v w : Plane) :
    ∀ i : Fin 2, w i * cross u v = cross w v * u i + cross u w * v i :=
  Fin.forall_fin_two.2 ⟨by simp only [cross]; ring, by simp only [cross]; ring⟩

/-- Every vector is a combination of two vectors with nonzero cross product, with coefficients given
by cross products (Cramer's rule). -/
theorem eq_cross_smul_add {u v : Plane} (h : cross u v ≠ 0) (w : Plane) :
    w = (cross w v / cross u v) • u + (cross u w / cross u v) • v := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
  exact cross_decomp u v w i

/-- The minimal height of the triangle `a b c`: twice its area divided by its longest side. -/
def minHeight (a b c : Plane) : ℝ :=
  |cross (b - a) (c - a)| / max (max ‖b - a‖ ‖c - a‖) ‖c - b‖

theorem minHeight_pos {a b c : Plane} (h : cross (b - a) (c - a) ≠ 0) : 0 < minHeight a b c := by
  have hba : b - a ≠ 0 := by
    intro hba
    apply h
    rw [hba]
    simp [cross]
  exact div_pos (abs_pos.2 h)
    ((norm_pos_iff.2 hba).trans_le ((le_max_left _ _).trans (le_max_left _ _)))

/-- The linear map of the plane sending `u ↦ u'` and `v ↦ v'`, for `u, v` with nonzero cross
product. -/
def interpLinear (u v u' v' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun w := (cross w v / cross u v) • u' + (cross u w / cross u v) • v'
  map_add' w w' := by
    ext i
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  map_smul' c w := by
    ext i
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem interpLinear_apply (u v u' v' w : Plane) :
    interpLinear u v u' v' w =
      (cross w v / cross u v) • u' + (cross u w / cross u v) • v' :=
  rfl

theorem interpLinear_left {u v : Plane} (u' v' : Plane) (h : cross u v ≠ 0) :
    interpLinear u v u' v' u = u' := by
  rw [interpLinear_apply, cross_self, div_self h, zero_div, one_smul, zero_smul, add_zero]

theorem interpLinear_right {u v : Plane} (u' v' : Plane) (h : cross u v ≠ 0) :
    interpLinear u v u' v' v = v' := by
  rw [interpLinear_apply, cross_self, div_self h, zero_div, one_smul, zero_smul, zero_add]

/-- **The affine interpolation on a triangle**: the affine map of the plane with `a ↦ a'`,
`b ↦ b'`, `c ↦ c'` (when `a b c` is nondegenerate). -/
def triangleInterp (a b c a' b' c' : Plane) : Plane →ᵃ[ℝ] Plane where
  toFun x := a' + interpLinear (b - a) (c - a) (b' - a') (c' - a') (x - a)
  linear := interpLinear (b - a) (c - a) (b' - a') (c' - a')
  map_vadd' x v := by
    simp only [vadd_eq_add]
    rw [show v + x - a = v + (x - a) by abel, map_add]
    abel

variable {a b c a' b' c' : Plane}

theorem triangleInterp_apply (x : Plane) :
    triangleInterp a b c a' b' c' x =
      a' + interpLinear (b - a) (c - a) (b' - a') (c' - a') (x - a) :=
  rfl

theorem triangleInterp_left : triangleInterp a b c a' b' c' a = a' := by
  rw [triangleInterp_apply, sub_self, map_zero, add_zero]

theorem triangleInterp_mid (h : cross (b - a) (c - a) ≠ 0) :
    triangleInterp a b c a' b' c' b = b' := by
  rw [triangleInterp_apply, interpLinear_left _ _ h]
  abel

theorem triangleInterp_right (h : cross (b - a) (c - a) ≠ 0) :
    triangleInterp a b c a' b' c' c = c' := by
  rw [triangleInterp_apply, interpLinear_right _ _ h]
  abel

/-- The displacement `‖A x - x‖` of the affine interpolation on the triangle is at most the
largest vertex displacement. -/
theorem norm_triangleInterp_sub_le {δ : ℝ} (ha : ‖a' - a‖ ≤ δ) (hb : ‖b' - b‖ ≤ δ)
    (hc : ‖c' - c‖ ≤ δ) (h : cross (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ convexHull ℝ {a, b, c}) : ‖triangleInterp a b c a' b' c' x - x‖ ≤ δ := by
  have key : ∀ y, y ∈ (triangleInterp a b c a' b' c' - AffineMap.id ℝ Plane) ⁻¹' closedBall 0 δ ↔
      ‖triangleInterp a b c a' b' c' y - y‖ ≤ δ := fun y => by
    rw [mem_preimage, mem_closedBall_zero_iff, AffineMap.coe_sub, AffineMap.coe_id, Pi.sub_apply,
      id_eq]
  have hconv := (convex_closedBall (0 : Plane) δ).affine_preimage
    (triangleInterp a b c a' b' c' - AffineMap.id ℝ Plane)
  have hsub : ({a, b, c} : Set Plane) ⊆
      (triangleInterp a b c a' b' c' - AffineMap.id ℝ Plane) ⁻¹' closedBall 0 δ := by
    rintro y (rfl | rfl | rfl)
    · rw [key, triangleInterp_left]; exact ha
    · rw [key, triangleInterp_mid h]; exact hb
    · rw [key, triangleInterp_right h]; exact hc
  exact (key x).1 (convexHull_min hsub hconv hx)

/-- The linear part of `triangleInterp - id` has operator norm at most `4 δ / minHeight`. -/
theorem norm_interpLinear_sub_le {δ : ℝ} (ha : ‖a' - a‖ ≤ δ) (hb : ‖b' - b‖ ≤ δ)
    (hc : ‖c' - c‖ ≤ δ) (h : cross (b - a) (c - a) ≠ 0) (w : Plane) :
    ‖interpLinear (b - a) (c - a) (b' - a') (c' - a') w - w‖ ≤
      4 * δ / minHeight a b c * ‖w‖ := by
  have hD : 0 < |cross (b - a) (c - a)| := abs_pos.2 h
  obtain ⟨m, hm⟩ : ∃ m, m = max (max ‖b - a‖ ‖c - a‖) ‖c - b‖ := ⟨_, rfl⟩
  have hum : ‖b - a‖ ≤ m := by rw [hm]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hvm : ‖c - a‖ ≤ m := by rw [hm]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hum
  have hmin : 4 * δ / minHeight a b c = 4 * δ * m / |cross (b - a) (c - a)| := by
    rw [minHeight, ← hm, div_div_eq_mul_div]
  have hL : interpLinear (b - a) (c - a) (b' - a') (c' - a') w - w =
      (cross w (c - a) / cross (b - a) (c - a)) • ((b' - a') - (b - a)) +
        (cross (b - a) w / cross (b - a) (c - a)) • ((c' - a') - (c - a)) := by
    conv_lhs => rw [eq_cross_smul_add h w]
    rw [map_add, map_smul, map_smul, interpLinear_left _ _ h, interpLinear_right _ _ h]
    module
  have hu' : ‖(b' - a') - (b - a)‖ ≤ 2 * δ := by
    rw [show (b' - a') - (b - a) = (b' - b) - (a' - a) by abel]
    exact (norm_sub_le _ _).trans (by linarith)
  have hv' : ‖(c' - a') - (c - a)‖ ≤ 2 * δ := by
    rw [show (c' - a') - (c - a) = (c' - c) - (a' - a) by abel]
    exact (norm_sub_le _ _).trans (by linarith)
  have hl : |cross w (c - a) / cross (b - a) (c - a)| ≤
      ‖w‖ * m / |cross (b - a) (c - a)| := by
    rw [abs_div]
    exact div_le_div_of_nonneg_right
      ((abs_cross_le w (c - a)).trans (mul_le_mul_of_nonneg_left hvm (norm_nonneg _))) hD.le
  have hl' : |cross (b - a) w / cross (b - a) (c - a)| ≤
      ‖w‖ * m / |cross (b - a) (c - a)| := by
    rw [abs_div]
    refine div_le_div_of_nonneg_right ?_ hD.le
    calc |cross (b - a) w| ≤ ‖b - a‖ * ‖w‖ := abs_cross_le _ _
      _ ≤ m * ‖w‖ := mul_le_mul_of_nonneg_right hum (norm_nonneg _)
      _ = ‖w‖ * m := mul_comm _ _
  have hq : 0 ≤ ‖w‖ * m / |cross (b - a) (c - a)| :=
    div_nonneg (mul_nonneg (norm_nonneg _) hm0) hD.le
  rw [hL, hmin]
  calc _ ≤ ‖(cross w (c - a) / cross (b - a) (c - a)) • ((b' - a') - (b - a))‖ +
        ‖(cross (b - a) w / cross (b - a) (c - a)) • ((c' - a') - (c - a))‖ :=
        norm_add_le _ _
    _ = |cross w (c - a) / cross (b - a) (c - a)| * ‖(b' - a') - (b - a)‖ +
        |cross (b - a) w / cross (b - a) (c - a)| * ‖(c' - a') - (c - a)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖w‖ * m / |cross (b - a) (c - a)| * (2 * δ) +
        ‖w‖ * m / |cross (b - a) (c - a)| * (2 * δ) :=
        add_le_add (mul_le_mul hl hu' (norm_nonneg _) hq) (mul_le_mul hl' hv' (norm_nonneg _) hq)
    _ = 4 * δ * m / |cross (b - a) (c - a)| * ‖w‖ := by ring

/-- `triangleInterp - id` is Lipschitz on the whole plane with constant `4 δ / minHeight`. -/
theorem norm_triangleInterp_sub_sub_le {δ : ℝ} (ha : ‖a' - a‖ ≤ δ) (hb : ‖b' - b‖ ≤ δ)
    (hc : ‖c' - c‖ ≤ δ) (h : cross (b - a) (c - a) ≠ 0) (x y : Plane) :
    ‖(triangleInterp a b c a' b' c' x - x) - (triangleInterp a b c a' b' c' y - y)‖ ≤
      4 * δ / minHeight a b c * ‖x - y‖ := by
  have e : (triangleInterp a b c a' b' c' x - x) - (triangleInterp a b c a' b' c' y - y) =
      interpLinear (b - a) (c - a) (b' - a') (c' - a') (x - y) - (x - y) := by
    simp only [triangleInterp_apply, map_sub]
    abel
  rw [e]
  exact norm_interpLinear_sub_le ha hb hc h (x - y)

/-- The affine interpolation maps the triangle onto the triangle of the displaced vertices. -/
theorem image_convexHull_triangleInterp (h : cross (b - a) (c - a) ≠ 0) :
    triangleInterp a b c a' b' c' '' convexHull ℝ {a, b, c} = convexHull ℝ {a', b', c'} := by
  rw [AffineMap.image_convexHull, image_insert_eq, image_insert_eq, image_singleton,
    triangleInterp_left, triangleInterp_mid h, triangleInterp_right h]

/-! ### Gluing affine maps over a triangulation -/

/-- The closed triangle `i` of a family with vertices `p i 0, p i 1, p i 2`. -/
def tri {ι : Type*} (p : ι → Fin 3 → Plane) (i : ι) : Set Plane :=
  convexHull ℝ {p i 0, p i 1, p i 2}

/-- The standing hypotheses on a triangulation of the plane: nondegenerate triangles, locally
finite, covering the plane, two distinct triangles meeting inside the convex hull of their common
vertices (a common face, possibly empty). -/
structure IsTriangulation {ι : Type*} (p : ι → Fin 3 → Plane) : Prop where
  nondeg : ∀ i, cross (p i 1 - p i 0) (p i 2 - p i 0) ≠ 0
  locallyFinite : LocallyFinite (tri p)
  cover : ⋃ i, tri p i = univ
  inter : ∀ i j, i ≠ j →
    tri p i ∩ tri p j ⊆ convexHull ℝ ({p i 0, p i 1, p i 2} ∩ {p j 0, p j 1, p j 2})

variable {ι : Type*} {p : ι → Fin 3 → Plane}

theorem isClosed_tri (i : ι) : IsClosed (tri p i) :=
  (Set.toFinite ({p i 0, p i 1, p i 2} : Set Plane)).isClosed_convexHull ℝ

theorem convex_tri (i : ι) : Convex ℝ (tri p i) :=
  convex_convexHull ℝ _

/-- The affine map on triangle `i` taking each vertex `v` to `v + σ v`. -/
def triInterp (p : ι → Fin 3 → Plane) (σ : Plane → Plane) (i : ι) : Plane →ᵃ[ℝ] Plane :=
  triangleInterp (p i 0) (p i 1) (p i 2) (p i 0 + σ (p i 0)) (p i 1 + σ (p i 1))
    (p i 2 + σ (p i 2))

theorem triInterp_vertex (hT : IsTriangulation p) (σ : Plane → Plane) (i : ι) {v : Plane}
    (hv : v ∈ ({p i 0, p i 1, p i 2} : Set Plane)) : triInterp p σ i v = v + σ v := by
  rcases hv with rfl | rfl | rfl
  · exact triangleInterp_left
  · exact triangleInterp_mid (hT.nondeg i)
  · exact triangleInterp_right (hT.nondeg i)

theorem triInterp_eq_of_mem (hT : IsTriangulation p) (σ : Plane → Plane) {i j : ι} {x : Plane}
    (hi : x ∈ tri p i) (hj : x ∈ tri p j) : triInterp p σ i x = triInterp p σ j x := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hx := hT.inter i j hij ⟨hi, hj⟩
  have hconv := (convex_singleton (0 : Plane)).affine_preimage (triInterp p σ i - triInterp p σ j)
  have hsub : ({p i 0, p i 1, p i 2} ∩ {p j 0, p j 1, p j 2} : Set Plane) ⊆
      (triInterp p σ i - triInterp p σ j) ⁻¹' {0} := by
    intro v hv
    rw [mem_preimage, AffineMap.coe_sub, Pi.sub_apply, mem_singleton_iff, sub_eq_zero,
      triInterp_vertex hT σ i hv.1, triInterp_vertex hT σ j hv.2]
  have := convexHull_min hsub hconv hx
  rwa [mem_preimage, AffineMap.coe_sub, Pi.sub_apply, mem_singleton_iff, sub_eq_zero] at this

theorem exists_tri (hT : IsTriangulation p) (x : Plane) : ∃ i, x ∈ tri p i :=
  mem_iUnion.1 (by rw [hT.cover]; trivial)

/-- **The glued piecewise affine map**: on each triangle, the affine interpolation of the vertex
displacement `σ`. -/
def plMap (hT : IsTriangulation p) (σ : Plane → Plane) (x : Plane) : Plane :=
  triInterp p σ (Classical.choose (exists_tri hT x)) x

theorem plMap_eq (hT : IsTriangulation p) (σ : Plane → Plane) {i : ι} {x : Plane}
    (hx : x ∈ tri p i) :
    plMap hT σ x = triInterp p σ i x :=
  triInterp_eq_of_mem hT σ (Classical.choose_spec (exists_tri hT x)) hx

theorem continuous_plMap (hT : IsTriangulation p) (σ : Plane → Plane) : Continuous (plMap hT σ) :=
  hT.locallyFinite.continuous hT.cover isClosed_tri fun i =>
    ((triInterp p σ i).continuous_of_finiteDimensional.continuousOn).congr fun _ hx =>
      plMap_eq hT σ hx

theorem plMap_vertex (hT : IsTriangulation p) (σ : Plane → Plane) (i : ι) (k : Fin 3) :
    plMap hT σ (p i k) = p i k + σ (p i k) := by
  have hk : p i k ∈ ({p i 0, p i 1, p i 2} : Set Plane) := by
    fin_cases k <;> simp
  rw [plMap_eq hT σ (subset_convexHull ℝ _ hk), triInterp_vertex hT σ i hk]

theorem norm_vertex_sub_le {σ : Plane → Plane} {δ : ι → ℝ} (hσ : ∀ i k, ‖σ (p i k)‖ ≤ δ i) (i : ι)
    (k : Fin 3) : ‖p i k + σ (p i k) - p i k‖ ≤ δ i := by
  rw [add_sub_cancel_left]
  exact hσ i k

/-- On triangle `i`, the glued map moves points by at most a bound `δ i` of the displacements of
the vertices of that triangle. -/
theorem norm_plMap_sub_le (hT : IsTriangulation p) (σ : Plane → Plane) {δ : ι → ℝ}
    (hσ : ∀ i k, ‖σ (p i k)‖ ≤ δ i) {i : ι} {x : Plane} (hx : x ∈ tri p i) :
    ‖plMap hT σ x - x‖ ≤ δ i := by
  rw [plMap_eq hT σ hx]
  exact norm_triangleInterp_sub_le (norm_vertex_sub_le hσ i 0) (norm_vertex_sub_le hσ i 1)
    (norm_vertex_sub_le hσ i 2) (hT.nondeg i) hx

/-- **The glued map minus the identity is Lipschitz**, with constant `L` as soon as
`4 δ i / minHeight ≤ L` on every triangle `i`, where `δ i` bounds the displacements of the vertices
of triangle `i`. -/
theorem lipschitzWith_plMap_sub (hT : IsTriangulation p) (σ : Plane → Plane) {δ : ι → ℝ} {L : ℝ≥0}
    (hσ : ∀ i k, ‖σ (p i k)‖ ≤ δ i)
    (hL : ∀ i, 4 * δ i / minHeight (p i 0) (p i 1) (p i 2) ≤ L) :
    LipschitzWith L fun x => plMap hT σ x - x := by
  refine lipschitzWith_of_locallyFinite_convex hT.locallyFinite isClosed_tri convex_tri hT.cover
    ((continuous_plMap hT σ).sub continuous_id) fun i x hx y hy => ?_
  show dist (plMap hT σ x - x) (plMap hT σ y - y) ≤ L * dist x y
  rw [dist_eq_norm, dist_eq_norm, plMap_eq hT σ hx, plMap_eq hT σ hy]
  exact (norm_triangleInterp_sub_sub_le (norm_vertex_sub_le hσ i 0) (norm_vertex_sub_le hσ i 1)
    (norm_vertex_sub_le hσ i 2) (hT.nondeg i) x y).trans
    (mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _))

/-- **The piecewise affine homeomorphism**: the glued map, once `plMap - id` is `L`-Lipschitz with
`L < 1`. -/
def plHomeomorph (hT : IsTriangulation p) (σ : Plane → Plane) {L : ℝ≥0}
    (hL : LipschitzWith L fun x => plMap hT σ x - x) (hK : L < 1) : Plane ≃ₜ Plane :=
  homeomorphAddOfLipschitzWith hK hL

@[simp]
theorem plHomeomorph_apply (hT : IsTriangulation p) (σ : Plane → Plane) {L : ℝ≥0}
    (hL : LipschitzWith L fun x => plMap hT σ x - x) (hK : L < 1) (x : Plane) :
    plHomeomorph hT σ hL hK x = plMap hT σ x := by
  rw [plHomeomorph, homeomorphAddOfLipschitzWith_apply]
  abel

/-- A map agreeing with the affine interpolation on each triangle maps each segment inside a
triangle onto the segment between the images of its endpoints. -/
theorem image_segment_of_eq_triInterp (σ : Plane → Plane) {f : Plane → Plane}
    (hf : ∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) {i : ι} {x y : Plane} (hx : x ∈ tri p i)
    (hy : y ∈ tri p i) : f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  have hs : segment ℝ x y ⊆ tri p i := (convex_tri i).segment_subset hx hy
  rw [image_congr fun z hz => hf i z (hs hz), image_segment, hf i x hx, hf i y hy]

/-- A map agreeing with the affine interpolation on each triangle maps each triangle onto the
triangle of the displaced vertices. -/
theorem image_tri_of_eq_triInterp (hT : IsTriangulation p) (σ : Plane → Plane) {f : Plane → Plane}
    (hf : ∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) (i : ι) :
    f '' tri p i =
      convexHull ℝ {p i 0 + σ (p i 0), p i 1 + σ (p i 1), p i 2 + σ (p i 2)} := by
  rw [image_congr fun z hz => hf i z hz]
  exact image_convexHull_triangleInterp (hT.nondeg i)

/-- A map agreeing with the affine interpolation on each triangle maps each union of triangles (a
polygon of the triangulation) onto the union of the displaced triangles. -/
theorem image_biUnion_tri_of_eq_triInterp (hT : IsTriangulation p) (σ : Plane → Plane)
    {f : Plane → Plane} (hf : ∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) (s : Set ι) :
    f '' ⋃ i ∈ s, tri p i =
      ⋃ i ∈ s, convexHull ℝ {p i 0 + σ (p i 0), p i 1 + σ (p i 1), p i 2 + σ (p i 2)} := by
  rw [image_iUnion₂]
  exact iUnion₂_congr fun i _ => image_tri_of_eq_triInterp hT σ hf i

/-- **A piecewise affine homeomorphism of the plane close to the identity.** Let `p` be a
triangulation of the plane and `σ` a vertex displacement with `‖σ v‖ ≤ δ i` at the vertices `v` of
triangle `i`. Suppose `4 δ i / minHeight ≤ L` on every triangle `i`, with `L < 1`, and `δ i ≤ δ₀`
for every `i`. Then there is a homeomorphism `f` of the plane which is the affine interpolation of
the displaced vertices on each triangle (so `f v = v + σ v` at each vertex, `f` is the identity on
each triangle with fixed vertices, and `f` maps each triangle onto the displaced triangle), which
moves the points of triangle `i` by at most `δ i` and every point by at most `δ₀` (as does its
inverse), and for which `f - id` is `L`-Lipschitz. -/
theorem exists_homeomorph_piecewiseAffine (hT : IsTriangulation p) (σ : Plane → Plane)
    {δ : ι → ℝ} {δ₀ : ℝ} {L : ℝ≥0} (hσ : ∀ i k, ‖σ (p i k)‖ ≤ δ i)
    (hL : ∀ i, 4 * δ i / minHeight (p i 0) (p i 1) (p i 2) ≤ L) (hK : L < 1)
    (hδ₀ : ∀ i, δ i ≤ δ₀) :
    ∃ f : Plane ≃ₜ Plane, (∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) ∧
      (∀ i k, f (p i k) = p i k + σ (p i k)) ∧
      (∀ i, (∀ k, σ (p i k) = 0) → ∀ x ∈ tri p i, f x = x) ∧
      (∀ i, ∀ x ∈ tri p i, dist x (f x) ≤ δ i) ∧
      (∀ x, dist x (f x) ≤ δ₀) ∧ (∀ y, dist y (f.symm y) ≤ δ₀) ∧
      LipschitzWith L (fun x => f x - x) ∧
      ∀ i, f '' tri p i =
        convexHull ℝ {p i 0 + σ (p i 0), p i 1 + σ (p i 1), p i 2 + σ (p i 2)} := by
  have hLip := lipschitzWith_plMap_sub hT σ hσ hL
  have hf : ∀ i, ∀ x ∈ tri p i, plHomeomorph hT σ hLip hK x = triInterp p σ i x :=
    fun i x hx => by rw [plHomeomorph_apply, plMap_eq hT σ hx]
  have hdisp : ∀ x, ‖plMap hT σ x - x‖ ≤ δ₀ := by
    intro x
    obtain ⟨i, hi⟩ := exists_tri hT x
    exact (norm_plMap_sub_le hT σ hσ hi).trans (hδ₀ i)
  have hfun : (fun x => plHomeomorph hT σ hLip hK x - x) = fun x => plMap hT σ x - x :=
    funext fun x => by rw [plHomeomorph_apply]
  refine ⟨plHomeomorph hT σ hLip hK, hf, fun i k => ?_, fun i hi x hx => ?_, fun i x hx => ?_,
    dist_homeomorphAddOfLipschitzWith_le hK hLip hdisp,
    dist_symm_homeomorphAddOfLipschitzWith_le hK hLip hdisp, hfun ▸ hLip,
    image_tri_of_eq_triInterp hT σ hf⟩
  · rw [plHomeomorph_apply, plMap_vertex]
  · have h0 : ‖plMap hT σ x - x‖ ≤ 0 := by
      rw [plMap_eq hT σ hx]
      refine norm_triangleInterp_sub_le ?_ ?_ ?_ (hT.nondeg i) hx <;> simp [hi]
    rw [norm_le_zero_iff, sub_eq_zero] at h0
    rw [plHomeomorph_apply, h0]
  · rw [plHomeomorph_apply, dist_comm, dist_eq_norm]
    exact norm_plMap_sub_le hT σ hσ hx

/-- **The uniform form**: if `‖σ‖ ≤ δ` at every vertex, every triangle with a moved vertex has
minimal height at least `h`, and `4 δ < h`, the piecewise affine homeomorphism and its inverse move
points by at most `δ` and `f - id` is `4 δ / h`-Lipschitz. Both bounds tend to zero with `δ` for a
fixed triangulation with finitely many moved vertices. -/
theorem exists_homeomorph_piecewiseAffine_of_le_minHeight (hT : IsTriangulation p)
    (σ : Plane → Plane) {δ h : ℝ} (hh : 0 < h) (hσ : ∀ i k, ‖σ (p i k)‖ ≤ δ)
    (hmin : ∀ i, (∃ k, σ (p i k) ≠ 0) → h ≤ minHeight (p i 0) (p i 1) (p i 2))
    (hδ : 4 * δ < h) :
    ∃ f : Plane ≃ₜ Plane, (∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) ∧
      (∀ x, dist x (f x) ≤ δ) ∧ (∀ y, dist y (f.symm y) ≤ δ) ∧
      LipschitzWith (4 * δ / h).toNNReal (fun x => f x - x) := by
  classical
  obtain ⟨i₀, -⟩ := exists_tri hT 0
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hσ i₀ 0)
  have hq0 : 0 ≤ 4 * δ / h := div_nonneg (by linarith) hh.le
  let δi : ι → ℝ := fun i => if ∀ k, σ (p i k) = 0 then 0 else δ
  have hσi : ∀ i k, ‖σ (p i k)‖ ≤ δi i := by
    intro i k
    show ‖σ (p i k)‖ ≤ if ∀ k, σ (p i k) = 0 then 0 else δ
    split_ifs with hi
    · rw [hi k, norm_zero]
    · exact hσ i k
  have hLi : ∀ i, 4 * δi i / minHeight (p i 0) (p i 1) (p i 2) ≤ (4 * δ / h).toNNReal := by
    intro i
    rw [Real.coe_toNNReal _ hq0]
    show 4 * (if ∀ k, σ (p i k) = 0 then 0 else δ) / minHeight (p i 0) (p i 1) (p i 2) ≤
      4 * δ / h
    split_ifs with hi
    · rw [mul_zero, zero_div]
      exact hq0
    · exact div_le_div_of_nonneg_left (by linarith) hh (hmin i (not_forall.1 hi))
  have hδi : ∀ i, δi i ≤ δ := fun i => by
    show (if ∀ k, σ (p i k) = 0 then 0 else δ) ≤ δ
    split_ifs
    · exact hδ0
    · exact le_rfl
  obtain ⟨f, hf, -, -, -, hd, hd', hLf, -⟩ := exists_homeomorph_piecewiseAffine hT σ hσi hLi
    (Real.toNNReal_lt_one.2 ((div_lt_one hh).2 hδ)) hδi
  exact ⟨f, hf, hd, hd', hLf⟩

end MatedCRT.ZeroConePolygonal
