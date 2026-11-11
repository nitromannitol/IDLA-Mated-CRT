import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaEdge

/-! # Finite nets for Hölder-bounded functions on a compact set

Functions `h : ℂ → ℝ` with `|h| ≤ m` and the Hölder bound `|h x - h y| ≤ m dist(x, y)^α` on a compact `K`
are uniformly `δ`-approximated on `K` by one of finitely many functions. The approximants are step functions on
a finite net of `K`, with integer values on a grid of mesh `δ/4`. This total boundedness supplies the finite nets
of the Hölder classes in the measurable selection of `OdometerMeasurableSelectionStep`. -/

namespace MatedCRT

open Set Metric Filter Topology

theorem holder_finite_net {K : Set ℂ} (hK : IsCompact K) {m α : ℝ} (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset (ℂ → ℝ), ∀ h : ℂ → ℝ, (∀ x ∈ K, |h x| ≤ m) →
      (∀ x ∈ K, ∀ y ∈ K, |h x - h y| ≤ m * dist x y ^ α) →
      ∃ c ∈ F, ∀ x ∈ K, |h x - c x| < δ := by
  classical
  have hs : (0 : ℝ) < 4 / δ := by positivity
  obtain ⟨δ', hδ'pos, hδ'α⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ^ α = δ / (4 * (|m| + 1)) :=
    ⟨(δ / (4 * (|m| + 1))) ^ α⁻¹, by positivity, Real.rpow_inv_rpow (by positivity) hα.ne'⟩
  have hsmall : |m| * (δ / (4 * (|m| + 1))) ≤ δ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg m]
  obtain ⟨X, hXK, hXfin, hcov⟩ := finite_cover_balls_of_compact hK hδ'pos
  have hπ : ∀ y : ℂ, ∃ x : ℂ, (y ∈ K → x ∈ X ∧ dist y x < δ') := by
    intro y
    by_cases hy : y ∈ K
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcov hy)
      exact ⟨x, fun _ => ⟨hx, mem_ball.mp hyx⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose π hπ using hπ
  obtain ⟨M, hM⟩ : ∃ M : ℤ, |m| * (4 / δ) + 1 ≤ M :=
    ⟨⌈|m| * (4 / δ)⌉ + 1, by push_cast; linarith [Int.le_ceil (|m| * (4 / δ))]⟩
  let Xf : Finset ℂ := hXfin.toFinset
  have hXf : ∀ x, x ∈ Xf ↔ x ∈ X := fun x => hXfin.mem_toFinset
  let F : Finset (ℂ → ℝ) := (Fintype.piFinset fun _ : Xf => Finset.Icc (-M) M).image
    (fun σ : Xf → ℤ => fun y : ℂ => δ / 4 * (if hy : π y ∈ Xf then (σ ⟨π y, hy⟩ : ℝ) else 0))
  refine ⟨F, fun h hbd hhol => ?_⟩
  have hσ : (fun x : Xf => ⌊h x * (4 / δ)⌋) ∈ Fintype.piFinset fun _ : Xf => Finset.Icc (-M) M := by
    rw [Fintype.mem_piFinset]
    intro x
    have hxK : (x : ℂ) ∈ K := hXK ((hXf x.1).mp x.2)
    obtain ⟨hl, hu⟩ := abs_le.mp (hbd x hxK)
    have hx1 : -|m| ≤ h x := by linarith [le_abs_self m]
    have hx2 : h x ≤ |m| := by linarith [le_abs_self m]
    have hl' : -|m| * (4 / δ) ≤ h x * (4 / δ) := mul_le_mul_of_nonneg_right hx1 hs.le
    have hu' : h x * (4 / δ) ≤ |m| * (4 / δ) := mul_le_mul_of_nonneg_right hx2 hs.le
    show ⌊h x * (4 / δ)⌋ ∈ Finset.Icc (-M) M
    rw [Finset.mem_Icc]
    have f1 := Int.lt_floor_add_one (h x * (4 / δ))
    have f2 := Int.floor_le (h x * (4 / δ))
    constructor
    · have : ((-M : ℤ) : ℝ) < ((⌊h x * (4 / δ)⌋ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
    · have : ((⌊h x * (4 / δ)⌋ : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  refine ⟨(fun σ : Xf → ℤ => fun y : ℂ => δ / 4 * (if hy : π y ∈ Xf then (σ ⟨π y, hy⟩ : ℝ) else 0))
    (fun x : Xf => ⌊h x * (4 / δ)⌋), Finset.mem_image_of_mem _ hσ, ?_⟩
  intro y hy
  obtain ⟨hxX, hdist⟩ := hπ y hy
  have hxXf : π y ∈ Xf := (hXf _).mpr hxX
  have hxK : π y ∈ K := hXK hxX
  have hHolder : |h y - h (π y)| ≤ δ / 4 := by
    have h1 := hhol y hy (π y) hxK
    have hd : dist y (π y) ^ α ≤ δ' ^ α := Real.rpow_le_rpow dist_nonneg hdist.le hα.le
    have h2 : m * dist y (π y) ^ α ≤ |m| * dist y (π y) ^ α :=
      mul_le_mul_of_nonneg_right (le_abs_self m) (by positivity)
    have h3 : |m| * dist y (π y) ^ α ≤ |m| * δ' ^ α := mul_le_mul_of_nonneg_left hd (abs_nonneg m)
    rw [hδ'α] at h3
    linarith
  have hGrid : |h (π y) - δ / 4 * ((⌊h (π y) * (4 / δ)⌋ : ℤ) : ℝ)| < δ / 4 := by
    have hwd : δ / 4 * (h (π y) * (4 / δ)) = h (π y) := by field_simp
    have f1 := Int.floor_le (h (π y) * (4 / δ))
    have f2 := Int.lt_floor_add_one (h (π y) * (4 / δ))
    have g1 := mul_le_mul_of_nonneg_left f1 (by positivity : (0 : ℝ) ≤ δ / 4)
    have g2 := mul_lt_mul_of_pos_left f2 (by positivity : (0 : ℝ) < δ / 4)
    rw [abs_lt]
    constructor <;> nlinarith
  simp only [hxXf, ↓reduceDIte]
  show |h y - δ / 4 * ((⌊h (π y) * (4 / δ)⌋ : ℤ) : ℝ)| < δ
  calc |h y - δ / 4 * ((⌊h (π y) * (4 / δ)⌋ : ℤ) : ℝ)|
      ≤ |h y - h (π y)| + |h (π y) - δ / 4 * ((⌊h (π y) * (4 / δ)⌋ : ℤ) : ℝ)| := abs_sub_le _ _ _
    _ < δ := by linarith


/-- The Hölder class on `K`: `|h| ≤ m` and `|h x - h y| ≤ m dist(x, y)^α` for `x, y ∈ K`. -/
def HolderClassOn (K : Set ℂ) (m α : ℝ) (h : ℂ → ℝ) : Prop :=
  (∀ x ∈ K, |h x| ≤ m) ∧ (∀ x ∈ K, ∀ y ∈ K, |h x - h y| ≤ m * dist x y ^ α)

/-- Finite `δ`-nets of the Hölder class whose centres belong to the class. The nets are used for the selection of
subsequences in `OdometerMeasurableSelectionStep`; the closedness of the class gives the limits. -/
theorem holder_finite_net_in_class {K : Set ℂ} (hK : IsCompact K) {m α : ℝ} (hα : 0 < α) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ F : Finset (ℂ → ℝ), (∀ c ∈ F, HolderClassOn K m α c) ∧
      ∀ h : ℂ → ℝ, HolderClassOn K m α h → ∃ c ∈ F, ∀ x ∈ K, |h x - c x| < δ := by
  classical
  obtain ⟨F₀, hF₀⟩ := holder_finite_net hK hα (half_pos hδ)
  let P : (ℂ → ℝ) → Prop := fun c =>
    ∃ h : ℂ → ℝ, HolderClassOn K m α h ∧ ∀ x ∈ K, |h x - c x| < δ / 2
  have hrep : ∀ c : ℂ → ℝ, ∃ h : ℂ → ℝ, P c →
      HolderClassOn K m α h ∧ ∀ x ∈ K, |h x - c x| < δ / 2 := by
    intro c
    by_cases hc : P c
    · obtain ⟨h, hh, hd⟩ := hc
      exact ⟨h, fun _ => ⟨hh, hd⟩⟩
    · exact ⟨c, fun h => absurd h hc⟩
  choose rep hrep using hrep
  refine ⟨(F₀.filter P).image rep, ?_, ?_⟩
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc
    exact (hrep c₀ (Finset.mem_filter.mp hc₀).2).1
  · intro h hh
    obtain ⟨c₀, hc₀, hd₀⟩ := hF₀ h hh.1 hh.2
    have hPc₀ : P c₀ := ⟨h, hh, hd₀⟩
    refine ⟨rep c₀, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hc₀, hPc₀⟩), fun x hx => ?_⟩
    have h1 := hd₀ x hx
    have h2 := (hrep c₀ hPc₀).2 x hx
    have h3 := abs_sub_le (h x) (c₀ x) (rep c₀ x)
    rw [abs_sub_comm (c₀ x)] at h3
    linarith


/-- The Hölder class on `K` is closed under pointwise limits on `K`. -/
theorem holderClassOn_of_tendsto {K : Set ℂ} {m α : ℝ} {h : ℕ → ℂ → ℝ} {w : ℂ → ℝ}
    (hh : ∀ k, HolderClassOn K m α (h k)) (hw : ∀ x ∈ K, Tendsto (fun k => h k x) atTop (𝓝 (w x))) :
    HolderClassOn K m α w := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact le_of_tendsto (hw x hx).abs (Eventually.of_forall fun k => (hh k).1 x hx)
  · exact le_of_tendsto ((hw x hx).sub (hw y hy)).abs
      (Eventually.of_forall fun k => (hh k).2 x hx y hy)

/-- A function in the Hölder class on `K` is continuous on `K`. -/
theorem holderClassOn_continuousOn {K : Set ℂ} {m α : ℝ} (hα : 0 < α) {h : ℂ → ℝ}
    (hh : HolderClassOn K m α h) : ContinuousOn h K := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ α = ε / (2 * (|m| + 1)) :=
    ⟨(ε / (2 * (|m| + 1))) ^ α⁻¹, by positivity, Real.rpow_inv_rpow (by positivity) hα.ne'⟩
  refine ⟨δ, hδpos, fun {y} hy hyx => ?_⟩
  rw [Real.dist_eq]
  have h1 := hh.2 y hy x hx
  have hd : dist y x ^ α ≤ δ ^ α := Real.rpow_le_rpow dist_nonneg (le_of_lt (by simpa [dist_comm] using hyx)) hα.le
  have h2 : m * dist y x ^ α ≤ |m| * dist y x ^ α :=
    mul_le_mul_of_nonneg_right (le_abs_self m) (by positivity)
  have h3 : |m| * dist y x ^ α ≤ |m| * δ ^ α := mul_le_mul_of_nonneg_left hd (abs_nonneg m)
  rw [hδ] at h3
  have h4 : |m| * (ε / (2 * (|m| + 1))) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg m]
  linarith

/-- The Hölder class on a compact set has a countable dense subset of centres in the class. -/
theorem exists_countable_holder_dense {K : Set ℂ} (hK : IsCompact K) {m α : ℝ} (hα : 0 < α) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ (∀ c ∈ D, HolderClassOn K m α c) ∧
      ∀ h : ℂ → ℝ, HolderClassOn K m α h → ∀ ε : ℝ, 0 < ε → ∃ c ∈ D, ∀ x ∈ K, |h x - c x| < ε := by
  classical
  have hnet : ∀ j : ℕ, ∃ F : Finset (ℂ → ℝ), (∀ c ∈ F, HolderClassOn K m α c) ∧
      ∀ h : ℂ → ℝ, HolderClassOn K m α h → ∃ c ∈ F, ∀ x ∈ K, |h x - c x| < 1 / ((j : ℝ) + 1) :=
    fun j => holder_finite_net_in_class hK hα (by positivity)
  choose F hF using hnet
  refine ⟨⋃ j, (F j : Set (ℂ → ℝ)), Set.countable_iUnion fun j => (F j).countable_toSet, ?_, ?_⟩
  · intro c hc
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
    exact (hF j).1 c hj
  · intro h hh ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    obtain ⟨c, hc, hd⟩ := (hF j).2 h hh
    exact ⟨c, Set.mem_iUnion.mpr ⟨j, hc⟩, fun x hx => lt_trans (hd x hx) hj⟩

end MatedCRT
