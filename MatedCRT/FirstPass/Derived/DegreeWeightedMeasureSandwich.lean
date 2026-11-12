import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCells

/-!
# The degree-weighted measure on a ball from the degree-weighted counting bound

The deterministic step from BG20 Lemma A.5 to BG20 Corollary A.6 on a ball `D = B_r`. Let `f` be
continuous and vanish off `B_ρ` with `ρ + ε^α ≤ r`. Lemma A.5 holds for every choice of the points
`w_a ∈ H^ε_a ∩ cl(D)`; choosing them where a nonnegative `f` is maximal, respectively minimal, on the
cell `H^ε_a` (a cell meeting `D` and its complement meets the sphere `∂D`, where `f` vanishes) bounds
`∫ f dμ^ε_h = ∑_a deg^ε(a) ∫_{H^ε_a} f dμ_h` from above and from below by the two counting sums of
Lemma A.5. Each of them is within `ε^α` of `6 ∫ f dμ_h`, hence so is `∫ f dμ^ε_h`. No modulus of
continuity of `f` and no bound on the degrees enters.

* `eq_zero_of_notMem_ball_diff_thickening_frontier`;
* `IsAreaParametrized.mul_le_setIntegral_cell`, `IsAreaParametrized.setIntegral_cell_le_mul`;
* `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le_of_nonneg`: `f ≥ 0`, error `ε^α`;
* `IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le_of_ball`: signed `f`, applying
  Lemma A.5 to `f⁺` and `f⁻`, error `2 ε^α`.
-/

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}

/-- A function vanishing off `B_ρ` vanishes off `B_r \ B_s(∂B_r)` when `0 ≤ s` and `ρ + s ≤ r`. -/
theorem eq_zero_of_notMem_ball_diff_thickening_frontier {f : ℂ → ℝ} {ρ r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (hρ : ρ + s ≤ r) (hf : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0) :
    ∀ x ∉ ball (0 : ℂ) r \ thickening s (frontier (ball (0 : ℂ) r)), f x = 0 := by
  intro x hx
  by_contra hfx
  have hxρ : x ∈ ball (0 : ℂ) ρ := by_contra fun h => hfx (hf x h)
  apply hx
  refine ⟨ball_subset_ball (by linarith) hxρ, ?_⟩
  rw [frontier_ball (0 : ℂ) hr.ne', mem_thickening_iff]
  rintro ⟨z, hz, hxz⟩
  rw [mem_sphere_zero_iff_norm] at hz
  rw [mem_ball_zero_iff] at hxρ
  rw [dist_eq_norm] at hxz
  have h := norm_sub_norm_le z x
  rw [norm_sub_rev] at h
  linarith

/-- `ε` times the value of `g` at a point where it is minimal on a cell is at most the integral of
`g` over the cell. -/
theorem IsAreaParametrized.mul_le_setIntegral_cell (hpar : IsAreaParametrized μ η) (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : Continuous g) {k : ℤ} {w : ℂ} (hw : ∀ x ∈ cell ε η k, g w ≤ g x) :
    ε * g w ≤ ∫ x in cell ε η k, g x ∂μ := by
  have hm : MeasurableSet (cell ε η k) := (isCompact_cell hpar.1 ε k).isClosed.measurableSet
  have hμ : μ.real (cell ε η k) = ε := by
    rw [measureReal_def, hpar.measure_cell hε, ENNReal.toReal_ofReal hε.le]
  calc ε * g w = ∫ _ in cell ε η k, g w ∂μ := by rw [setIntegral_const, hμ, smul_eq_mul]
    _ ≤ ∫ x in cell ε η k, g x ∂μ :=
      setIntegral_mono_on (hpar.integrableOn_cell (f := fun _ => g w) hε continuous_const k)
        (hpar.integrableOn_cell hε hg k) hm hw

/-- The integral of `g` over a cell is at most `ε` times the value of `g` at a point where it is
maximal on the cell. -/
theorem IsAreaParametrized.setIntegral_cell_le_mul (hpar : IsAreaParametrized μ η) (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : Continuous g) {k : ℤ} {w : ℂ} (hw : ∀ x ∈ cell ε η k, g x ≤ g w) :
    ∫ x in cell ε η k, g x ∂μ ≤ ε * g w := by
  have hm : MeasurableSet (cell ε η k) := (isCompact_cell hpar.1 ε k).isClosed.measurableSet
  have hμ : μ.real (cell ε η k) = ε := by
    rw [measureReal_def, hpar.measure_cell hε, ENNReal.toReal_ofReal hε.le]
  calc ∫ x in cell ε η k, g x ∂μ ≤ ∫ _ in cell ε η k, g w ∂μ :=
      setIntegral_mono_on (hpar.integrableOn_cell hε hg k)
        (hpar.integrableOn_cell (f := fun _ => g w) hε continuous_const k) hm hw
    _ = ε * g w := by rw [setIntegral_const, hμ, smul_eq_mul]

/-- **BG20 Lemma A.5 ⇒ Corollary A.6 on a ball, nonnegative `f`.** Let `g ≥ 0` be continuous and
vanish off `B_ρ`, `ρ + ε^α ≤ r`, `t = V^ε(B_r)` finite, and let the two-sided degree-weighted counting
bound of Lemma A.5 hold for `g` on `D = B_r` for every choice of points `w_k ∈ H^ε_k ∩ cl(D)`. Then
`|∫ g dμ^ε_h - 6 ∫ g dμ_h| ≤ ε^α`. -/
theorem IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le_of_nonneg
    (hpar : IsAreaParametrized μ η) (hε : 0 < ε) {α ρ r : ℝ} (hr : 0 < r) (hρ : ρ + ε ^ α ≤ r)
    (t : Finset ℤ) (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η (ball 0 r))
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgρ : ∀ x ∉ ball (0 : ℂ) ρ, g x = 0)
    (hA5 : ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k ∩ closure (ball 0 r)) →
      6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂μ - ε ^ (-1 + α) ≤
          ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ∧
        ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂μ + ε ^ (-1 + α)) :
    |∫ x, g x ∂degreeWeightedMeasure m ε η μ - 6 * ∫ x, g x ∂μ| ≤ ε ^ α := by
  set D : Set ℂ := ball 0 r with hD_def
  have hs : 0 < ε ^ α := Real.rpow_pos_of_pos hε α
  have hgD : ∀ x ∉ D, g x = 0 := fun x hx =>
    hgρ x fun h => hx (ball_subset_ball (by linarith) h)
  have hcellD : ∀ k ∈ t, (cell ε η k ∩ closure D).Nonempty := fun k hk => by
    obtain ⟨y, hy1, hy2⟩ := (ht k).1 hk
    exact ⟨y, hy1, subset_closure hy2⟩
  have hcpt : ∀ k, IsCompact (cell ε η k ∩ closure D) := fun k =>
    (isCompact_cell hpar.1 ε k).inter_right isClosed_closure
  have hmax : ∀ k, ∃ w : ℂ, k ∈ t → w ∈ cell ε η k ∩ closure D ∧ ∀ x ∈ cell ε η k, g x ≤ g w := by
    intro k
    by_cases hk : k ∈ t
    · obtain ⟨w, hw, hwmax⟩ := (hcpt k).exists_isMaxOn (hcellD k hk) hg.continuousOn
      refine ⟨w, fun _ => ⟨hw, fun x hx => ?_⟩⟩
      by_cases hxD : x ∈ D
      · exact hwmax ⟨hx, subset_closure hxD⟩
      · rw [hgD x hxD]
        exact hg0 w
    · exact ⟨0, fun h => absurd h hk⟩
  have hmin : ∀ k, ∃ w : ℂ, k ∈ t → w ∈ cell ε η k ∩ closure D ∧ ∀ x ∈ cell ε η k, g w ≤ g x := by
    intro k
    by_cases hk : k ∈ t
    · obtain ⟨w, hw, hwmin⟩ := (hcpt k).exists_isMinOn (hcellD k hk) hg.continuousOn
      by_cases hsub : cell ε η k ⊆ closure D
      · exact ⟨w, fun _ => ⟨hw, fun x hx => hwmin ⟨hx, hsub hx⟩⟩⟩
      · -- the cell meets `D` and the complement of `cl(D)`, hence the sphere `‖z‖ = r`
        obtain ⟨y, hyc, hyD⟩ := (ht k).1 hk
        obtain ⟨x₀, hx₀c, hx₀D⟩ := not_subset.1 hsub
        have hconn : IsPreconnected (cell ε η k) :=
          isPreconnected_Icc.image η hpar.1.continuousOn
        have hy : ‖y‖ < r := mem_ball_zero_iff.1 hyD
        have hclD : closure D = closedBall 0 r := closure_ball 0 hr.ne'
        have hx₀ : r < ‖x₀‖ := by
          rw [hclD, mem_closedBall_zero_iff, not_le] at hx₀D
          exact hx₀D
        obtain ⟨z, hzc, hz⟩ := hconn.intermediate_value hyc hx₀c continuous_norm.continuousOn
          (show r ∈ Icc ‖y‖ ‖x₀‖ from ⟨hy.le, hx₀.le⟩)
        replace hz : ‖z‖ = r := hz
        have hzD : z ∉ D := by
          rw [hD_def, mem_ball_zero_iff, hz]
          exact lt_irrefl r
        refine ⟨z, fun _ => ⟨⟨hzc, ?_⟩, fun x _ => ?_⟩⟩
        · rw [hclD, mem_closedBall_zero_iff, hz]
        · rw [hgD z hzD]
          exact hg0 x
    · exact ⟨0, fun h => absurd h hk⟩
  choose wp hwp using hmax
  choose wm hwm using hmin
  have hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, g x = 0 := fun k hk x hx =>
    hgD x fun hxD => hk ((ht k).2 ⟨x, hx, hxD⟩)
  have hsum := integral_degreeWeightedMeasure_eq_sum (m := m) (μ := μ) hg hpar.1 t hvan
    (fun k _ => hpar.integrableOn_cell hε hg k)
  have hup : ∫ x, g x ∂degreeWeightedMeasure m ε η μ ≤
      ε * ∑ k ∈ t, (matedDeg m k : ℝ) * g (wp k) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have h := hpar.setIntegral_cell_le_mul hε hg (hwp k hk).2
    calc (matedDeg m k : ℝ) * ∫ x in cell ε η k, g x ∂μ ≤ (matedDeg m k : ℝ) * (ε * g (wp k)) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = ε * ((matedDeg m k : ℝ) * g (wp k)) := by ring
  have hlo : ε * ∑ k ∈ t, (matedDeg m k : ℝ) * g (wm k) ≤
      ∫ x, g x ∂degreeWeightedMeasure m ε η μ := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have h := hpar.mul_le_setIntegral_cell hε hg (hwm k hk).2
    calc ε * ((matedDeg m k : ℝ) * g (wm k)) = (matedDeg m k : ℝ) * (ε * g (wm k)) := by ring
      _ ≤ (matedDeg m k : ℝ) * ∫ x in cell ε η k, g x ∂μ :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have hf₁ := eq_zero_of_notMem_ball_diff_thickening_frontier hr hs.le hρ hgρ
  have hf₂ : ∀ x ∉ thickening (ε ^ α) D, g x = 0 := fun x hx =>
    hgD x fun h => hx (self_subset_thickening hs D h)
  have hp := hA5 wp fun k hk => (hwp k ((ht k).2 hk)).1
  have hm := hA5 wm fun k hk => (hwm k ((ht k).2 hk)).1
  have ep : ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (wp k) =
      ∑ k ∈ t, (matedDeg m k : ℝ) * g (wp k) :=
    tsum_cellVertices_eq_sum t ht (fun k => (matedDeg m k : ℝ) * g (wp k))
  have em : ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (wm k) =
      ∑ k ∈ t, (matedDeg m k : ℝ) * g (wm k) :=
    tsum_cellVertices_eq_sum t ht (fun k => (matedDeg m k : ℝ) * g (wm k))
  rw [ep] at hp
  rw [em] at hm
  have hp' := abs_mul_sub_six_integral_le_of_bounds hε hf₁ hf₂ hp.1 hp.2
  have hm' := abs_mul_sub_six_integral_le_of_bounds hε hf₁ hf₂ hm.1 hm.2
  rw [abs_le] at hp' hm' ⊢
  constructor <;> linarith [hp'.1, hp'.2, hm'.1, hm'.2]

/-- **BG20 Lemma A.5 ⇒ Corollary A.6 on a ball.** Let `f` be continuous, `|f| ≤ K`, `L`-Lipschitz and
vanishing off `B_ρ`, `ρ + ε^α ≤ r`, `t = V^ε(B_r)` finite, and let the two-sided degree-weighted
counting bound of Lemma A.5 on `D = B_r` hold for every nonnegative `g ≤ K` which is `L`-Lipschitz and
every choice of points `w_k ∈ H^ε_k ∩ cl(D)`. Then `|∫ f dμ^ε_h - 6 ∫ f dμ_h| ≤ 2 ε^α`. -/
theorem IsAreaParametrized.abs_integral_degreeWeightedMeasure_sub_six_le_of_ball
    (hpar : IsAreaParametrized μ η) (hε : 0 < ε) {α ρ r K L : ℝ} (hr : 0 < r) (hρ : ρ + ε ^ α ≤ r)
    (t : Finset ℤ) (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η (ball 0 r))
    {f : ℂ → ℝ} (hf : Continuous f) (hfK : ∀ x, |f x| ≤ K)
    (hfL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hfρ : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0)
    (hA5 : ∀ g : ℂ → ℝ, (∀ x, 0 ≤ g x ∧ |g x| ≤ K) → (∀ x y, |g x - g y| ≤ L * ‖x - y‖) →
      ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k ∩ closure (ball 0 r)) →
      6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂μ - ε ^ (-1 + α) ≤
          ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ∧
        ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂μ + ε ^ (-1 + α)) :
    |∫ x, f x ∂degreeWeightedMeasure m ε η μ - 6 * ∫ x, f x ∂μ| ≤ 2 * ε ^ α := by
  have hs : 0 < ε ^ α := Real.rpow_pos_of_pos hε α
  have hDρ : ball (0 : ℂ) ρ ⊆ ball 0 r := ball_subset_ball (by linarith)
  have hvan : ∀ {g : ℂ → ℝ}, (∀ x ∉ ball (0 : ℂ) ρ, g x = 0) → ∀ k ∉ t, ∀ x ∈ cell ε η k, g x = 0 :=
    fun hgρ k hk x hx => hgρ x fun hxρ => hk ((ht k).2 ⟨x, hx, hDρ hxρ⟩)
  have hcov : ∀ {g : ℂ → ℝ}, (∀ x ∉ ball (0 : ℂ) ρ, g x = 0) →
      ∀ x ∉ ⋃ k ∈ t, cell ε η k, g x = 0 := by
    intro g hgρ x hx
    by_contra hgx
    obtain ⟨k, hk⟩ := exists_mem_cell hpar.2.2.1 hε x
    have hxρ : x ∈ ball (0 : ℂ) ρ := by_contra fun h => hgx (hgρ x h)
    exact hx (mem_iUnion₂.2 ⟨k, (ht k).2 ⟨x, hk, hDρ hxρ⟩, hk⟩)
  have hintμ : ∀ {g : ℂ → ℝ}, Continuous g → (∀ x ∉ ball (0 : ℂ) ρ, g x = 0) → Integrable g μ :=
    fun hgc hgρ => (integrableOn_finset_iUnion.2 fun k _ =>
      hpar.integrableOn_cell hε hgc k).integrable_of_forall_notMem_eq_zero (hcov hgρ)
  have hintε : ∀ {g : ℂ → ℝ}, Continuous g → (∀ x ∉ ball (0 : ℂ) ρ, g x = 0) →
      Integrable g (degreeWeightedMeasure m ε η μ) :=
    fun hgc hgρ => integrable_degreeWeightedMeasure hgc hpar.1 t (hvan hgρ) fun k _ =>
      hpar.integrableOn_cell hε hgc k
  have hpc : Continuous fun x => max (f x) 0 := hf.max continuous_const
  have hmc : Continuous fun x => max (-f x) 0 := hf.neg.max continuous_const
  have hpρ : ∀ x ∉ ball (0 : ℂ) ρ, max (f x) 0 = 0 := fun x hx => by simp [hfρ x hx]
  have hmρ : ∀ x ∉ ball (0 : ℂ) ρ, max (-f x) 0 = 0 := fun x hx => by simp [hfρ x hx]
  have hpb : ∀ x, 0 ≤ max (f x) 0 ∧ |max (f x) 0| ≤ K := fun x =>
    ⟨le_max_right _ _, by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((le_abs_self _).trans (hfK x)) ((abs_nonneg _).trans (hfK x))⟩
  have hmb : ∀ x, 0 ≤ max (-f x) 0 ∧ |max (-f x) 0| ≤ K := fun x =>
    ⟨le_max_right _ _, by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (hfK x)) ((abs_nonneg _).trans (hfK x))⟩
  have hpL : ∀ x y, |max (f x) 0 - max (f y) 0| ≤ L * ‖x - y‖ := fun x y =>
    (abs_max_sub_max_le_abs _ _ _).trans (hfL x y)
  have hmL : ∀ x y, |max (-f x) 0 - max (-f y) 0| ≤ L * ‖x - y‖ := fun x y => by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact hfL x y
  have h1 := hpar.abs_integral_degreeWeightedMeasure_sub_six_le_of_nonneg (m := m) hε hr hρ t ht
    hpc (fun x => (hpb x).1) hpρ (hA5 _ hpb hpL)
  have h2 := hpar.abs_integral_degreeWeightedMeasure_sub_six_le_of_nonneg (m := m) hε hr hρ t ht
    hmc (fun x => (hmb x).1) hmρ (hA5 _ hmb hmL)
  have hsplit : ∀ ν : Measure ℂ, Integrable (fun x => max (f x) 0) ν →
      Integrable (fun x => max (-f x) 0) ν →
      ∫ x, f x ∂ν = ∫ x, max (f x) 0 ∂ν - ∫ x, max (-f x) 0 ∂ν := by
    intro ν hp hm
    rw [← integral_sub hp hm]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      (max_zero_sub_max_neg_zero_eq_self (f x)).symm)
  rw [hsplit _ (hintε hpc hpρ) (hintε hmc hmρ), hsplit _ (hintμ hpc hpρ) (hintμ hmc hmρ)]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end MatedCRT
