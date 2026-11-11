import MatedCRT.FirstPass.S3g.Geometry
import MatedCRT.FirstPass.S3g.DiscreteSolve
import MatedCRT.Defs.Notation

/-! # Estimates for the boundary-stability bridge of corrected Lemma 3.5

* `boundary_bound`: a boundary cell `b` (meeting the sphere, of diameter `≤ D ≤ s`) has
  `|φ(η b) - φ(π η b)| ≤ C D^χ`, where `π` is the radial retraction onto `cl B_r(z)`; this uses only the Hölder
  bound of `φ` on `cl B_{r+s}(z)`.
* `rescale_sub_bound`: the discrete maximum principle, applied to the discrete difference `F - G` (harmonic on the
  interior cells), transfers the boundary bound to every point of `cl B_r(z)` after rescaling.
* `tendsto_uniformly_inProb_of_sup_bound`: a uniform-in-probability limit transfers across an almost sure
  uniform bound whose failure has polynomially small probability. -/

namespace MatedCRT.FirstPass35Bridge

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Hölder bound in real form: `|f x - f y| ≤ C dist(x,y)^χ` on `s`. -/
theorem holder_dist_le {f : ℂ → ℝ} {s : Set ℂ} {C χ : ℝ≥0} (h : HolderOnWith C χ f s) {x y : ℂ}
    (hx : x ∈ s) (hy : y ∈ s) : dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (χ : ℝ) := by
  have h1 := h.nndist_le_of_le hx hy (le_refl (nndist x y))
  have h2 : ((nndist (f x) (f y) : ℝ≥0) : ℝ) ≤ ((C * (nndist x y) ^ (χ : ℝ) : ℝ≥0) : ℝ) :=
    NNReal.coe_le_coe.2 h1
  rw [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist] at h2
  exact h2

/-- **Boundary bound.** For a boundary cell `b` (its cell meets the sphere `∂B_r(z)`) of diameter at most `D ≤ s`,
the discrepancy between the boundary data read at `η(b)` and at its retraction `π η(b)` is at most `C D^χ`. -/
theorem boundary_bound {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r s D : ℝ} {φ : ℂ → ℝ} {C χ : ℝ≥0}
    (hε : 0 < ε) (hη : Continuous η) (hr : 0 < r) (hs : 0 < s) (hDs : D ≤ s)
    (hH : HolderOnWith C χ φ (closedBall z (r + s))) {b : ℤ}
    (hb : b ∈ cellVertices ε η (sphere z r)) (hdiam : diam (cell ε η b) ≤ D) :
    |φ (vertexPoint ε η b) - φ (ballRetraction z r (vertexPoint ε η b))| ≤ (C : ℝ) * D ^ (χ : ℝ) := by
  obtain ⟨w, hwcell, hwsph⟩ := hb
  have hcb : Bornology.IsBounded (cell ε η b) := ((isCompact_Icc).image hη).isBounded
  have hp : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell_self hε b
  have hpw : dist (vertexPoint ε η b) w ≤ D := (dist_le_diam_of_mem hcb hp hwcell).trans hdiam
  have hwz : dist w z = r := mem_sphere.1 hwsph
  have hq : dist (vertexPoint ε η b) (ballRetraction z r (vertexPoint ε η b)) ≤ D :=
    (dist_le_dist_ballRetraction hr _ (mem_closedBall.2 hwz.le)).trans hpw
  have hpS : vertexPoint ε η b ∈ closedBall z (r + s) := by
    rw [mem_closedBall]
    have := dist_triangle (vertexPoint ε η b) w z
    linarith
  have hqS : ballRetraction z r (vertexPoint ε η b) ∈ closedBall z (r + s) :=
    closedBall_subset_closedBall (show r ≤ r + s by linarith) (ballRetraction_mem_closedBall hr _)
  have h1 := holder_dist_le hH hpS hqS
  have h2 : dist (vertexPoint ε η b) (ballRetraction z r (vertexPoint ε η b)) ^ (χ : ℝ) ≤ D ^ (χ : ℝ) :=
    Real.rpow_le_rpow dist_nonneg hq (NNReal.coe_nonneg χ)
  rw [Real.dist_eq] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 C.coe_nonneg)

/-- The sphere lies in `ball 0 ρ₁` when the ball `ball z r` lies in `ball 0 ρ` and `ρ < ρ₁`. -/
theorem sphere_subset_ball_of_ball_subset {z : ℂ} {r ρ ρ₁ : ℝ} (hr : r ≠ 0) (hρ : 0 < ρ)
    (hball : ball z r ⊆ ball 0 ρ) (hρρ : ρ < ρ₁) : sphere z r ⊆ ball 0 ρ₁ := by
  intro y hy
  have h1 : closedBall z r ⊆ closedBall 0 ρ := by
    rw [← closure_ball z hr, ← closure_ball (0 : ℂ) hρ.ne']
    exact closure_mono hball
  have hy' : y ∈ closedBall 0 ρ := h1 (sphere_subset_closedBall hy)
  rw [mem_closedBall, dist_zero_right] at hy'
  rw [mem_ball, dist_zero_right]
  linarith

/-- **Discrete maximum principle transfer.** Let `H = F - G` on `ℤ`, harmonic on the interior cells `A` of the
ball, with `|H b| ≤ |m_ε| K₀` on the boundary cells. Then `|m_ε⁻¹ H(a)| ≤ K₀` for every vertex `a` of a cell meeting
`cl B_r(z)`, since such a vertex is interior or a boundary cell (`vertexOf_mem_interior_or_sphere`). -/
theorem rescale_sub_bound {mε ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {z : ℂ} {r K₀ : ℝ}
    (hε : 0 < ε) (hη : Continuous η) (hsurj : Function.Surjective η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hr : 0 < r)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hadj : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hmaxA : ∀ u : ℤ → ℝ, IsSubharmonicOn m u (interiorCellVertices ε η (ball z r)) →
      ∀ a ∈ interiorCellVertices ε η (ball z r),
        ∃ b ∈ vBoundary m (interiorCellVertices ε η (ball z r)), u a ≤ u b)
    (F G : ℤ → ℝ) (hK₀ : 0 ≤ K₀)
    (hHarm : ∀ a ∈ interiorCellVertices ε η (ball z r), mLaplacian m (fun x => F x - G x) a = 0)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), |F b - G b| ≤ |mε| * K₀) (x : ℂ) (hx : x ∈ closedBall z r) :
    |rescale mε ε η F x - rescale mε ε η G x| ≤ K₀ := by
  have hr0 : r ≠ 0 := hr.ne'
  have hbdH : ∀ b ∈ vBoundary m (interiorCellVertices ε η (ball z r)), |F b - G b| ≤ |mε| * K₀ :=
    fun b hb => hbd b (vBoundary_interior_subset_sphere hη hr0 hadj hb)
  have hHa : |F (vertexOf ε η x) - G (vertexOf ε η x)| ≤ |mε| * K₀ := by
    have hxc := mem_cell_vertexOf hη hsurj hp hε x
    rcases vertexOf_mem_interior_or_sphere hr0 hx hxc with haA | has
    · have hsubH : IsSubharmonicOn m (fun y => F y - G y) (interiorCellVertices ε η (ball z r)) :=
        fun a ha => (hHarm a ha).ge
      have hsubN : IsSubharmonicOn m (fun y => (0 : ℝ) - (F y - G y))
          (interiorCellVertices ε η (ball z r)) := by
        intro a ha
        have h := mLaplacian_sub_of_locallyFinite hlf (fun _ => (0 : ℝ)) (fun y => F y - G y) a
        rw [mLaplacian_zero_fun', hHarm a ha] at h
        show 0 ≤ mLaplacian m (fun y => (0 : ℝ) - (F y - G y)) a
        rw [h]
        norm_num
      obtain ⟨b, hb, hHb⟩ := hmaxA _ hsubH _ haA
      obtain ⟨b', hb', hHb'⟩ := hmaxA _ hsubN _ haA
      have hb1 : F b - G b ≤ |mε| * K₀ := (le_abs_self _).trans (hbdH b hb)
      have hb2 : -(F b' - G b') ≤ |mε| * K₀ := (neg_le_abs _).trans (hbdH b' hb')
      have hA1 : F (vertexOf ε η x) - G (vertexOf ε η x) ≤ |mε| * K₀ := by linarith
      have hA2 : -(F (vertexOf ε η x) - G (vertexOf ε η x)) ≤ |mε| * K₀ := by linarith
      exact abs_le.2 ⟨by linarith, hA1⟩
    · exact hbd _ has
  have hinv : |mε⁻¹| * |mε| ≤ 1 := by
    rcases eq_or_ne mε 0 with h | h
    · simp [h]
    · rw [← abs_mul, inv_mul_cancel₀ h, abs_one]
  unfold rescale
  rw [← mul_sub, abs_mul]
  calc |mε⁻¹| * |F (vertexOf ε η x) - G (vertexOf ε η x)|
      ≤ |mε⁻¹| * (|mε| * K₀) := mul_le_mul_of_nonneg_left hHa (abs_nonneg _)
    _ = (|mε⁻¹| * |mε|) * K₀ := by ring
    _ ≤ 1 * K₀ := mul_le_mul_of_nonneg_right hinv hK₀
    _ = K₀ := one_mul _

/-- Real power tends to `0` at `0` along the right half-line, for positive exponent. -/
theorem tendsto_rpow_zero_nhds {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝 0) (𝓝 0) := by
  have h0 := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rwa [Real.zero_rpow ha.ne'] at h0

/-- The same limit along the right half-line. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_rpow_zero_nhds ha).mono_left nhdsWithin_le_nhds

/-- **Uniform convergence in probability transfers across a sup bound.** If `Y ε → v` uniformly on `K` in
probability, and `|X ε ω x - Y ε ω x| ≤ g ε` on the good event (of polynomially high probability, for a.e. `ω`
in `G ε`), with `g ε → 0`, then `X ε → v` uniformly on `K` in probability. -/
theorem tendsto_uniformly_inProb_of_sup_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : ℝ → Ω → ℂ → ℝ} {v : Ω → ℂ → ℝ} {K : Set ℂ} {E G : ℝ → Set Ω} {g : ℝ → ℝ}
    (hY : TendstoUniformlyOnInProbability P Y v K) (hE : HarmonicBalls.PolyHighProb P E)
    (hG : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, ω ∈ G ε) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ G ε, ω ∈ E ε → ∀ x ∈ K, |X ε ω x - Y ε ω x| ≤ g ε) :
    TendstoUniformlyOnInProbability P X v K := by
  intro δ hδ
  have hEt : Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨p, hp, C, r₀, hr₀, hEp⟩ := hE
    have hpow : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 0) := by
        have := (tendsto_const_nhds (x := C)).mul (tendsto_rpow_nhdsGT_zero hp)
        simpa using this
      have := ENNReal.tendsto_ofReal h1
      rwa [ENNReal.ofReal_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow ?_ ?_
    · exact Eventually.of_forall fun _ => zero_le
    · filter_upwards [Ioo_mem_nhdsGT hr₀] with ε hε
      exact hEp ε hε.1 hε.2
  have hgd : ∀ᶠ ε in 𝓝[>] 0, g ε ≤ δ / 2 :=
    hg.eventually (eventually_le_nhds (half_pos hδ))
  have hsum := (hY (δ / 2) (half_pos hδ)).add hEt
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [hbound, hgd, self_mem_nhdsWithin] with ε hbε hgε hε0
    have hGnull : P (G ε)ᶜ = 0 := ae_iff.1 (hG ε hε0)
    have hsub : {ω | ∃ x ∈ K, δ < |X ε ω x - v ω x|} ⊆
        {ω | ∃ x ∈ K, δ / 2 < |Y ε ω x - v ω x|} ∪ ((E ε)ᶜ ∪ (G ε)ᶜ) := by
      intro ω hω
      obtain ⟨x, hxK, hx⟩ := hω
      by_cases hc : ω ∈ G ε ∧ ω ∈ E ε
      · left
        refine ⟨x, hxK, ?_⟩
        have h1 := hbε ω hc.1 hc.2 x hxK
        have h2 := abs_sub_le (X ε ω x) (Y ε ω x) (v ω x)
        linarith
      · right
        by_cases hGω : ω ∈ G ε
        · left
          exact fun hEω => hc ⟨hGω, hEω⟩
        · right
          exact hGω
    calc P {ω | ∃ x ∈ K, δ < |X ε ω x - v ω x|}
        ≤ P ({ω | ∃ x ∈ K, δ / 2 < |Y ε ω x - v ω x|} ∪ ((E ε)ᶜ ∪ (G ε)ᶜ)) := measure_mono hsub
      _ ≤ P {ω | ∃ x ∈ K, δ / 2 < |Y ε ω x - v ω x|} + P ((E ε)ᶜ ∪ (G ε)ᶜ) := measure_union_le _ _
      _ ≤ P {ω | ∃ x ∈ K, δ / 2 < |Y ε ω x - v ω x|} + (P (E ε)ᶜ + P (G ε)ᶜ) :=
          add_le_add le_rfl (measure_union_le _ _)
      _ = P {ω | ∃ x ∈ K, δ / 2 < |Y ε ω x - v ω x|} + P (E ε)ᶜ := by rw [hGnull, add_zero]

end MatedCRT.FirstPass35Bridge
