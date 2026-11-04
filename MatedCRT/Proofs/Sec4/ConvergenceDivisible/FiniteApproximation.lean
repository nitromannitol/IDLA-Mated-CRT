import MatedCRT.Proofs.Sec4.ConvergenceDivisible.SupersolutionMeasurable
import MatedCRT.Proofs.Sec4.GreenLaplacian

/-! # Countable approximation of strict discrete supersolutions -/

namespace MatedCRT

open Set Topology

/-- On a locally finite multigraph the Laplacian at a vertex is continuous for
the topology of pointwise convergence. -/
theorem continuous_mLaplacian_of_locallyFinite {α : Type*}
    (m : α → α → ℕ) (a : α) (h : {b | m a b ≠ 0}.Finite) :
    Continuous fun u : α → ℝ => mLaplacian m u a := by
  classical
  let s := h.toFinset
  have hsum (u : α → ℝ) :
      (∑ᶠ b, (m a b : ℝ) * (u b - u a)) =
        ∑ b ∈ s, (m a b : ℝ) * (u b - u a) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    by_contra hs
    have hz : m a b = 0 := by
      by_contra hn
      exact hs (h.mem_toFinset.mpr hn)
    exact hb (by simp [hz])
  simp_rw [mLaplacian, hsum]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul ((continuous_apply b).sub (continuous_apply a))

/-- Every strict discrete supersolution on finite constraint sets has a strict
approximation in any dense family, with its value at a chosen vertex below any
specified upper bound. -/
theorem exists_dense_strict_discreteSupersolution
    {α : Type*} (m : α → α → ℕ) (V W : Set α)
    (hV : V.Finite) (hW : W.Finite)
    (hlf : ∀ b ∈ V, {c | m b c ≠ 0}.Finite)
    (r φ : α → ℝ) (a : α) (q : ℝ)
    (D : Set (α → ℝ)) (hD : Dense D) (v : α → ℝ)
    (hvV : ∀ b ∈ V, mLaplacian m v b < r b)
    (hvW : ∀ b ∈ W, φ b < v b) (hvq : v a < q) :
    ∃ u ∈ D, (∀ b ∈ V, mLaplacian m u b < r b) ∧
      (∀ b ∈ W, φ b < u b) ∧ u a < q := by
  let U : Set (α → ℝ) :=
    (⋂ b ∈ V, {u | mLaplacian m u b < r b}) ∩
    (⋂ b ∈ W, {u | φ b < u b}) ∩ {u | u a < q}
  have hU : IsOpen U := by
    refine ((hV.isOpen_biInter fun b hb => ?_).inter
      (hW.isOpen_biInter fun b hb => ?_)).inter ?_
    · exact isOpen_lt (continuous_mLaplacian_of_locallyFinite m b (hlf b hb)) continuous_const
    · exact isOpen_lt continuous_const (continuous_apply b)
    · exact isOpen_lt (continuous_apply a) continuous_const
  have hv : v ∈ U := by
    simp only [U, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨⟨hvV, hvW⟩, hvq⟩
  obtain ⟨u, huD, huU⟩ := hD.exists_mem_open hU ⟨v, hv⟩
  refine ⟨u, huD, ?_⟩
  simp only [U, mem_inter_iff, mem_iInter, mem_ofPred_eq] at huU
  exact ⟨huU.1.1, huU.1.2, huU.2⟩

/-- A strictly positive Laplacian threshold permits strictification by mixing
an admissible function with a sufficiently large constant. -/
theorem exists_strict_discreteSupersolution
    {α : Type*} (m : α → α → ℕ) (V W : Set α) (hW : W.Finite)
    (hlf : ∀ b, {c | m b c ≠ 0}.Finite) (r φ : α → ℝ)
    (hr : ∀ b ∈ V, 0 < r b) (v : α → ℝ)
    (hvV : ∀ b ∈ V, mLaplacian m v b ≤ r b)
    (hvW : ∀ b ∈ W, φ b ≤ v b) (a : α) (q : ℝ) (hvq : v a < q) :
    ∃ v' : α → ℝ, (∀ b ∈ V, mLaplacian m v' b < r b) ∧
      (∀ b ∈ W, φ b < v' b) ∧ v' a < q := by
  obtain ⟨C, hC⟩ := (hW.image φ).bddAbove
  let K : ℝ := C + 1
  have hK : ∀ b ∈ W, φ b < K := by
    intro b hb
    have := hC (mem_image_of_mem φ hb)
    dsimp [K]
    linarith
  let U : Set ℝ := {t | (1 - t) * v a + t * K < q}
  have hU : IsOpen U := by
    exact isOpen_lt ((continuous_const.sub continuous_id).mul continuous_const |>.add
      (continuous_id.mul continuous_const)) continuous_const
  have h0 : (0 : ℝ) ∈ U := by simpa [U] using hvq
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  let δ : ℝ := min (η / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 := by dsimp [δ]; linarith [min_le_right (η / 2) (1 / 2 : ℝ)]
  have hδball : δ ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
    dsimp [δ]
    linarith [min_le_left (η / 2) (1 / 2 : ℝ)]
  have hδq : (1 - δ) * v a + δ * K < q := hball hδball
  let v' : α → ℝ := fun b => (1 - δ) * v b + δ * K
  refine ⟨v', ?_, ?_, hδq⟩
  · intro b hb
    have hconst : mLaplacian m (fun _ => K) b = 0 := by simp [mLaplacian]
    have hΔ : mLaplacian m v' b = (1 - δ) * mLaplacian m v b := by
      dsimp [v']
      rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul,
        mLaplacian_const_mul, hconst]
      ring
    rw [hΔ]
    have hmul := mul_nonneg (sub_nonneg.mpr hδle) (sub_nonneg.mpr (hvV b hb))
    have hpos := mul_pos hδpos (hr b hb)
    nlinarith
  · intro b hb
    have hmul := mul_nonneg (sub_nonneg.mpr hδle) (sub_nonneg.mpr (hvW b hb))
    have hpos := mul_pos hδpos (sub_pos.mpr (hK b hb))
    dsimp [v']
    nlinarith

/-- Measurability follows once each admissible function can be strictly
perturbed without increasing its value at the chosen vertex past a bound. -/
theorem MatedCRTEnv.IsValid.measurable_discreteLeastSupersolution_of_strictify
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (hVW : ∀ ω, V ω ⊆ W ω) (hr0 : ∀ ω b, 0 ≤ r ω b)
    (hφ0 : ∀ ω b, φ ω b ≤ 0)
    (hVfin : ∀ ω, (V ω).Finite) (hWfin : ∀ ω, (W ω).Finite)
    (hlf : ∀ ω b, b ∈ V ω → {c | S.mult ε ω b c ≠ 0}.Finite)
    (hstrict : ∀ ω, a ∈ W ω → ∀ (v : ℤ → ℝ),
      ((∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ v b) → ∀ q : ℝ, v a < q →
      ∃ v' : ℤ → ℝ, (∀ b ∈ V ω, mLaplacian (S.mult ε ω) v' b < r ω b) ∧
        (∀ b ∈ W ω, φ ω b < v' b) ∧ v' a < q) :
    Measurable fun ω => discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a := by
  let d : ℕ → (ℤ → ℝ) := TopologicalSpace.denseSeq (ℤ → ℝ)
  have hd : Dense (range d) := TopologicalSpace.denseRange_denseSeq (ℤ → ℝ)
  apply hS.measurable_discreteLeastSupersolution_of_countable_on_domain ε V W hV hW r φ hr hφ a
    (fun n _ => d n) (fun n b => measurable_const) hVW hr0 hφ0
  intro ω ha v hv q hvq
  obtain ⟨v', hv'V, hv'W, hv'q⟩ := hstrict ω ha v hv q hvq
  obtain ⟨u, ⟨n, rfl⟩, huV, huW, huq⟩ :=
    exists_dense_strict_discreteSupersolution (S.mult ε ω) (V ω) (W ω)
      (hVfin ω) (hWfin ω) (hlf ω) (r ω) (φ ω) a q (range d) hd v' hv'V hv'W hv'q
  exact ⟨n, ⟨fun b hb => (huV b hb).le, fun b hb => (huW b hb).le⟩, huq⟩

/-- The finite discrete obstacle problem has a measurable least supersolution
when its threshold is positive on the Laplacian constraint set. -/
theorem MatedCRTEnv.IsValid.measurable_discreteLeastSupersolution_of_finite
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (hVW : ∀ ω, V ω ⊆ W ω) (hr0 : ∀ ω b, 0 ≤ r ω b)
    (hφ0 : ∀ ω b, φ ω b ≤ 0)
    (hVfin : ∀ ω, (V ω).Finite) (hWfin : ∀ ω, (W ω).Finite)
    (hlf : ∀ ω b, {c | S.mult ε ω b c ≠ 0}.Finite)
    (hrpos : ∀ ω b, b ∈ V ω → 0 < r ω b) :
    Measurable fun ω => discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a := by
  apply hS.measurable_discreteLeastSupersolution_of_strictify ε V W hV hW r φ hr hφ a
    hVW hr0 hφ0 hVfin hWfin (fun ω b _ => hlf ω b)
  intro ω _ v hv q hvq
  exact exists_strict_discreteSupersolution (S.mult ε ω) (V ω) (W ω)
    (hWfin ω) (hlf ω) (r ω) (φ ω) (hrpos ω) v hv.1 hv.2 a q hvq

end MatedCRT
