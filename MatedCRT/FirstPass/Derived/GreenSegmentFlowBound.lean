import MatedCRT.FirstPass.Derived.GreenResistanceLower
import MatedCRT.FirstPass.Derived.GreenRandomPath
import LatticeProb.Network.SegmentPathFlow

/-!
# The Green kernel on the inner boundary through the segment-path flow

Let `B ⊆ S` be finite vertex sets of a multigraph `m` on `ℤ`, `x ∈ A ⊆ B`, and `θ` a unit flow from
`x` out of `B` (divergence `1{v = x}` on `B`). Its restriction to the edges with at least one
endpoint outside `A` is a unit flow from `A` out of `B`
([BG20, proof of Lem. 5.3, Step 1]); hence by `exists_mem_innerBoundary_greenKernel_le_flowEnergy`
some `y ∈ A` with a neighbour outside `A` satisfies `g_B(y, x) ≤ ½ ∑' θ(a,b)² / m(a,b)`, the sum
running over the edges not inside `A`.

If `|θ(a,b)| ≤ d(a)` for every `a ∉ A`, the edge sum is at most `∑_{a ∈ S \ A} deg(a) d(a)²`
([BG20, (5.6)-(5.7)]). For the expected flow of the segment paths from `z` through the cells `H`,
`d(a) = diam H_a / dist(z, H_a)` (the angle under which `z` sees the cell `H_a`).

## Main statements

* `MatedCRT.exists_mem_innerBoundary_greenKernel_le_restrictedEnergy`: the restriction step.
* `MatedCRT.restrictedFlowEnergy_le_of_edgeBound`: energy of the restricted flow from an
  edge-wise bound by the cell `d`.
* `MatedCRT.exists_mem_innerBoundary_greenKernel_le_segmentPaths`: the bound
  `g_B(y, x) ≤ ∑_{a ∈ S \ A} deg(a) (diam H_a / dist(z, H_a))²` for the segment-path flow.
-/

namespace MatedCRT

open Finset Metric Set LatticeProb

variable {m : ℤ → ℤ → ℕ}

/-- **Restriction to the edges not inside `A`.** For a flow `θ` from `x ∈ A` with divergence
`1{v = x}` on `B ⊇ A`, some `y ∈ A` with a neighbour outside `A`, minimal for `v ↦ G_B(v, x)` on
`A`, has `g_B(y, x)` at most the energy of `θ` on the edges not inside `A`. -/
theorem exists_mem_innerBoundary_greenKernel_le_restrictedEnergy
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a) {B A S : Finset ℤ} (hBS : B ⊆ S) (hAB : A ⊆ B)
    (hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    (hdiv : ∀ v ∈ B, ∑ b ∈ S, θ v b = if v = x then 1 else 0) :
    ∃ y ∈ A, (∃ z, z ∉ A ∧ m y z ≠ 0) ∧
      (∀ v ∈ A, greenFn m (B : Set ℤ) y x ≤ greenFn m (B : Set ℤ) v x) ∧
      greenKernel m (B : Set ℤ) y x ≤ (1 / 2) * ∑ a ∈ S, ∑ b ∈ S,
        (if a ∈ A ∧ b ∈ A then 0 else θ a b) ^ 2 / (m a b : ℝ) := by
  classical
  have hAS : A ⊆ S := hAB.trans hBS
  refine exists_mem_innerBoundary_greenKernel_le_flowEnergy hlf hcons hsymm hBS hAB hS hx
    (θ := fun a b => if a ∈ A ∧ b ∈ A then 0 else θ a b) (fun a b => ?_) (fun a b hab => ?_)
    (fun v hvB hvA => ?_) ?_
  · by_cases h : a ∈ A ∧ b ∈ A
    · simp [h.1, h.2]
    · have h' : ¬ (b ∈ A ∧ a ∈ A) := fun h'' => h ⟨h''.2, h''.1⟩
      simp only [h, h', ite_false]
      exact hθ a b
  · by_cases h : a ∈ A ∧ b ∈ A
    · simp [h.1, h.2]
    · simp only [h, ite_false]
      exact hθc a b hab
  · have hvx : v ≠ x := fun h => hvA (h ▸ hx)
    have := hdiv v hvB
    simp only [hvx, ite_false] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hvA]
  · have h1 : ∑ v ∈ A, ∑ b ∈ S, (if v ∈ A ∧ b ∈ A then 0 else θ v b) =
        ∑ v ∈ A, ∑ b ∈ S, θ v b - ∑ v ∈ A, ∑ b ∈ A, θ v b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.sum_sdiff hAS (f := fun b => θ v b)]
      have : ∑ b ∈ S, (if v ∈ A ∧ b ∈ A then 0 else θ v b) = ∑ b ∈ S \ A, θ v b := by
        rw [← Finset.sum_sdiff hAS (f := fun b => if v ∈ A ∧ b ∈ A then 0 else θ v b)]
        have e1 : ∑ b ∈ A, (if v ∈ A ∧ b ∈ A then 0 else θ v b) = 0 := by
          refine Finset.sum_eq_zero fun b hb => by simp [hv, hb]
        have e2 : ∑ b ∈ S \ A, (if v ∈ A ∧ b ∈ A then 0 else θ v b) = ∑ b ∈ S \ A, θ v b := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have : b ∉ A := (Finset.mem_sdiff.1 hb).2
          simp [this]
        rw [e1, e2, add_zero]
      rw [this]
      ring
    have h2 : ∑ v ∈ A, ∑ b ∈ A, θ v b = 0 := by
      have h3 : ∑ v ∈ A, ∑ b ∈ A, θ v b = -∑ v ∈ A, ∑ b ∈ A, θ v b := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun b _ => hθ b v
      linarith
    have h4 : ∑ v ∈ A, ∑ b ∈ S, θ v b = 1 := by
      rw [Finset.sum_congr rfl fun v hv => hdiv v (hAB hv)]
      simp [Finset.sum_ite_eq', hx]
    rw [h1, h2, h4]; norm_num

/-- **Energy of the restricted flow from an edge-wise bound.** If `|θ(a,b)| ≤ d(a)` for every
`a ∈ S \ A` and `b ∈ S`, the energy of `θ` on the edges of `S` not inside `A` is at most
`∑_{a ∈ S \ A} deg(a) d(a)²` ([BG20, (5.6)-(5.7)]). -/
theorem restrictedFlowEnergy_le_of_edgeBound
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsymm : ∀ a b, m a b = m b a) {A S : Finset ℤ}
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    {d : ℤ → ℝ} (hd : ∀ a ∈ S, a ∉ A → ∀ b ∈ S, |θ a b| ≤ d a) :
    (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (if a ∈ A ∧ b ∈ A then 0 else θ a b) ^ 2 / (m a b : ℝ) ≤
      ∑ a ∈ S with a ∉ A, (mdeg m a : ℝ) * d a ^ 2 := by
  classical
  set e : ℤ → ℝ := fun a => if a ∈ A then 0 else d a ^ 2 with he_def
  have he : ∀ a, 0 ≤ e a := fun a => by
    simp only [he_def]; split_ifs <;> positivity
  have hsq : ∀ a ∈ S, a ∉ A → ∀ b ∈ S, θ a b ^ 2 ≤ e a := fun a ha haA b hb => by
    have := pow_le_pow_left₀ (abs_nonneg _) (hd a ha haA b hb) 2
    rw [sq_abs] at this
    simpa [he_def, haA] using this
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      (if a ∈ A ∧ b ∈ A then 0 else θ a b) ^ 2 / (m a b : ℝ) ≤ (m a b : ℝ) * (e a + e b) := by
    intro a ha b hb
    by_cases hab : a ∈ A ∧ b ∈ A
    · simp only [hab, and_self, ite_true]
      simpa using mul_nonneg (Nat.cast_nonneg (m a b)) (add_nonneg (he a) (he b))
    · simp only [hab, ite_false]
      by_cases hm0 : m a b = 0
      · simp [hm0, hθc a b hm0]
      · have hm1 : (1 : ℝ) ≤ (m a b : ℝ) := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hm0)
        have h1 : θ a b ^ 2 ≤ e a + e b := by
          by_cases haA : a ∈ A
          · have hbA : b ∉ A := fun h => hab ⟨haA, h⟩
            have := hsq b hb hbA a ha
            rw [hθ a b, neg_sq]
            linarith [he a]
          · have := hsq a ha haA b hb
            linarith [he b]
        calc θ a b ^ 2 / (m a b : ℝ) ≤ θ a b ^ 2 := div_le_self (sq_nonneg _) hm1
          _ ≤ e a + e b := h1
          _ ≤ (m a b : ℝ) * (e a + e b) :=
            le_mul_of_one_le_left (add_nonneg (he a) (he b)) hm1
  have hsw : ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * e b = ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * e a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [hsymm a b]
  have hmain : ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (e a + e b) =
      2 * ∑ a ∈ S, e a * ∑ b ∈ S, (m a b : ℝ) := by
    calc ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (e a + e b)
        = ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * e a + ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * e b := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * e a := by rw [hsw]; ring
      _ = 2 * ∑ a ∈ S, e a * ∑ b ∈ S, (m a b : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_mul, mul_comm]
  calc (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (if a ∈ A ∧ b ∈ A then 0 else θ a b) ^ 2 / (m a b : ℝ)
      ≤ (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (e a + e b) := by
        gcongr with a ha b hb
        exact hpair a ha b hb
    _ = ∑ a ∈ S, e a * ∑ b ∈ S, (m a b : ℝ) := by rw [hmain]; ring
    _ ≤ ∑ a ∈ S with a ∉ A, (mdeg m a : ℝ) * d a ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun a ha => ?_
        by_cases haA : a ∈ A
        · simp [he_def, haA]
        · simp only [he_def, haA, ite_false, not_false_eq_true, ite_true]
          have : ∑ b ∈ S, (m a b : ℝ) ≤ (mdeg m a : ℝ) := by
            exact_mod_cast sum_le_mdeg hlf S a
          nlinarith [sq_nonneg (d a)]

/-- **The Green kernel on the inner boundary through the segment-path flow.**
For finite `x ∈ A ⊆ B ⊆ S`, cells `H` and the expected flow of self-avoiding paths through the
cells met by the segment from `z`, starting at `x`, staying in `S` and ending outside `B`: some
`y ∈ A` with a neighbour outside `A`, minimal for `v ↦ G_B(v, x)` on `A`, satisfies
`g_B(y, x) ≤ ∑_{a ∈ S \ A} deg(a) (diam H_a / dist(z, H_a))²`. -/
theorem exists_mem_innerBoundary_greenKernel_le_segmentPaths
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a) {B A S : Finset ℤ} (hBS : B ⊆ S) (hAB : A ⊆ B)
    (hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {H : ℤ → Set ℂ} {z : ℂ} {ℓ : ℝ} {Y : Finset ℤ} {F : Finset ℤ → List ℤ}
    (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) (hHc : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ θ, (segmentPath z ℓ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath z ℓ H Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath z ℓ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ B)
    (hb : ∀ a ∈ S, a ∉ A → Bornology.IsBounded (H a))
    (hpos : ∀ a ∈ S, a ∉ A → 0 < infDist z (H a)) :
    ∃ y ∈ A, (∃ w, w ∉ A ∧ m y w ≠ 0) ∧
      (∀ v ∈ A, greenFn m (B : Set ℤ) y x ≤ greenFn m (B : Set ℤ) v x) ∧
      greenKernel m (B : Set ℤ) y x ≤
        ∑ a ∈ S with a ∉ A, (mdeg m a : ℝ) * (diam (H a) / infDist z (H a)) ^ 2 := by
  have hR' : ∀ a b, m a b ≠ 0 → m b a ≠ 0 := fun a b h => by rwa [hsymm b a]
  have hθ := segmentPathFlow_antisymm (z := z) (ρ := ℓ) (H := H) (Y := Y) (F := F)
  have hθc : ∀ a b, m a b = 0 → segmentPathFlow z ℓ H Y F a b = 0 := fun a b h0 =>
    segmentPathFlow_eq_zero_of_not_rel hR' hchain (not_not.2 h0)
  obtain ⟨y, hyA, hyout, hymin, hyle⟩ := exists_mem_innerBoundary_greenKernel_le_restrictedEnergy
    hlf hcons hsymm hBS hAB hS hx hθ hθc (sum_segmentPathFlow_eq_ite_of_path hHc hpath)
  refine ⟨y, hyA, hyout, hymin, hyle.trans (restrictedFlowEnergy_le_of_edgeBound hlf hsymm hθ hθc
    (d := fun a => diam (H a) / infDist z (H a)) fun a ha haA b _ => ?_)⟩
  exact abs_segmentPathFlow_le_diam_div_infDist hHc hnd
    (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha haA) (hpos a ha haA) b

end MatedCRT
