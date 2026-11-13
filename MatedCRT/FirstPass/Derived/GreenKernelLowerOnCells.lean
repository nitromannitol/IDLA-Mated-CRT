import MatedCRT.FirstPass.Derived.GreenKernelHarnackLowerBound
import MatedCRT.FirstPass.Derived.HarnackRingGeometry

/-!
# The bound (4.16) of Berestycki-Gwynne on the cells of the mated-CRT map

Deterministic part of the proof of Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville
Brownian motion*, Lemma 4.4, on the cell sets `V^ε(D) = {k | H^ε_k ∩ D ≠ ∅}` of a continuous space-filling curve
`η`, for an edge multiplicity `m` whose adjacent cells intersect.

* `mem_cellVertices_sphere_of_cells_meet` (footnote 4 of ibid.): a vertex of `V^ε(B̄_s(z))` adjacent to a vertex
  outside `V^ε(B̄_s(z))` lies in `V^ε(∂B_s(z))`, since its cell is connected.
* `le_greenKernel_of_harnack_sphere_of_energy_le`: the bound (4.16). With `A = V^ε(B̄_s(z))`, if the Harnack bound
  (4.13) `max g ≤ C₁ min g` holds for `g = g_B(x, ·)` on `V^ε(∂B_s(z))` and some `h = 1` on `A`, `0` off `B`, has
  `L · E(h) ≤ C₂` (the resistance bound (4.15)), then `g ≥ L / (C₁ C₂) - 1` on `V^ε(∂B_s(z))`.
* `inv_mul_log_min_sub_one_le_greenKernel`: the bound (4.12) for `η(y) ≠ η(x)`, with `z = η(x)`,
  `s = |η(x) - η(y)|`, `L = log(r/s)` and `C = C₁ C₂`.
* `le_greenKernel_of_shell`: the step (4.17) of ibid., by the minimum principle. If adjacent vertices have positions
  `p` at distance at most `δ` and `τ ≤ g` on the shell `s₀ ≤ |p(·) - z| < s₀ + δ`, then `τ ≤ g` at every vertex
  with `|p(·) - z| < s₀`.
* `inv_mul_log_sub_one_le_greenKernel_of_shell`: the same with `τ = C⁻¹ log(r / (s₀ + δ)) - 1`, from the bound
  `C⁻¹ log(r / |p(b) - z|) - 1 ≤ g(b)` on the shell.
-/

namespace MatedCRT

open Set Metric Finset Classical

variable {m : ℤ → ℤ → ℕ}

/-- **Footnote 4 of Berestycki-Gwynne (proof of Lemma 4.4).** For a continuous `η`, a vertex whose cell meets the
closed disk `B̄_s(z)` and meets the cell of a vertex whose cell misses `B̄_s(z)` has a cell point on the circle
`∂B_s(z)`: its cell is connected. -/
theorem mem_cellVertices_sphere_of_cells_meet {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {s : ℝ}
    {a b : ℤ} (ha : a ∈ cellVertices ε η (closedBall z s)) (hb : b ∉ cellVertices ε η (closedBall z s))
    (hab : (cell ε η a ∩ cell ε η b).Nonempty) : a ∈ cellVertices ε η (sphere z s) := by
  obtain ⟨p, hpa, hps⟩ := ha
  obtain ⟨q, hqa, hqb⟩ := hab
  have hq : s < dist q z := by
    by_contra hle
    exact hb ⟨q, hqb, mem_closedBall.2 (not_lt.1 hle)⟩
  have hconn : IsPreconnected ((fun w => dist w z) '' cell ε η a) :=
    (isPreconnected_Icc.image η hη.continuousOn).image _
      (continuous_id.dist continuous_const).continuousOn
  obtain ⟨w, hw, hws⟩ :=
    hconn.Icc_subset ⟨p, hpa, rfl⟩ ⟨q, hqa, rfl⟩ ⟨mem_closedBall.1 hps, hq.le⟩
  exact ⟨w, hw, mem_sphere.2 hws⟩

/-- The vertex `x` lies in `V^ε(B̄_s(η(x)))` for `s ≥ 0`. -/
theorem mem_cellVertices_closedBall_vertexPoint {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (x : ℤ) {s : ℝ}
    (hs : 0 ≤ s) : x ∈ cellVertices ε η (closedBall (vertexPoint ε η x) s) :=
  ⟨vertexPoint ε η x, vertexPoint_mem_cell hε η x, mem_closedBall_self hs⟩

/-- A vertex `y` with `|η(y) - z| = s` lies in `V^ε(∂B_s(z))`. -/
theorem mem_cellVertices_sphere_of_dist_eq {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) {y : ℤ} {z : ℂ} {s : ℝ}
    (hd : dist (vertexPoint ε η y) z = s) : y ∈ cellVertices ε η (sphere z s) :=
  ⟨vertexPoint ε η y, vertexPoint_mem_cell hε η y, mem_sphere.2 hd⟩

/-- **The bound (4.16) of Berestycki-Gwynne on the circle `∂B_s(z)`** (proof of Lemma 4.4). Let `η` be continuous
and let adjacent vertices have intersecting cells. Let `A = V^ε(B̄_s(z)) ⊆ B ⊆ S` be finite, with `S` containing
the neighbours of every vertex of `B`, and `x ∈ A`. Suppose the Harnack bound (4.13)
`g_B(x, a) ≤ C₁ g_B(x, a')` holds for all `a, a' ∈ V^ε(∂B_s(z))`, with `C₁ ≥ 1`, and that some `h` equal to `1` on
`A` and `0` off `B` has `L · E(h) ≤ C₂`, `C₂ > 0`, where `E(h) = ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²`. Then
`g_B(x, y) ≥ L / (C₁ C₂) - 1` for every `y ∈ V^ε(∂B_s(z))`. -/
theorem le_greenKernel_of_harnack_sphere_of_energy_le (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {z : ℂ} {s : ℝ}
    {A B S : Finset ℤ} (hA : (A : Set ℤ) = cellVertices ε η (closedBall z s)) (hAB : A ⊆ B) (hBS : B ⊆ S)
    (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ) (hxA : x ∈ A) {C₁ C₂ L : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    (hharn : ∀ a ∈ cellVertices ε η (sphere z s), ∀ a' ∈ cellVertices ε η (sphere z s),
      greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x a')
    {h : ℤ → ℝ} (h1 : ∀ a ∈ A, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0)
    (hE : L * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    ∀ y ∈ cellVertices ε η (sphere z s), L / (C₁ * C₂) - 1 ≤ greenKernel m ↑B x y :=
  le_greenKernel_of_harnack_of_energy_le_of_mem hsymm hlf hcons hAB hBS hS x hxA hC₁ hC₂
    (fun a ha b _ hbA hab => mem_cellVertices_sphere_of_cells_meet hη
      (by rw [← hA]; exact Finset.mem_coe.2 ha) (by rw [← hA]; exact fun hb => hbA (Finset.mem_coe.1 hb))
      (hadj a b hab)) hharn h1 h0 hE

/-- **The bound (4.12) of Berestycki-Gwynne when `η(y) ≠ η(x)`** (proof of Lemma 4.4, case `s ≥ ε^β`). Take
`z = η(x)` and `s = |η(x) - η(y)| > 0` in `le_greenKernel_of_harnack_sphere_of_energy_le`, with `A = V^ε(B̄_s(η(x)))`
and `L = log(r/s)`, `r > 0`, `ε > 0`. Then
`g_B(x, y) ≥ (C₁ C₂)⁻¹ log ((r / |η(x) - η(y)|) ∧ ε⁻¹) - 1`. -/
theorem inv_mul_log_min_sub_one_le_greenKernel (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Continuous η) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {x y : ℤ}
    (hxy : 0 < ‖vertexPoint ε η x - vertexPoint ε η y‖) {r : ℝ} (hr : 0 < r) {A B S : Finset ℤ}
    (hA : (A : Set ℤ) = cellVertices ε η (closedBall (vertexPoint ε η x)
      ‖vertexPoint ε η x - vertexPoint ε η y‖))
    (hAB : A ⊆ B) (hBS : B ⊆ S) (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {C₁ C₂ : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    (hharn : ∀ a ∈ cellVertices ε η (sphere (vertexPoint ε η x) ‖vertexPoint ε η x - vertexPoint ε η y‖),
      ∀ a' ∈ cellVertices ε η (sphere (vertexPoint ε η x) ‖vertexPoint ε η x - vertexPoint ε η y‖),
      greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x a')
    {h : ℤ → ℝ} (h1 : ∀ a ∈ A, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0)
    (hE : Real.log (r / ‖vertexPoint ε η x - vertexPoint ε η y‖) *
      ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    (C₁ * C₂)⁻¹ * Real.log (min (r / ‖vertexPoint ε η x - vertexPoint ε η y‖) ε⁻¹) - 1 ≤
      greenKernel m ↑B x y := by
  set d := ‖vertexPoint ε η x - vertexPoint ε η y‖ with hd
  have hxA : x ∈ A := by
    rw [← Finset.mem_coe, hA]
    exact mem_cellVertices_closedBall_vertexPoint hε.le η x hxy.le
  have hy : y ∈ cellVertices ε η (sphere (vertexPoint ε η x) d) :=
    mem_cellVertices_sphere_of_dist_eq hε.le η (by rw [dist_eq_norm, norm_sub_rev])
  have hmain := le_greenKernel_of_harnack_sphere_of_energy_le hsymm hlf hcons hη hadj hA hAB hBS hS x hxA
    hC₁ hC₂ hharn h1 h0 hE y hy
  have hM : 0 < min (r / d) ε⁻¹ := lt_min (div_pos hr hxy) (inv_pos.2 hε)
  have hlog : Real.log (min (r / d) ε⁻¹) ≤ Real.log (r / d) := Real.log_le_log hM (min_le_left _ _)
  have hC : 0 ≤ (C₁ * C₂)⁻¹ := inv_nonneg.2 (mul_pos (by linarith) hC₂).le
  calc (C₁ * C₂)⁻¹ * Real.log (min (r / d) ε⁻¹) - 1 ≤ (C₁ * C₂)⁻¹ * Real.log (r / d) - 1 := by
        gcongr
    _ = Real.log (r / d) / (C₁ * C₂) - 1 := by ring
    _ ≤ greenKernel m ↑B x y := hmain

/-- **The step (4.17) of Berestycki-Gwynne** (proof of Lemma 4.4), by the minimum principle. Let adjacent vertices
have positions `p : ℤ → ℂ` at distance at most `δ`. Let `B ⊆ S` be finite, with `S` containing the neighbours of
every vertex of `B`, and let every vertex of `S` within distance `s₀` of `z` lie in `B`. Let `x ∈ S` with
`|p(x) - z| < s₀`. If `τ ≤ g_B(x, b)` for every `b ∈ S` on the shell `s₀ ≤ |p(b) - z| < s₀ + δ`, then
`τ ≤ g_B(x, y)` for every `y ∈ S` with `|p(y) - z| < s₀`: every edge leaving `{|p(·) - z| < s₀}` ends on the shell. -/
theorem le_greenKernel_of_shell (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {p : ℤ → ℂ} {δ : ℝ} (hadj : ∀ a b, m a b ≠ 0 → ‖p a - p b‖ ≤ δ)
    {B S : Finset ℤ} (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {z : ℂ} {s₀ τ : ℝ}
    (hsub : ∀ k ∈ S, ‖p k - z‖ < s₀ → k ∈ B) {x : ℤ} (hxS : x ∈ S) (hx : ‖p x - z‖ < s₀)
    (hshell : ∀ b ∈ S, s₀ ≤ ‖p b - z‖ → ‖p b - z‖ < s₀ + δ → τ ≤ greenKernel m ↑B x b) :
    ∀ y ∈ S, ‖p y - z‖ < s₀ → τ ≤ greenKernel m ↑B x y := by
  have hAB : S.filter (fun k => ‖p k - z‖ < s₀) ⊆ B := fun k hk => by
    rw [Finset.mem_filter] at hk
    exact hsub k hk.1 hk.2
  have key := le_greenKernel_of_outer_boundary hsymm hlf hcons hAB x (Finset.mem_filter.2 ⟨hxS, hx⟩)
    (τ := τ) fun a ha b hbA hab => by
      have has : ‖p a - z‖ < s₀ := (Finset.mem_filter.1 ha).2
      have hbS : b ∈ S := hS a (hAB ha) ((mem_nbrs hlf).2 hab)
      have hb0 : s₀ ≤ ‖p b - z‖ := not_lt.1 fun h => hbA (Finset.mem_filter.2 ⟨hbS, h⟩)
      have h1 : ‖p b - z‖ ≤ ‖p b - p a‖ + ‖p a - z‖ := by
        have := norm_add_le (p b - p a) (p a - z)
        rwa [sub_add_sub_cancel] at this
      have h2 : ‖p b - p a‖ ≤ δ := by
        rw [norm_sub_rev]
        exact hadj a b hab
      exact hshell b hbS hb0 (by linarith)
  exact fun y hyS hy => key y (Finset.mem_filter.2 ⟨hyS, hy⟩)

/-- **The bound (4.17) of Berestycki-Gwynne** in logarithmic form. In the setting of `le_greenKernel_of_shell`, with
`0 < s₀`, `0 < r`, `0 < C`: if `C⁻¹ log(r / |p(b) - z|) - 1 ≤ g_B(x, b)` (the bound (4.16)) for every `b ∈ S` on the
shell `s₀ ≤ |p(b) - z| < s₀ + δ`, then `C⁻¹ log(r / (s₀ + δ)) - 1 ≤ g_B(x, y)` for every `y ∈ S` with
`|p(y) - z| < s₀`. -/
theorem inv_mul_log_sub_one_le_greenKernel_of_shell (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {p : ℤ → ℂ} {δ : ℝ}
    (hadj : ∀ a b, m a b ≠ 0 → ‖p a - p b‖ ≤ δ) {B S : Finset ℤ} (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {z : ℂ}
    {s₀ r C : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (hC : 0 < C) (hsub : ∀ k ∈ S, ‖p k - z‖ < s₀ → k ∈ B) {x : ℤ}
    (hxS : x ∈ S) (hx : ‖p x - z‖ < s₀)
    (hshell : ∀ b ∈ S, s₀ ≤ ‖p b - z‖ → ‖p b - z‖ < s₀ + δ →
      C⁻¹ * Real.log (r / ‖p b - z‖) - 1 ≤ greenKernel m ↑B x b) :
    ∀ y ∈ S, ‖p y - z‖ < s₀ → C⁻¹ * Real.log (r / (s₀ + δ)) - 1 ≤ greenKernel m ↑B x y :=
  le_greenKernel_of_shell hsymm hlf hcons hadj hS hsub hxS hx fun b hbS hb0 hb1 => by
    have hpos : 0 < ‖p b - z‖ := hs₀.trans_le hb0
    have hle : r / (s₀ + δ) ≤ r / ‖p b - z‖ := div_le_div_of_nonneg_left hr.le hpos hb1.le
    have hlog : Real.log (r / (s₀ + δ)) ≤ Real.log (r / ‖p b - z‖) :=
      Real.log_le_log (div_pos hr (hpos.trans hb1)) hle
    have hCi : 0 ≤ C⁻¹ := inv_nonneg.2 hC.le
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog hCi) 1).trans (hshell b hbS hb0 hb1)

end MatedCRT
