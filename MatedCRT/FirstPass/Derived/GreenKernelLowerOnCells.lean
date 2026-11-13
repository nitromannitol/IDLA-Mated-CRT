import MatedCRT.FirstPass.Derived.GreenKernelHarnackLowerBound
import MatedCRT.FirstPass.Derived.HarnackRingGeometry
import MatedCRT.FirstPass.S4S6c.HcGreen68

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
* `cellVertices_ball_subset_interiorCellVertices`: cells of diameter at most `δ` meeting `B_ρ(z)` are interior to
  `B_{ρ₀}(z)` when `ρ + δ < ρ₀`.
* `inv_two_mul_log_sub_one_le_greenKernel_interior`: the bound (4.16) for the Green domain
  `V^ε(B_r(z)) \ V^ε(∂B_r(z))`, from the resistance bound (4.15) of the annulus `B_{3r/4}(z) \ B̄_s(z)`, `s ≤ r/4`.
* `inv_mul_log_min_sub_one_le_greenKernel_interior`: the bound (4.12) for one vertex `x` and one radius `r`, in all
  cases `η(y) = η(x)`, `|η(y) - η(x)| < s₁`, `s₁ ≤ |η(y) - η(x)| ≤ r/4` and `|η(y) - η(x)| > r/4`, from the Harnack
  bound (4.13) and the resistance bound (4.15) for all `s ∈ [s₁, r/4]`.
* `greenKernelLowerBound_event_of_harnack_energy`: the event of Lemma 2.16 (ibid. Lemma 4.4) for a fixed
  environment, for all `a ∈ V^ε(B_{ρ - ε^{ω₀}})`, `r ∈ [ε^{ω₀}, dist(η(a), ∂B_ρ)]`, `b ∈ V^ε(B_{r/3}(η(a)))`, with
  `C = 2 K C₁ C₂`, from small cells on `B_ρ`, the Harnack bound (4.13) and the resistance bound (4.15).
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
have positions `p : ℤ → ℂ` at distance at most `δ` when one of them lies in `B`. Let `B ⊆ S` be finite, with `S` containing the neighbours of
every vertex of `B`, and let every vertex of `S` within distance `s₀` of `z` lie in `B`. Let `x ∈ S` with
`|p(x) - z| < s₀`. If `τ ≤ g_B(x, b)` for every `b ∈ S` on the shell `s₀ ≤ |p(b) - z| < s₀ + δ`, then
`τ ≤ g_B(x, y)` for every `y ∈ S` with `|p(y) - z| < s₀`: every edge leaving `{|p(·) - z| < s₀}` ends on the shell. -/
theorem le_greenKernel_of_shell (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {p : ℤ → ℂ} {δ : ℝ} {B S : Finset ℤ}
    (hadj : ∀ a ∈ B, ∀ b, m a b ≠ 0 → ‖p a - p b‖ ≤ δ) (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {z : ℂ} {s₀ τ : ℝ}
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
        exact hadj a (hAB ha) b hab
      exact hshell b hbS hb0 (by linarith)
  exact fun y hyS hy => key y (Finset.mem_filter.2 ⟨hyS, hy⟩)

/-- **The bound (4.17) of Berestycki-Gwynne** in logarithmic form. In the setting of `le_greenKernel_of_shell`, with
`0 < s₀`, `0 < r`, `0 < C`: if `C⁻¹ log(r / |p(b) - z|) - 1 ≤ g_B(x, b)` (the bound (4.16)) for every `b ∈ S` on the
shell `s₀ ≤ |p(b) - z| < s₀ + δ`, then `C⁻¹ log(r / (s₀ + δ)) - 1 ≤ g_B(x, y)` for every `y ∈ S` with
`|p(y) - z| < s₀`. -/
theorem inv_mul_log_sub_one_le_greenKernel_of_shell (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {p : ℤ → ℂ} {δ : ℝ}
    {B S : Finset ℤ} (hadj : ∀ a ∈ B, ∀ b, m a b ≠ 0 → ‖p a - p b‖ ≤ δ) (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {z : ℂ}
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

/-- **Small cells meeting `B_ρ(z)` are interior to `B_{ρ₀}(z)`**: if every cell meeting `B_ρ(z)` has diameter at most
`δ` and `ρ + δ < ρ₀`, then `V^ε(B_ρ(z)) ⊆ V^ε(B_{ρ₀}(z)) \ V^ε(∂B_{ρ₀}(z))`. -/
theorem cellVertices_ball_subset_interiorCellVertices {ε : ℝ} (η : ℝ → ℂ) {z : ℂ} {ρ ρ₀ δ : ℝ}
    (hρρ₀ : ρ < ρ₀) (hδ : ρ + δ < ρ₀)
    (hdiam : ∀ b ∈ cellVertices ε η (ball z ρ), ∀ w ∈ cell ε η b, ∀ w' ∈ cell ε η b, dist w w' ≤ δ) :
    cellVertices ε η (ball z ρ) ⊆ interiorCellVertices ε η (ball z ρ₀) := by
  intro b hb
  obtain ⟨w0, hw0, hw0b⟩ := hb
  have h3 : dist w0 z < ρ := mem_ball.1 hw0b
  refine ⟨⟨w0, hw0, ball_subset_ball hρρ₀.le hw0b⟩, ?_⟩
  rintro ⟨w, hw, hwf⟩
  have hρ₀ : ρ₀ ≠ 0 := (lt_of_le_of_lt dist_nonneg (h3.trans hρρ₀)).ne'
  rw [frontier_ball _ hρ₀, mem_sphere] at hwf
  have h1 := dist_triangle w w0 z
  have h2 := hdiam b ⟨w0, hw0, hw0b⟩ w hw w0 hw0
  linarith

/-- **The bound (4.16) of Berestycki-Gwynne for the Green domain `V^ε(B_r(z)) \ V^ε(∂B_r(z))`.** Let `B` be that
domain, `B ⊆ S` with `S` containing the neighbours of every vertex of `B`, let the cells meeting `B_{3r/4}(z)` have
diameter at most `δ` with `3r/4 + δ < r`, and let `η(x) = z`. Let `0 < s ≤ r/4`. Suppose the Harnack bound (4.13)
`g_B(x, a) ≤ C₁ g_B(x, a')` holds on `V^ε(∂B_s(z))`, `C₁ ≥ 1`, and some `h` equal to `1` on `V^ε(B̄_s(z))` and `0`
off `V^ε(B_{3r/4}(z))` has `log(3r/(4s)) E(h) ≤ C₂`, `C₂ > 0` (the resistance bound (4.15) of the annulus
`B_{3r/4}(z) \ B̄_s(z)`). Then `(2 C₁ C₂)⁻¹ log(r/s) - 1 ≤ g_B(x, y)` for every `y ∈ V^ε(∂B_s(z))`. -/
theorem inv_two_mul_log_sub_one_le_greenKernel_interior (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) {η : ℝ → ℂ}
    (hη : Continuous η) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {z : ℂ} {r δ s : ℝ}
    (hδ : 3 * r / 4 + δ < r)
    (hdiam : ∀ b ∈ cellVertices ε η (ball z (3 * r / 4)), ∀ w ∈ cell ε η b, ∀ w' ∈ cell ε η b, dist w w' ≤ δ)
    {B S : Finset ℤ} (hB : (B : Set ℤ) = interiorCellVertices ε η (ball z r)) (hBS : B ⊆ S)
    (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) {x : ℤ} (hx : vertexPoint ε η x = z) (hs : 0 < s) (hsr : s ≤ r / 4)
    {C₁ C₂ : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    (hharn : ∀ a ∈ cellVertices ε η (sphere z s), ∀ a' ∈ cellVertices ε η (sphere z s),
      greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x a')
    {h : ℤ → ℝ} (h1 : ∀ a ∈ cellVertices ε η (closedBall z s), h a = 1)
    (h0 : ∀ a, a ∉ cellVertices ε η (ball z (3 * r / 4)) → h a = 0)
    (hE : Real.log (3 * r / 4 / s) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    ∀ y ∈ cellVertices ε η (sphere z s), (2 * C₁ * C₂)⁻¹ * Real.log (r / s) - 1 ≤ greenKernel m ↑B x y := by
  have hr : 0 < r := by linarith
  have hsub : cellVertices ε η (ball z (3 * r / 4)) ⊆ (B : Set ℤ) := by
    rw [hB]
    exact cellVertices_ball_subset_interiorCellVertices η (by linarith) hδ hdiam
  have hcl : cellVertices ε η (closedBall z s) ⊆ cellVertices ε η (ball z (3 * r / 4)) :=
    fun k ⟨w, hw, hwk⟩ => ⟨w, hw, closedBall_subset_ball (by linarith) hwk⟩
  let A := B.filter (fun k => k ∈ cellVertices ε η (closedBall z s))
  have hA : (A : Set ℤ) = cellVertices ε η (closedBall z s) := by
    ext k
    rw [Finset.coe_filter]
    exact ⟨fun hk => hk.2, fun hk => ⟨Finset.mem_coe.1 (hsub (hcl hk)), hk⟩⟩
  have hAB : A ⊆ B := Finset.filter_subset _ _
  have hxA : x ∈ A := by
    rw [← Finset.mem_coe, hA, ← hx]
    exact mem_cellVertices_closedBall_vertexPoint hε η x hs.le
  have hmain := le_greenKernel_of_harnack_sphere_of_energy_le hsymm hlf hcons hη hadj hA hAB hBS hS x hxA hC₁ hC₂
    hharn (fun a ha => h1 a (by rw [← hA]; exact Finset.mem_coe.2 ha))
    (fun a ha => h0 a fun hk => ha (Finset.mem_coe.1 (hsub hk))) hE
  intro y hy
  have hrs : 4 ≤ r / s := by rw [le_div_iff₀ hs]; linarith
  have hpos : 0 < 3 * r / 4 / s := div_pos (by linarith) hs
  have hhalf : Real.log (r / s) / 2 ≤ Real.log (3 * r / 4 / s) := by
    have h2 : Real.log (r / s) ≤ 2 * Real.log (3 * r / 4 / s) := by
      rw [two_mul, ← Real.log_mul hpos.ne' hpos.ne']
      apply Real.log_le_log (div_pos hr hs)
      rw [show 3 * r / 4 / s = 3 / 4 * (r / s) by ring]
      nlinarith [hrs]
    linarith
  have hCC : 0 < C₁ * C₂ := mul_pos (by linarith) hC₂
  have hCi : 0 ≤ (C₁ * C₂)⁻¹ := inv_nonneg.2 hCC.le
  calc (2 * C₁ * C₂)⁻¹ * Real.log (r / s) - 1 = (C₁ * C₂)⁻¹ * (Real.log (r / s) / 2) - 1 := by ring
    _ ≤ (C₁ * C₂)⁻¹ * Real.log (3 * r / 4 / s) - 1 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hhalf hCi) 1
    _ = Real.log (3 * r / 4 / s) / (C₁ * C₂) - 1 := by ring
    _ ≤ greenKernel m ↑B x y := hmain y hy

/-- **The bound (4.12) of Berestycki-Gwynne for one vertex and one radius** (proof of Lemma 4.4, all cases). Let
`η(x) = z`, let `B = V^ε(B_r(z)) \ V^ε(∂B_r(z))` be the Green domain, `B ⊆ S` with `S` containing the neighbours of
every vertex of `B`; let the cells meeting `B_{3r/4}(z)` have diameter at most `δ`, `3r/4 + δ < r`, and adjacent
vertices one of which lies in `B` have positions within `δ' ≥ 0`. Let `0 < s₁`, `s₁ + δ' ≤ r/4`, and suppose that
for each `s ∈ [s₁, r/4]` the Harnack bound (4.13) holds on `V^ε(∂B_s(z))` with constant `C₁ ≥ 1`, and some `h`
equal to `1` on `V^ε(B̄_s(z))` and `0` off `V^ε(B_{3r/4}(z))` has `log(3r/(4s)) E(h) ≤ C₂`, `C₂ ≥ 1` (the bound
(4.15)). If `log ε⁻¹ ≤ K log(r/(s₁ + δ'))` with `K ≥ 1` (in ibid. `s₁ = ε^β`, `r ≥ ε^ω`, `ω < β`), then for every
`y ∈ S`, `(2 K C₁ C₂)⁻¹ log((r/|η(x) - η(y)|) ∧ ε⁻¹) - 1 ≤ g_B(x, y)`, with `ε⁻¹` in place of the minimum when
`η(y) = η(x)`. For `|η(y) - η(x)| < s₁` this is the step (4.17); for `|η(y) - η(x)| > r/4` the left side is
negative. -/
theorem inv_mul_log_min_sub_one_le_greenKernel_interior (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Continuous η) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {z : ℂ} {x : ℤ}
    (hx : vertexPoint ε η x = z) {r δ δ' s₁ : ℝ} (hδ : 3 * r / 4 + δ < r)
    (hdiam : ∀ b ∈ cellVertices ε η (ball z (3 * r / 4)), ∀ w ∈ cell ε η b, ∀ w' ∈ cell ε η b, dist w w' ≤ δ)
    {B S : Finset ℤ} (hB : (B : Set ℤ) = interiorCellVertices ε η (ball z r)) (hBS : B ⊆ S)
    (hS : ∀ a ∈ B, nbrs hlf a ⊆ S)
    (hadjp : ∀ a ∈ B, ∀ b, m a b ≠ 0 → ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ δ') (hδ' : 0 ≤ δ')
    (hs₁ : 0 < s₁) (hs₁r : s₁ + δ' ≤ r / 4) {C₁ C₂ K : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K)
    (hgap : Real.log ε⁻¹ ≤ K * Real.log (r / (s₁ + δ')))
    (hharn : ∀ s, s₁ ≤ s → s ≤ r / 4 → ∀ a ∈ cellVertices ε η (sphere z s),
      ∀ a' ∈ cellVertices ε η (sphere z s), greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x a')
    (henergy : ∀ s, s₁ ≤ s → s ≤ r / 4 → ∃ h : ℤ → ℝ,
      (∀ a ∈ cellVertices ε η (closedBall z s), h a = 1) ∧
      (∀ a, a ∉ cellVertices ε η (ball z (3 * r / 4)) → h a = 0) ∧
      Real.log (3 * r / 4 / s) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    ∀ y ∈ S, (2 * K * C₁ * C₂)⁻¹ * Real.log (if z = vertexPoint ε η y then ε⁻¹
        else min (r / ‖z - vertexPoint ε η y‖) ε⁻¹) - 1 ≤ greenKernel m ↑B x y := by
  have hr : 0 < r := by linarith
  have hK0 : K ≠ 0 := by linarith
  have hC₁0 : C₁ ≠ 0 := by linarith
  have hC₂0 : C₂ ≠ 0 := by linarith
  have hCC : 1 ≤ C₁ * C₂ := one_le_mul_of_one_le_of_one_le hC₁ hC₂
  have hKCC : 1 ≤ K * C₁ * C₂ := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC₁) hC₂
  have hN : 0 < 2 * C₁ * C₂ := by linarith
  have hM : 0 < 2 * K * C₁ * C₂ := by linarith
  have hCi : 0 ≤ (2 * K * C₁ * C₂)⁻¹ := inv_nonneg.2 hM.le
  have hinv : (2 * K * C₁ * C₂)⁻¹ ≤ (2 * C₁ * C₂)⁻¹ :=
    inv_anti₀ hN (by nlinarith [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hCC)])
  have hball : cellVertices ε η (ball z (3 * r / 4)) ⊆ (B : Set ℤ) := by
    rw [hB]
    exact cellVertices_ball_subset_interiorCellVertices η (by linarith) hδ hdiam
  have hsub : ∀ k ∈ S, ‖vertexPoint ε η k - z‖ < s₁ → k ∈ B := fun k _ hk =>
    Finset.mem_coe.1 (hball ⟨vertexPoint ε η k, vertexPoint_mem_cell hε.le η k,
      mem_ball.2 (by rw [dist_eq_norm]; linarith)⟩)
  have hxS : x ∈ S := hBS (Finset.mem_coe.1 (hball ⟨vertexPoint ε η x, vertexPoint_mem_cell hε.le η x,
    mem_ball.2 (by rw [hx, dist_self]; linarith)⟩))
  have hx0 : ‖vertexPoint ε η x - z‖ < s₁ := by rw [hx, sub_self, norm_zero]; exact hs₁
  have core : ∀ b, s₁ ≤ ‖vertexPoint ε η b - z‖ → ‖vertexPoint ε η b - z‖ ≤ r / 4 →
      (2 * C₁ * C₂)⁻¹ * Real.log (r / ‖vertexPoint ε η b - z‖) - 1 ≤ greenKernel m ↑B x b := by
    intro b hb1 hb2
    obtain ⟨h, h1, h0, hE⟩ := henergy _ hb1 hb2
    exact inv_two_mul_log_sub_one_le_greenKernel_interior hsymm hlf hcons hε.le hη hadj hδ hdiam hB hBS hS hx
      (hs₁.trans_le hb1) hb2 hC₁ (by linarith) (hharn _ hb1 hb2) h1 h0 hE b
      (mem_cellVertices_sphere_of_dist_eq hε.le η (dist_eq_norm _ _))
  intro y hyS
  have hsmall : ∀ X : ℝ, 0 < X → X ≤ ε⁻¹ → ‖vertexPoint ε η y - z‖ < s₁ →
      (2 * K * C₁ * C₂)⁻¹ * Real.log X - 1 ≤ greenKernel m ↑B x y := by
    intro X hX hXe hy
    have hsh := inv_mul_log_sub_one_le_greenKernel_of_shell hsymm hlf hcons (p := vertexPoint ε η) hadjp hS
      hs₁ hr hN hsub hxS hx0 (fun b _ hb1 hb2 => core b hb1 (by linarith)) y hyS hy
    calc (2 * K * C₁ * C₂)⁻¹ * Real.log X - 1
        ≤ (2 * K * C₁ * C₂)⁻¹ * (K * Real.log (r / (s₁ + δ'))) - 1 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left ((Real.log_le_log hX hXe).trans hgap) hCi) 1
      _ = (2 * C₁ * C₂)⁻¹ * Real.log (r / (s₁ + δ')) - 1 := by
          congr 1
          field_simp
      _ ≤ greenKernel m ↑B x y := hsh
  by_cases hxy : z = vertexPoint ε η y
  · have hif : (if z = vertexPoint ε η y then ε⁻¹ else min (r / ‖z - vertexPoint ε η y‖) ε⁻¹) = ε⁻¹ := by
      simp only [hxy, ↓reduceIte]
    rw [hif]
    exact hsmall _ (inv_pos.2 hε) le_rfl (by rw [← hxy, sub_self, norm_zero]; exact hs₁)
  have hif : (if z = vertexPoint ε η y then ε⁻¹ else min (r / ‖z - vertexPoint ε η y‖) ε⁻¹) =
      min (r / ‖z - vertexPoint ε η y‖) ε⁻¹ := by
    simp only [hxy, ↓reduceIte]
  rw [hif]
  have hd : 0 < ‖z - vertexPoint ε η y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hdy : ‖vertexPoint ε η y - z‖ = ‖z - vertexPoint ε η y‖ := norm_sub_rev _ _
  have hMin : 0 < min (r / ‖z - vertexPoint ε η y‖) ε⁻¹ := lt_min (div_pos hr hd) (inv_pos.2 hε)
  have hlogmin := Real.log_le_log hMin (min_le_left (r / ‖z - vertexPoint ε η y‖) ε⁻¹)
  rcases lt_or_ge ‖z - vertexPoint ε η y‖ s₁ with h1 | h1
  · exact hsmall _ hMin (min_le_right _ _) (by rw [hdy]; exact h1)
  rcases le_or_gt ‖z - vertexPoint ε η y‖ (r / 4) with h2 | h2
  · have hc := core y (by rw [hdy]; exact h1) (by rw [hdy]; exact h2)
    rw [hdy] at hc
    have hlog0 : 0 ≤ Real.log (r / ‖z - vertexPoint ε η y‖) :=
      Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
    calc (2 * K * C₁ * C₂)⁻¹ * Real.log (min (r / ‖z - vertexPoint ε η y‖) ε⁻¹) - 1
        ≤ (2 * K * C₁ * C₂)⁻¹ * Real.log (r / ‖z - vertexPoint ε η y‖) - 1 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hlogmin hCi) 1
      _ ≤ (2 * C₁ * C₂)⁻¹ * Real.log (r / ‖z - vertexPoint ε η y‖) - 1 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_right hinv hlog0) 1
      _ ≤ greenKernel m ↑B x y := hc
  · have hl2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
      ring
    have hle4 : Real.log (r / ‖z - vertexPoint ε η y‖) ≤ Real.log 4 :=
      Real.log_le_log (div_pos hr hd) (by rw [div_le_iff₀ hd]; linarith)
    have hle : (2 * K * C₁ * C₂)⁻¹ * Real.log (min (r / ‖z - vertexPoint ε η y‖) ε⁻¹) ≤ 1 :=
      calc (2 * K * C₁ * C₂)⁻¹ * Real.log (min (r / ‖z - vertexPoint ε η y‖) ε⁻¹)
          ≤ (2 * K * C₁ * C₂)⁻¹ * (2 * K * C₁ * C₂) :=
            mul_le_mul_of_nonneg_left (by linarith) hCi
        _ = 1 := inv_mul_cancel₀ hM.ne'
    linarith [greenKernel_nonneg_pole m (↑B) x y]

/-- A point `x` of the closed disk `|x| ≤ ρ` is within `ρ - |x|` of the circle `∂B_ρ` (the radial point `ρ x/|x|`,
or `ρ` when `x = 0`). -/
private theorem infDist_sphere_zero_le_sub_norm {x : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hx : ‖x‖ ≤ ρ) :
    infDist x (sphere 0 ρ) ≤ ρ - ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | h0
  · have hw : ((ρ : ℝ) : ℂ) ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ]
    calc infDist 0 (sphere 0 ρ) ≤ dist (0 : ℂ) (ρ : ℂ) := infDist_le_dist_of_mem hw
      _ = ρ - ‖(0 : ℂ)‖ := by
        rw [dist_comm, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ, norm_zero, sub_zero]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    have hw : ((ρ / ‖x‖ : ℝ) : ℂ) * x ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg hρ hxpos.le), div_mul_cancel₀ _ hxpos.ne']
    have hneg : 1 - ρ / ‖x‖ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hxpos, one_mul]
      exact hx
    calc infDist x (sphere 0 ρ) ≤ dist x (((ρ / ‖x‖ : ℝ) : ℂ) * x) := infDist_le_dist_of_mem hw
      _ = ρ - ‖x‖ := by
        rw [dist_eq_norm, show x - ((ρ / ‖x‖ : ℝ) : ℂ) * x = ((1 - ρ / ‖x‖ : ℝ) : ℂ) * x by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg,
          neg_sub, sub_mul, div_mul_cancel₀ _ hxpos.ne', one_mul]

/-- **The event of Lemma 2.16 (Berestycki-Gwynne, Lemma 4.4) for a fixed environment.** Let `ε > 0`, let finitely
many cells meet each disk, let the cells meeting `B_ρ` have diameter at most `δ` with `4δ < ε^{ω₀}`, and let adjacent
vertices one of which has its cell meeting `B_ρ` have positions within `δ' ≥ 0`, with `ε^β + δ' ≤ ε^{ω₀}/4` and
`log ε⁻¹ ≤ K log(ε^{ω₀}/(ε^β + δ'))`, `K ≥ 1`. Suppose that for every `a ∈ V^ε(B_{ρ - ε^{ω₀}})`, every
`r ∈ [ε^{ω₀}, dist(η(a), ∂B_ρ)]` and every `s ∈ [ε^β, r/4]`, the Green kernel `g = g_{B_r(η(a))}(a, ·)` of the
domain `V^ε(B_r(η(a))) \ V^ε(∂B_r(η(a)))` satisfies the Harnack bound (4.13) `g(y) ≤ C₁ g(y')` on
`V^ε(∂B_s(η(a)))`, and that some `h` equal to `1` on `V^ε(B̄_s(η(a)))` and `0` off `V^ε(B_{3r/4}(η(a)))` has
`log(3r/(4s)) E_S(h) ≤ C₂` for every finite `S` (the resistance bound (4.15)), `C₁, C₂ ≥ 1`. Then for all such
`a`, `r` and every `b ∈ V^ε(B_{r/3}(η(a)))`, `g ≤ G` and `C⁻¹ log((r/|η(a) - η(b)|) ∧ ε⁻¹) - 1 ≤ g(b)` with
`C = 2 K C₁ C₂` (and `ε⁻¹` in place of the minimum when `η(a) = η(b)`). -/
theorem greenKernelLowerBound_event_of_harnack_energy (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Continuous η) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hfin : ∀ (z : ℂ) (r : ℝ), (cellVertices ε η (ball z r)).Finite) {ρ ω₀ β δ δ' C₁ C₂ K : ℝ}
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 ρ), ∀ w ∈ cell ε η b, ∀ w' ∈ cell ε η b, dist w w' ≤ δ)
    (hadjp : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b, m a b ≠ 0 →
      ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ δ')
    (hδ : 4 * δ < ε ^ ω₀) (hδ' : 0 ≤ δ') (hβ : ε ^ β + δ' ≤ ε ^ ω₀ / 4)
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K) (hgap : Real.log ε⁻¹ ≤ K * Real.log (ε ^ ω₀ / (ε ^ β + δ')))
    (hharn : ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) → ∀ s, ε ^ β ≤ s → s ≤ r / 4 →
      ∀ y ∈ cellVertices ε η (sphere (vertexPoint ε η a) s),
      ∀ y' ∈ cellVertices ε η (sphere (vertexPoint ε η a) s),
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a y ≤
          C₁ * greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a y')
    (henergy : ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) → ∀ s, ε ^ β ≤ s → s ≤ r / 4 → ∃ h : ℤ → ℝ,
      (∀ k ∈ cellVertices ε η (closedBall (vertexPoint ε η a) s), h k = 1) ∧
      (∀ k, k ∉ cellVertices ε η (ball (vertexPoint ε η a) (3 * r / 4)) → h k = 0) ∧
      ∀ S : Finset ℤ, Real.log (3 * r / 4 / s) *
        ((1 / 2) * ∑ k ∈ S, ∑ l ∈ S, (m k l : ℝ) * (h k - h l) ^ 2) ≤ C₂) :
    ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ,
      ε ^ ω₀ ≤ r → r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b ≤
          greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b ∧
        (2 * K * C₁ * C₂)⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b := by
  intro a ha r hr1 hr2 b hb
  have hεω : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε ω₀
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hr : 0 < r := hεω.trans_le hr1
  have hmono : ∀ {D D' : Set ℂ}, D ⊆ D' → cellVertices ε η D ⊆ cellVertices ε η D' :=
    fun hDD' _ ⟨w, hw, hwD⟩ => ⟨w, hw, hDD' hwD⟩
  have haρ : a ∈ cellVertices ε η (ball 0 ρ) := hmono (ball_subset_ball (by linarith)) ha
  have hpa : ‖vertexPoint ε η a‖ < ρ := by
    obtain ⟨w, hw, hwb⟩ := ha
    have h1 := hdiam a haρ _ (vertexPoint_mem_cell hε.le η a) w hw
    have h2 := norm_sub_norm_le (vertexPoint ε η a) w
    have h3 : ‖w‖ < ρ - ε ^ ω₀ := mem_ball_zero_iff.1 hwb
    rw [dist_eq_norm] at h1
    linarith
  have hrρ : r ≤ ρ - ‖vertexPoint ε η a‖ :=
    hr2.trans (infDist_sphere_zero_le_sub_norm ((norm_nonneg _).trans hpa.le) hpa.le)
  have hballρ : ∀ t ≤ r, ball (vertexPoint ε η a) t ⊆ ball 0 ρ := fun t ht w hw => by
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    have := norm_sub_norm_le w (vertexPoint ε η a)
    linarith
  have hBfin : (interiorCellVertices ε η (ball (vertexPoint ε η a) r)).Finite :=
    (hfin (vertexPoint ε η a) r).subset sdiff_subset
  set B := hBfin.toFinset with hBdef
  have hB : (B : Set ℤ) = interiorCellVertices ε η (ball (vertexPoint ε η a) r) := hBfin.coe_toFinset
  set S := B ∪ B.biUnion (fun k => nbrs hlf k) with hSdef
  have hBS : B ⊆ S := Finset.subset_union_left
  have hS : ∀ k ∈ B, nbrs hlf k ⊆ S := fun k hk =>
    (Finset.subset_biUnion_of_mem (fun k => nbrs hlf k) hk).trans Finset.subset_union_right
  have hδr : 3 * r / 4 + δ < r := by linarith
  have hdiam' : ∀ k ∈ cellVertices ε η (ball (vertexPoint ε η a) (3 * r / 4)), ∀ w ∈ cell ε η k,
      ∀ w' ∈ cell ε η k, dist w w' ≤ δ := fun k hk => hdiam k (hmono (hballρ _ (by linarith)) hk)
  have hadjp' : ∀ k ∈ B, ∀ l, m k l ≠ 0 → ‖vertexPoint ε η k - vertexPoint ε η l‖ ≤ δ' := by
    intro k hk
    have hk' : k ∈ interiorCellVertices ε η (ball (vertexPoint ε η a) r) := by
      rw [← hB]
      exact Finset.mem_coe.2 hk
    exact hadjp k (hmono (hballρ r le_rfl) hk'.1)
  have hs₁r : ε ^ β + δ' ≤ r / 4 := by linarith
  have hgap' : Real.log ε⁻¹ ≤ K * Real.log (r / (ε ^ β + δ')) :=
    hgap.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hεω (by linarith))
      (div_le_div_of_nonneg_right hr1 (by linarith))) (by linarith))
  have hharn' : ∀ s, ε ^ β ≤ s → s ≤ r / 4 → ∀ y ∈ cellVertices ε η (sphere (vertexPoint ε η a) s),
      ∀ y' ∈ cellVertices ε η (sphere (vertexPoint ε η a) s),
        greenKernel m ↑B a y ≤ C₁ * greenKernel m ↑B a y' := by
    rw [hB]
    exact hharn a ha r hr1 hr2
  have key := inv_mul_log_min_sub_one_le_greenKernel_interior hsymm hlf hcons hε hη hadj (x := a) rfl hδr
    hdiam' hB hBS hS hadjp' hδ' hεβ hs₁r hC₁ hC₂ hK hgap' hharn' fun s hs1 hs2 => by
      obtain ⟨h, h1, h0, hE⟩ := henergy a ha r hr1 hr2 s hs1 hs2
      exact ⟨h, h1, h0, hE S⟩
  have hbB : b ∈ B := by
    rw [← Finset.mem_coe, hB]
    exact cellVertices_ball_subset_interiorCellVertices η (by linarith) hδr hdiam'
      (hmono (ball_subset_ball (by linarith)) hb)
  refine ⟨HcGreen68.greenKernel_le_greenFn _ _ _ _, ?_⟩
  have := key b (hBS hbB)
  rwa [hB] at this

end MatedCRT
