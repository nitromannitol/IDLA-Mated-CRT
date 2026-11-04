import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ArzelaAscoli
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-!
# Lemma 3.1: uniform convergence along a subsequence on which the proxies converge (deterministic)

Fix a continuous, proper, surjective curve `η`, scales `ε_n → 0`, factors `m_n` with `m_n⁻¹ ≤ C_m ε_n`
(eq:meps-scaling), and functions `u_n` on `ℤ`. Write `F_n = ū_n` (`rescale`).

* `isAsymptoticallyEquicontinuousOn_rescale`: asymptotic equicontinuity of `ε_n u_n` at the level of vertices on
  `V^{ε_n}(K)` gives asymptotic equicontinuity of `F_n` on `K`. The cells meeting `K` shrink, and `x` lies in the
  cell of `a^ε_x`.
* `eventually_abs_sub_proxyValue_le`: at `t ∈ D`, `F_n(t)` is within `k` of the proxy at radius `1/(j+1)` for large
  `j` and `n`.
* `tightness_of_proxies`: if the proxies at the points of `denseSeq ℂ` and the radii `1/(j+1)` converge along `Φ`,
  then `F_{Φ k}` converges uniformly on compacts of `D` to a limit continuous on `D`. Under asymptotic equicontinuity
  on `V(cl D)` it also converges uniformly on `cl(D)`.
-/

namespace MatedCRT.Tightness

open Filter Topology Set Metric

variable {D : Set ℂ} {η : ℝ → ℂ} {ε : ℕ → ℝ} {u : ℕ → ℤ → ℝ} {mε : ℕ → ℝ} {Cm : ℝ}

/-- The bound `m⁻¹ |u a - u b| ≤ k` from `ε |u a - u b| ≤ k / C_m` and `0 ≤ m⁻¹ ≤ C_m ε`. -/
theorem abs_inv_mul_sub_le {m e Cm k x y : ℝ} (hCm : 0 < Cm) (hm0 : 0 ≤ m⁻¹) (hm : m⁻¹ ≤ Cm * e)
    (h : e * |x - y| ≤ k / Cm) : |m⁻¹ * x - m⁻¹ * y| ≤ k := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hm0]
  calc m⁻¹ * |x - y| ≤ Cm * e * |x - y| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
    _ = Cm * (e * |x - y|) := by ring
    _ ≤ Cm * (k / Cm) := mul_le_mul_of_nonneg_left h hCm.le
    _ = k * (Cm * Cm⁻¹) := by ring
    _ = k := by rw [mul_inv_cancel₀ hCm.ne', mul_one]

/-- Asymptotic equicontinuity of `ū_n` on a bounded `K` from the vertex-level one. -/
theorem isAsymptoticallyEquicontinuousOn_rescale {K : Set ℂ} (hK : Bornology.IsBounded K)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η)
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 < Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hV : IsVertexAsymptoticallyEquicontinuous ε η u K) :
    IsAsymptoticallyEquicontinuousOn (fun n => rescale (mε n) (ε n) η (u n)) K := by
  intro k hk
  obtain ⟨δ, hδ, hev⟩ := hV (k / Cm) (div_pos hk hCm)
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp hK (s := δ / 4) (by positivity)
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hev, hm, hε0.eventually (gt_mem_nhds hε₀)] with n hn hmn hεn x hx y hy hxy
  have hxa : x ∈ cell (ε n) η (vertexOf (ε n) η x) := mem_cell_vertexOf hη hp hsurj (hε n) x
  have hyb : y ∈ cell (ε n) η (vertexOf (ε n) η y) := mem_cell_vertexOf hη hp hsurj (hε n) y
  have haK : vertexOf (ε n) η x ∈ cellVertices (ε n) η K := ⟨x, hxa, hx⟩
  have hbK : vertexOf (ε n) η y ∈ cellVertices (ε n) η K := ⟨y, hyb, hy⟩
  have h1 : ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - x‖ < δ / 4 := by
    rw [norm_sub_rev]; exact hcell (ε n) (hε n) hεn _ haK x hxa
  have h2 : ‖y - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ < δ / 4 :=
    hcell (ε n) (hε n) hεn _ hbK y hyb
  have hab : ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ ≤ δ := by
    calc _ = ‖(vertexPoint (ε n) η (vertexOf (ε n) η x) - x) + (x - y) +
          (y - vertexPoint (ε n) η (vertexOf (ε n) η y))‖ := by congr 1; ring
      _ ≤ ‖vertexPoint (ε n) η (vertexOf (ε n) η x) - x‖ + ‖x - y‖ +
          ‖y - vertexPoint (ε n) η (vertexOf (ε n) η y)‖ := norm_add₃_le
      _ ≤ δ := by linarith
  exact abs_inv_mul_sub_le hCm hmn.1 hmn.2 (hn _ haK _ hbK hab)

/-- At `t ∈ D`, `ū_n(t)` is within `k` of the proxy at radius `1/(j+1)`, for all large `j` and `n`. -/
theorem eventually_abs_sub_proxyValue_le (hDo : IsOpen D) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 < Cm) (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hEQ : ∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous ε η u K)
    {t : ℂ} (ht : t ∈ D) {k : ℝ} (hk : 0 < k) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ᶠ n in atTop,
      |rescale (mε n) (ε n) η (u n) t -
        proxyValue (ε n) η D t (1 / ((j : ℝ) + 1)) (fun a => (mε n)⁻¹ * u n a)| ≤ k := by
  obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.1 hDo t ht
  have hKD : closedBall t (r0 / 2) ⊆ D := (closedBall_subset_ball (half_lt_self hr0)).trans hball
  obtain ⟨δ, hδ, hev⟩ := hEQ _ (isCompact_closedBall t _) hKD (k / Cm) (div_pos hk hCm)
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt (lt_min (half_pos hδ) (half_pos hr0))
  refine ⟨J, fun j hj => ?_⟩
  have hrJ : 1 / ((j : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
    have : (J : ℝ) ≤ j := by exact_mod_cast hj
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set r : ℝ := 1 / ((j : ℝ) + 1) with hr_def
  have hr : 0 < r := by positivity
  have hrδ : r < δ / 2 := lt_of_le_of_lt hrJ (lt_of_lt_of_le hJ (min_le_left _ _))
  have hrr0 : r < r0 / 2 := lt_of_le_of_lt hrJ (lt_of_lt_of_le hJ (min_le_right _ _))
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp (Bornology.isBounded_singleton (x := t)) hr
  filter_upwards [hev, hm, hε0.eventually (gt_mem_nhds hε₀)] with n hn hmn hεn
  have hta : t ∈ cell (ε n) η (vertexOf (ε n) η t) := mem_cell_vertexOf hη hp hsurj (hε n) t
  have h1 : ‖t - vertexPoint (ε n) η (vertexOf (ε n) η t)‖ < r :=
    hcell (ε n) (hε n) hεn _ ⟨t, hta, rfl⟩ t hta
  have haK : vertexOf (ε n) η t ∈ cellVertices (ε n) η (closedBall t (r0 / 2)) :=
    ⟨t, hta, mem_closedBall_self (by positivity)⟩
  have hprox : IsProxyVertex (ε n) η D t r (vertexOf (ε n) η t) := by
    refine ⟨hKD ?_, by rw [norm_sub_rev]; exact h1⟩
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    linarith
  rcases proxyValue_spec (ε n) η D t r (fun a => (mε n)⁻¹ * u n a) with ⟨κ, hκ, hval⟩ | ⟨hnone, -⟩
  swap
  · exact absurd hprox (hnone _)
  rw [hval]
  have hκK : κ ∈ cellVertices (ε n) η (closedBall t (r0 / 2)) := by
    refine mem_cellVertices_of_vertexPoint_mem (hε n) ?_
    rw [mem_closedBall, dist_eq_norm]
    linarith [hκ.2]
  have e1 : ‖vertexPoint (ε n) η (vertexOf (ε n) η t) - t‖ < r := by rw [norm_sub_rev]; exact h1
  have e2 : ‖t - vertexPoint (ε n) η κ‖ < r := by rw [norm_sub_rev]; exact hκ.2
  have hab : ‖vertexPoint (ε n) η (vertexOf (ε n) η t) - vertexPoint (ε n) η κ‖ ≤ δ := by
    calc _ = ‖(vertexPoint (ε n) η (vertexOf (ε n) η t) - t) + (t - vertexPoint (ε n) η κ)‖ := by
          congr 1; ring
      _ ≤ ‖vertexPoint (ε n) η (vertexOf (ε n) η t) - t‖ + ‖t - vertexPoint (ε n) η κ‖ := norm_add_le _ _
      _ ≤ δ := by linarith
  exact abs_inv_mul_sub_le hCm hmn.1 hmn.2 (hn _ haK κ hκK hab)

/-- Convergence of `ū_{Φ k}(t)` at `t ∈ D` from the convergence of the proxies at `t`. -/
theorem tendsto_rescale_of_proxies (hDo : IsOpen D) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 < Cm) (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hEQ : ∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous ε η u K)
    {Φ : ℕ → ℕ} (hΦ : StrictMono Φ) {t : ℂ}
    (hY : ∀ j : ℕ, ∃ l, Tendsto (fun k => proxyValue (ε (Φ k)) η D t (1 / ((j : ℝ) + 1))
      (fun a => (mε (Φ k))⁻¹ * u (Φ k) a)) atTop (𝓝 l)) (ht : t ∈ D) :
    ∃ l, Tendsto (fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u (Φ k)) t) atTop (𝓝 l) := by
  refine tendsto_of_forall_approx fun k hk => ?_
  obtain ⟨J, hJ⟩ := eventually_abs_sub_proxyValue_le hDo hη hp hsurj hε hε0 hCm hm hEQ ht hk
  exact ⟨_, hY J, hΦ.tendsto_atTop.eventually (hJ J le_rfl)⟩

/-- The proxy coordinates: coordinate `c` is the proxy at the point `denseSeq ℂ i` and radius `1/(j+1)`, where
`(i, j) = c.unpair`. -/
noncomputable def proxyCoord (ε : ℕ → ℝ) (η : ℝ → ℂ) (D : Set ℂ) (mε : ℕ → ℝ) (u : ℕ → ℤ → ℝ) (n c : ℕ) : ℝ :=
  proxyValue (ε n) η D (TopologicalSpace.denseSeq ℂ c.unpair.1) (1 / ((c.unpair.2 : ℝ) + 1))
    fun a => (mε n)⁻¹ * u n a

/-- **Uniform convergence along a subsequence on which the proxies converge.** -/
theorem tightness_of_proxies (hDo : IsOpen D) (hDb : Bornology.IsBounded D) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 < Cm) (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hEQ : ∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous ε η u K)
    {Φ : ℕ → ℕ} (hΦ : StrictMono Φ)
    (hY : ∀ c, ∃ l, Tendsto (fun k => proxyCoord ε η D mε u (Φ k) c) atTop (𝓝 l)) :
    ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u (Φ k))) ubar atTop O) ∧
      (IsVertexAsymptoticallyEquicontinuous ε η u (closure D) →
        TendstoUniformlyOn (fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u (Φ k))) ubar atTop (closure D)) := by
  set G : ℕ → ℂ → ℝ := fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u (Φ k)) with hG
  have hconv : ∀ t ∈ {t : ℂ | t ∈ D ∧ ∃ i, TopologicalSpace.denseSeq ℂ i = t},
      ∃ l, Tendsto (fun k => G k t) atTop (𝓝 l) := by
    rintro t ⟨ht, i, rfl⟩
    refine tendsto_rescale_of_proxies hDo hη hp hsurj hε hε0 hCm hm hEQ hΦ (fun j => ?_) ht
    have := hY (Nat.pair i j)
    simpa only [proxyCoord, Nat.unpair_pair] using this
  have hEQG : ∀ K : Set ℂ, IsCompact K → K ⊆ D → IsAsymptoticallyEquicontinuousOn G K := fun K hK hKD =>
    (isAsymptoticallyEquicontinuousOn_rescale hK.isBounded hη hp hsurj hε hε0 hCm hm
      (hEQ K hK hKD)).comp_strictMono hΦ
  have hdense := TopologicalSpace.denseRange_denseSeq ℂ
  have hunif : ∀ O : Set ℂ, IsCompact O → O ⊆ D →
      TendstoUniformlyOn G (fun x => limUnder atTop fun k => G k x) atTop O := by
    intro O hO hOD
    obtain ⟨r, hr, hrD⟩ := hO.exists_cthickening_subset_open hDo hOD
    refine tendstoUniformlyOn_limUnder (uniformCauchySeqOn_of_isAsymptoticallyEquicontinuousOn hO
      (self_subset_cthickening O) (hEQG _ hO.cthickening hrD) ?_ hconv)
    intro x hx δ hδ
    obtain ⟨i, hi⟩ := hdense.exists_mem_open ((show IsOpen (ball x (min δ r)) from isOpen_ball).inter hDo)
      ⟨x, mem_ball_self (lt_min hδ hr), hOD hx⟩
    refine ⟨_, ⟨hi.2, i, rfl⟩, mem_cthickening_of_dist_le _ x r O hx
      (lt_of_lt_of_le hi.1 (min_le_right _ _)).le, ?_⟩
    rw [← dist_eq_norm, dist_comm]
    exact lt_of_lt_of_le hi.1 (min_le_left _ _)
  refine ⟨fun x => limUnder atTop fun k => G k x, ?_, fun O hO hOD => hunif O hO (subset_closure.trans hOD), ?_⟩
  · intro x hx
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hDo x hx
    have hK : closedBall x (r / 2) ⊆ D := (closedBall_subset_ball (half_lt_self hr)).trans hrD
    refine (continuousAt_of_isAsymptoticallyEquicontinuousOn (closedBall_mem_nhds x (half_pos hr))
      (hEQG _ (isCompact_closedBall x _) hK) fun y hy => ?_).continuousWithinAt
    exact (hunif _ (isCompact_closedBall x _) hK).tendsto_at hy
  · intro hEQc
    have hEQGc : IsAsymptoticallyEquicontinuousOn G (closure D) :=
      (isAsymptoticallyEquicontinuousOn_rescale hDb.closure hη hp hsurj hε hε0 hCm hm hEQc).comp_strictMono hΦ
    refine tendstoUniformlyOn_limUnder (uniformCauchySeqOn_of_isAsymptoticallyEquicontinuousOn
      hDb.isCompact_closure subset_rfl hEQGc ?_ hconv)
    intro x hx δ hδ
    obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.1 hx δ hδ
    have hyx : y ∈ ball x δ := by rw [mem_ball, dist_comm]; exact hxy
    obtain ⟨i, hi⟩ := hdense.exists_mem_open ((show IsOpen (ball x δ) from isOpen_ball).inter hDo) ⟨y, hyx, hyD⟩
    refine ⟨_, ⟨hi.2, i, rfl⟩, subset_closure hi.2, ?_⟩
    rw [← dist_eq_norm, dist_comm]
    exact hi.1

end MatedCRT.Tightness
