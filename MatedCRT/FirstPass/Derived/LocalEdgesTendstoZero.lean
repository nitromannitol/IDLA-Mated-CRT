import MatedCRT.FirstPass.Derived.LocalMeshSubsequence

/-!
# Edges starting in a fixed disc vanish with the mesh, along every null sequence

For a continuous proper curve `η : ℝ → ℂ` the cells `η([ε (k - 1), ε k])` that meet a fixed disc have
times in a fixed compact interval, so their diameters are bounded by the modulus of continuity of `η` on that
interval at scale `ε`.  Hence, for every `a > 0`, there is `ε₀ > 0` such that for `0 < ε < ε₀` two vertices with
intersecting cells, the first one embedded in the disc, are at distance `< a` (`exists_eps_forall_dist_vertexPoint_lt`).
Almost surely the curve is continuous and proper and adjacent vertices have intersecting cells, so almost surely, for
every `a > 0`, all edges of the mated-CRT map `𝒢^ε` starting at an embedded vertex in the disc have length `< a`
for all small `ε`, in particular eventually along every null sequence of meshes
(`MatedCRTEnv.IsValid.ae_eventually_local_edges_lt`, which needs no subsequence).
-/

set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- **Local edge lengths for a continuous proper curve.** For `R : ℝ` and `a > 0` there is `ε₀ > 0` such that
for `0 < ε < ε₀` and vertices `j, k` with intersecting cells and `η (ε j) ∈ ball 0 R`, we have
`dist (η (ε j)) (η (ε k)) < a`. -/
theorem exists_eps_forall_dist_vertexPoint_lt {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ j k : ℤ,
      (cell ε η j ∩ cell ε η k).Nonempty → vertexPoint ε η j ∈ ball (0 : ℂ) R →
      dist (vertexPoint ε η j) (vertexPoint ε η k) < a := by
  -- the compact set of times at which `η` is in the closed disc of radius `R + 1`
  obtain ⟨K, hKc, hK⟩ := mem_cocompact.1 (hp (isCompact_closedBall (0 : ℂ) (R + 1)).compl_mem_cocompact)
  obtain ⟨T, hT⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
  have hTime : ∀ t : ℝ, η t ∈ closedBall (0 : ℂ) (R + 1) → |t| ≤ T := by
    intro t ht
    by_contra h
    have hnK : t ∉ K := fun h' => h (by simpa [Real.dist_eq] using hT h')
    exact hK hnK ht
  -- uniform continuity on `[-T - 1, T + 1]`
  have hunif := (isCompact_Icc (a := -T - 1) (b := T + 1)).uniformContinuousOn_of_continuous
    hη.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hunif (min (a / 2) (1 / 2))
    (lt_min (by linarith) (by norm_num))
  have hmin1 : min (a / 2) (1 / 2) ≤ a / 2 := min_le_left _ _
  have hmin2 : min (a / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro ε hε hεδ j k ⟨p, hpj, hpk⟩ hj
  have hεδ' : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨t, ht, rfl⟩ := hpj
  obtain ⟨t', ht', hpt'⟩ := hpk
  simp only [vertexPoint] at hj ⊢
  rw [mem_ball_zero_iff] at hj
  -- time of the vertex `j`
  have hεj : |ε * j| ≤ T := hTime _ (by rw [mem_closedBall_zero_iff]; linarith)
  rw [abs_le] at hεj
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨ht1', ht2'⟩ := ht'
  have hmem1 : ε * j ∈ Icc (-T - 1) (T + 1) := ⟨by linarith [hεj.1], by linarith [hεj.2]⟩
  have hmem2 : t ∈ Icc (-T - 1) (T + 1) :=
    ⟨by linarith [hεj.1], by linarith [hεj.2]⟩
  have hd1 : dist (η t) (η (ε * j)) < min (a / 2) (1 / 2) :=
    hδ' t hmem2 (ε * j) hmem1 (by rw [Real.dist_eq, abs_lt]; constructor <;> nlinarith)
  -- the intersection point lies in the disc of radius `R + 1`
  have hpR : η t ∈ closedBall (0 : ℂ) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖η t‖ ≤ ‖η (ε * j)‖ + dist (η t) (η (ε * j)) := by
      have := norm_le_insert' (η t) (η (ε * j))
      rw [dist_eq_norm]; linarith [norm_sub_rev (η t) (η (ε * j))]
    linarith
  have hTt' : |t'| ≤ T := hTime _ (by rw [hpt']; exact hpR)
  rw [abs_le] at hTt'
  have hmem3 : t' ∈ Icc (-T - 1) (T + 1) := ⟨by linarith [hTt'.1], by linarith [hTt'.2]⟩
  have hmem4 : ε * k ∈ Icc (-T - 1) (T + 1) := ⟨by linarith [hTt'.1], by linarith [hTt'.2]⟩
  have hd2 : dist (η t') (η (ε * k)) < min (a / 2) (1 / 2) :=
    hδ' t' hmem3 (ε * k) hmem4 (by rw [Real.dist_eq, abs_lt]; constructor <;> nlinarith)
  rw [hpt'] at hd2
  calc dist (η (ε * j)) (η (ε * k))
      ≤ dist (η (ε * j)) (η t) + dist (η t) (η (ε * k)) := dist_triangle _ _ _
    _ < a := by rw [dist_comm] at hd1; linarith

/-- **Almost surely the edges starting in a disc vanish with the mesh, along every null sequence.** Almost surely,
for every `a > 0` there is `ε₀ > 0` such that for `0 < ε < ε₀` every edge of `𝒢^ε` (positive multiplicity)
starting at a vertex embedded in `ball 0 R` has embedded length `< a`. -/
theorem MatedCRTEnv.IsValid.ae_exists_eps_local_edges_lt {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (R : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ a : ℝ, 0 < a → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ j k : ℤ,
      S.mult ε ω j k ≠ 0 → vertexPoint ε (S.η ω) j ∈ ball (0 : ℂ) R →
      dist (vertexPoint ε (S.η ω) j) (vertexPoint ε (S.η ω) k) < a := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hη hp hadj
  intro a ha
  obtain ⟨ε₀, hε₀, H⟩ := exists_eps_forall_dist_vertexPoint_lt hη hp R ha
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ j k hm hj => H ε hε hεε₀ j k (hadj ε hε j k hm) hj⟩

/-- **Almost surely the edges starting in a disc are eventually shorter than any `a > 0`, along every null
sequence of meshes.** -/
theorem MatedCRTEnv.IsValid.ae_eventually_local_edges_lt {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {e : ℕ → ℝ} (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) (R : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ j k : ℤ,
      S.mult (e n) ω j k ≠ 0 → vertexPoint (e n) (S.η ω) j ∈ ball (0 : ℂ) R →
      dist (vertexPoint (e n) (S.η ω) j) (vertexPoint (e n) (S.η ω) k) < a := by
  filter_upwards [hS.ae_exists_eps_local_edges_lt hγ hγ2 R] with ω hω
  intro a ha
  obtain ⟨ε₀, hε₀, H⟩ := hω a ha
  filter_upwards [(tendsto_order.1 he0).2 ε₀ hε₀] with n hn
  exact fun j k hm hj => H (e n) (he n) hn j k hm hj

end MatedCRT
