import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterCriterion

/-! # Approximate coverage from a dense noncoincidence set -/

namespace MatedCRT

open Set Metric Filter Topology

/-- A compact subset of the closure of a set has a finite spatial net with
centres in that set. -/
theorem exists_finite_subset_thickening_of_isCompact {K D : Set ℂ}
    (hK : IsCompact K) (hKD : K ⊆ closure D) {a : ℝ} (ha : 0 < a) :
    ∃ F : Set ℂ, F.Finite ∧ F ⊆ D ∧ K ⊆ thickening a F := by
  classical
  let U : D → Set ℂ := fun y => ball y.1 a
  have hcover : K ⊆ ⋃ y : D, U y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hKD hx) a ha
    simp only [mem_iUnion]
    exact ⟨⟨y, hy⟩, by simpa [U, dist_comm] using hxy⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  let F : Set ℂ := Subtype.val '' (↑T : Set D)
  have hfin : F.Finite := T.finite_toSet.image Subtype.val
  refine ⟨F, hfin, ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.2
  · intro x hx
    have hxT := hT hx
    simp only [mem_iUnion] at hxT
    obtain ⟨y, hyT, hxy⟩ := hxT
    apply Metric.mem_thickening_iff.mpr
    refine ⟨y.1, ⟨y, hyT, rfl⟩, ?_⟩
    simpa [U, dist_comm] using hxy

/-- An open obstacle cluster lies in the closure of its strict
noncoincidence points away from the pole. -/
theorem cluster_subset_closure_scaled_noncoincidence
    {μ : MeasureTheory.Measure ℂ} {ρ t c : ℝ} (hc : 0 < c)
    (hopen : IsOpen (HarmonicBalls.cluster μ ρ 0 t)) :
    HarmonicBalls.cluster μ ρ 0 t ⊆ closure {x ∈ ball (0 : ℂ) ρ |
      x ≠ 0 ∧ -t * c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x <
        c * HarmonicBalls.leastSupersolution μ ρ 0 t x} := by
  have hdense : Dense (({0} : Set ℂ)ᶜ) := dense_compl_singleton 0
  have hsub : HarmonicBalls.cluster μ ρ 0 t ∩ ({0} : Set ℂ)ᶜ ⊆
      {x ∈ ball (0 : ℂ) ρ | x ≠ 0 ∧
        -t * c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x <
          c * HarmonicBalls.leastSupersolution μ ρ 0 t x} := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx.2
    rcases hx.1.2 with hzero | hlt
    · exact (hx0 hzero).elim
    · refine ⟨hx.1.1, hx0, ?_⟩
      have h := mul_lt_mul_of_pos_left hlt hc
      nlinarith
  exact (hdense.open_subset_closure_inter hopen).trans (closure_mono hsub)

/-- Before exit, every point of the cone harmonic ball is approximated by
strict noncoincidence points away from the pole, provided the local obstacle
cluster is open. -/
theorem coneFamily_subset_closure_scaled_noncoincidence
    {μ : MeasureTheory.Measure ℂ} [MeasureTheory.IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} {ρ t c : ℝ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    (hρ : 0 < ρ) (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) (hc : 0 < c)
    (hopen : IsOpen (HarmonicBalls.cluster μ ρ 0 t)) :
    Λ t ⊆ closure {x ∈ ball (0 : ℂ) ρ | x ≠ 0 ∧
      -t * c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x <
        c * HarmonicBalls.leastSupersolution μ ρ 0 t x} := by
  obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hΛ ht).mp hT
  have hsub : Λ t ⊆ ball 0 (ρ / 3) :=
    (hΛ.2.1.monotoneOn ht (ht.trans htq) htq.le).trans hq
  have heq := (hΛ.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
  rw [heq]
  exact interior_subset.trans (closure_minimal
    (cluster_subset_closure_scaled_noncoincidence hc hopen) isClosed_closure)

/-- Pointwise convergence is uniform on a finite set. -/
theorem tendstoUniformlyOn_of_finite_pointwise {F : Set ℂ} (hF : F.Finite)
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (h : ∀ x ∈ F, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop F := by
  intro U hU
  apply hF.eventually_all.mpr
  intro x hx
  have hs := tendstoUniformlyOn_singleton_iff_tendsto.mpr (h x hx)
  filter_upwards [hs U hU] with n hn
  exact hn x (mem_singleton x)

/-- Uniform approximation of the obstacle and least supersolution covers a
compact set up to any positive spatial tolerance when the compact set lies in
the closure of the strict noncoincidence set. -/
theorem eventually_subset_thickening_fillCells_of_dense_strict_gap
    {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {ρ t a : ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {w φ : ℂ → ℝ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n) (hmε : ∀ n, 0 ≤ mε n)
    (hcompact : IsCompact K) (ha : 0 < a)
    (hclose : K ⊆ closure {x ∈ ball (0 : ℂ) ρ | x ≠ 0 ∧ φ x < w x})
    (hw : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 →
      Tendsto (fun n => rescale (mε n) (ε n) η
        (matedLeastSupersolution (m n) (ε n) η ρ t) x) atTop (𝓝 (w x)))
    (hφ : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 →
      Tendsto (fun n => rescale (mε n) (ε n) η
        (matedObstacle (m n) (ε n) η ρ t) x) atTop (𝓝 (φ x))) :
    ∀ᶠ n in atTop, K ⊆ thickening a
      (fillCells (ε n) η (matedDiscreteCluster (m n) (ε n) η ρ t)) := by
  obtain ⟨F, hF, hFD, hKF⟩ := exists_finite_subset_thickening_of_isCompact hcompact hclose ha
  have hFball : F ⊆ ball (0 : ℂ) ρ := fun _ hx => (hFD hx).1
  have he := eventually_subset_fillCells_matedDiscreteCluster_of_strict_gap hη hp hsurj hε hmε
    hFball hF.isCompact (hF.continuousOn w) (hF.continuousOn φ)
    (fun x hx => (hFD hx).2.2)
    (tendstoUniformlyOn_of_finite_pointwise hF (fun x hx => hw x (hFball hx) (hFD hx).2.1))
    (tendstoUniformlyOn_of_finite_pointwise hF (fun x hx => hφ x (hFball hx) (hFD hx).2.1))
  filter_upwards [he] with n hn
  exact hKF.trans (Metric.thickening_subset_of_subset a hn)

/-- Before exit, pointwise convergence away from the pole covers the compact
inner neighbourhood up to any prescribed positive spatial tolerance. -/
theorem eventually_innerNbhd_subset_thickening_fillCells
    {μ : MeasureTheory.Measure ℂ} [MeasureTheory.IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ}
    {ρ t c δ a : ℝ} {η : ℝ → ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) (hc : 0 < c) (hδ : 0 < δ) (ha : 0 < a)
    (hopen : IsOpen (HarmonicBalls.cluster μ ρ 0 t))
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n) (hmε : ∀ n, 0 ≤ mε n)
    (hw : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 →
      Tendsto (fun n => rescale (mε n) (ε n) η
        (matedLeastSupersolution (m n) (ε n) η ρ t) x) atTop
          (𝓝 (c * HarmonicBalls.leastSupersolution μ ρ 0 t x)))
    (hφ : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 →
      Tendsto (fun n => rescale (mε n) (ε n) η
        (matedObstacle (m n) (ε n) η ρ t) x) atTop
          (𝓝 (-t * c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x))) :
    ∀ᶠ n in atTop, innerNbhd δ (Λ t) ⊆ thickening a
      (fillCells (ε n) η (matedDiscreteCluster (m n) (ε n) η ρ t)) := by
  apply eventually_subset_thickening_fillCells_of_dense_strict_gap hη hp hsurj hε hmε
    (coneFamily_innerNbhd_compact_subset hΛ hρ ht hT hδ).1 ha ?_ hw hφ
  intro x hx
  exact coneFamily_subset_closure_scaled_noncoincidence hΛ hρ ht hT hc hopen hx.1

end MatedCRT
