import MatedCRT.FirstPass.S5d.StoppedSteps

/-!
# The killing domain contains the cells of a small ball around a target (FIRST PASS, S5e)

Deterministic input of the second Green inequality of the stopped clause (correction [C21], proof of Proposition 5.1;
referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md §5.3, equation (5.6): `V^ε(B_{δ/4}(η(a))) ⊆ I_ε`). For a target `a`
whose cell meets `B⁻_δ(Λ_t)` (`stoppedTargetSet`), every cell meeting `B_r(η(a))` lies in the killing domain
`stoppedKillSet` as soon as `r + d ≤ δ/2`, where `d` bounds the diameters of the cells near `η(a)`, and the floor holds
at level `δ/2`. A label of the killing domain is one whose cell meets `Λ_t` and whose odometer is positive, which puts it
in the discrete cluster (`mem_matedDiscreteCluster_of_odometer_pos`).
-/

open MeasureTheory Set Metric

namespace MatedCRT.S5e

/-- A vertex of `cellVertices (ball 0 ρ)` with positive stopped odometer lies in the discrete cluster: on the closed
ball the odometer is `w̃ - φ`, and the cluster is `{a ∈ W | φ a < w̃ a}` (`discreteCluster`). -/
theorem mem_matedDiscreteCluster_of_odometer_pos {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ} {k : ℤ}
    (hk : k ∈ cellVertices ε η (ball 0 ρ)) (hpos : 0 < stoppedOdometer m ε η ρ t k) :
    k ∈ matedDiscreteCluster m ε η ρ t := by
  obtain ⟨y, hyc, hyb⟩ := hk
  have hkc : k ∈ cellVertices ε η (closedBall 0 ρ) := ⟨y, hyc, ball_subset_closedBall hyb⟩
  unfold stoppedOdometer at hpos
  simp only [hkc, ↓reduceIte] at hpos
  exact ⟨⟨y, hyc, hyb⟩, by linarith⟩

/-- **Killing domain contains the cells of a small ball around a target.** Let `a` be a target (its cell meets
`innerNbhd δ (Λ t)`) and let `d` bound the diameter of every cell meeting `B_r(η a)`. If `r + d ≤ δ/2`,
`Λ t ⊆ B_{ρ/3}`, `t < clusterExitTime`, and the floor holds at level `δ/2`, then every interior vertex of `B_r(η a)`
lies in `stoppedKillSet S Λ ρ t ε ω`. -/
theorem interiorCellVertices_subset_stoppedKillSet {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Λ : Ω → ℝ → Set ℂ) (ω : Ω) {ρ t δ ε r d : ℝ} (a : ℤ)
    (hε : 0 < ε) (hρ : 0 < ρ) (hδ : 0 < δ) (hr : 0 < r) (hrd : r + d ≤ δ / 2)
    (hT : t < clusterExitTime (Λ ω) ρ) (hΛsub : Λ ω t ⊆ ball 0 (ρ / 3))
    (hfloor : ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
      0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k)
    (ha : a ∈ cellVertices ε (S.η ω) (innerNbhd δ (Λ ω t)))
    (hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (vertexPoint ε (S.η ω) a) r).Nonempty →
      ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ d) :
    interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r) ⊆ stoppedKillSet S Λ ρ t ε ω := by
  -- the vertex point lies in its own cell
  have hva : vertexPoint ε (S.η ω) a ∈ cell ε (S.η ω) a := by
    refine ⟨ε * a, ⟨?_, le_rfl⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  obtain ⟨y0, hy0c, hy0⟩ := ha
  -- every point of the complement of `Λ t` is at distance `≥ δ` from `y0`
  have hy0far : ∀ z ∉ Λ ω t, δ ≤ dist y0 z := by
    intro z hz
    have h1 : ENNReal.ofReal δ ≤ edist y0 z :=
      le_trans hy0.2 (Metric.infEDist_le_edist_of_mem hz)
    rw [edist_dist] at h1
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 h1
  have hd0 : dist (vertexPoint ε (S.η ω) a) y0 ≤ d :=
    hdiam a ⟨vertexPoint ε (S.η ω) a, hva, mem_ball_self hr⟩ _ hva y0 hy0c
  have hfar : ∀ z ∉ Λ ω t, δ - d ≤ dist (vertexPoint ε (S.η ω) a) z := by
    intro z hz
    have h1 := hy0far z hz
    have h2 := dist_triangle y0 (vertexPoint ε (S.η ω) a) z
    have h3 : dist y0 (vertexPoint ε (S.η ω) a) ≤ d := by rw [dist_comm]; exact hd0
    linarith
  intro k hk
  obtain ⟨x, hxc, hxb⟩ := hk.1
  -- points of the cell in the ball are at distance `≥ δ/2` from the complement of `Λ t`
  have hxfar : ∀ z ∉ Λ ω t, δ / 2 ≤ dist x z := by
    intro z hz
    have h1 := hfar z hz
    have h2 : dist (vertexPoint ε (S.η ω) a) x < r := by
      rw [dist_comm]; exact Metric.mem_ball.1 hxb
    have h3 := dist_triangle (vertexPoint ε (S.η ω) a) x z
    linarith
  have hxX : x ∈ Λ ω t := by
    by_contra h
    have h1 := hxfar x h
    rw [dist_self] at h1
    linarith
  have hinf : ENNReal.ofReal (δ / 2) ≤ Metric.infEDist x (Λ ω t)ᶜ :=
    Metric.le_infEDist.2 fun z hz => by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hxfar z hz)
  have hodo := hfloor k ⟨x, hxc, hxX, hinf⟩
  have hkball : k ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    ⟨x, hxc, Metric.ball_subset_ball (by linarith) (hΛsub hxX)⟩
  show t < clusterExitTime (Λ ω) ρ ∧ k ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ∧
    k ∈ cellVertices ε (S.η ω) (Λ ω t)
  exact ⟨hT, mem_matedDiscreteCluster_of_odometer_pos hkball hodo, ⟨x, hxc, hxX⟩⟩

end MatedCRT.S5e
