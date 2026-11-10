import MatedCRT.FirstPass.S2h.CertDense

/-!
# The certificate of a code (fp-S2h, z1; CHATGPT-cone-good-set.md Section 4.1 hypotheses, Section 3)

A relation witness `w` of `CertRel` for a locally finite measure gives a certificate `CertSuper` of `CertReal` for its
extension `extW w`: the obstacle inequality off the pole (density of the data `z` and continuity of the Green function,
`FrozenGreenDiscPole`), the boundary values (density of the data `b` on the circle), the contact set in `B̄_{1/2}` and
reaching the circle `|x| = 1/2` (clauses C3, C3b), and the Laplacian identity (`lap_identity_test`). The supersolution
inequality `Δw ≤ ν` follows from `Δw = ν|_A ≤ ν`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The extension of a witness vanishes off the closed disc. -/
theorem extW_eq_zero_of_notMem {w : DiscW} {x : ℂ} (hx : x ∉ closedBall (0 : ℂ) (3 / 4)) : extW w x = 0 := by
  simp [extW, hx]

/-- A function continuous on an open set which is nonnegative on a family dense in the set is nonnegative there. -/
theorem nonneg_of_dense_open {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℝ} (hF : ContinuousOn F U)
    (z : ℕ → ℂ) (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ U).Nonempty → ∃ j, z j ∈ O)
    (hz0 : ∀ j, 0 ≤ F (z j)) : ∀ x ∈ U, 0 ≤ F x := by
  intro x hx
  by_contra hneg
  rw [not_le] at hneg
  have hev : ∀ᶠ y in 𝓝 x, F y < 0 := (hF.continuousAt (hU.mem_nhds hx)).tendsto.eventually (Iio_mem_nhds hneg)
  obtain ⟨O, hOsub, hOo, hxO⟩ := _root_.mem_nhds_iff.1 hev
  obtain ⟨j, hj⟩ := hzd O hOo ⟨x, hxO, hx⟩
  have hlt : F (z j) < 0 := hOsub hj
  exact absurd (hz0 j) (not_le.2 hlt)

/-- A function continuous on the closed disc which vanishes on a dense family of the circle vanishes on the circle. -/
theorem eq_zero_on_sphere_of_dense {F : ℂ → ℝ} (hF : ContinuousOn F (closedBall (0 : ℂ) (3 / 4)))
    (b : ℕ → ℂ) (hbS : ∀ j, b j ∈ sphere (0 : ℂ) (3 / 4))
    (hbd : ∀ O : Set ℂ, IsOpen O → (O ∩ sphere (0 : ℂ) (3 / 4)).Nonempty → ∃ j, b j ∈ O)
    (hb0 : ∀ j, F (b j) = 0) : ∀ x ∈ sphere (0 : ℂ) (3 / 4), F x = 0 := by
  intro x hx
  have hxc : x ∈ closedBall (0 : ℂ) (3 / 4) := sphere_subset_closedBall hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : ∀ᶠ y in 𝓝 x, y ∈ closedBall (0 : ℂ) (3 / 4) → F y < 0 :=
      eventually_nhdsWithin_iff.1 ((hF x hxc).tendsto.eventually (Iio_mem_nhds hneg))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h1
    obtain ⟨j, hj⟩ := hbd (ball x δ) isOpen_ball ⟨x, mem_ball_self hδ, hx⟩
    have h2 := hball (mem_ball.1 hj) (sphere_subset_closedBall (hbS j))
    rw [hb0 j] at h2
    exact lt_irrefl 0 h2
  · have h1 : ∀ᶠ y in 𝓝 x, y ∈ closedBall (0 : ℂ) (3 / 4) → 0 < F y :=
      eventually_nhdsWithin_iff.1 ((hF x hxc).tendsto.eventually (Ioi_mem_nhds hpos))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h1
    obtain ⟨j, hj⟩ := hbd (ball x δ) isOpen_ball ⟨x, mem_ball_self hδ, hx⟩
    have h2 := hball (mem_ball.1 hj) (sphere_subset_closedBall (hbS j))
    rw [hb0 j] at h2
    exact lt_irrefl 0 h2

/-- The raw field is positive at a point of the contact set off the pole. -/
theorem certRaw_pos_of_mem_cluster {t : ℝ} {w : DiscW} {x : closedBall (0 : ℂ) (3 / 4)}
    (hx : (x : ℂ) ∈ certCluster (3 / 4) t (extW w)) (hx0 : (x : ℂ) ≠ 0) : 0 < certRaw t w x := by
  rcases hx.2 with h0 | h1
  · exact absurd h0 hx0
  · rw [extW_apply] at h1
    unfold certRaw
    linarith

/-- The obstacle inequality off the pole, from the data `z` and the Green function continuity (C1). -/
theorem obstacle_extW (hpole : FrozenGreenDiscPole) {t : ℝ} {w : DiscW}
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)}
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    (hC1 : ∀ j, 0 ≤ certRaw t w (z j)) :
    ∀ x ∈ ball (0 : ℂ) (3 / 4) \ {0}, -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ extW w x := by
  have hU : IsOpen (ball (0 : ℂ) (3 / 4) \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hF : ContinuousOn (fun y => extW w y + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 y)
      (ball (0 : ℂ) (3 / 4) \ {0}) := by
    refine ContinuousOn.add ((extW_continuousOn w).mono fun y hy => ball_subset_closedBall hy.1) ?_
    exact continuousOn_const.mul ((hpole (3 / 4) (by norm_num)).1.mono fun y hy =>
      ⟨ball_subset_closedBall hy.1, hy.2⟩)
  have hz0 : ∀ j, 0 ≤ extW w (z j) + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (z j) := fun j => by
    rw [extW_apply]
    exact hC1 j
  intro x hx
  have h : 0 ≤ extW w x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x :=
    nonneg_of_dense_open hU hF (fun j => (z j : ℂ)) hzd hz0 x hx
  linarith

/-- The closure of the contact set lies in `B̄_{1/2}` (CertRel C3 and the density of the data `z`). -/
theorem closure_cluster_subset_half (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t) {w : DiscW}
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    (hC3 : ∀ j, 0 < certRaw t w (z j) → ‖(z j : ℂ)‖ ≤ 1 / 2) :
    closure (certCluster (3 / 4) t (extW w)) ⊆ closedBall (0 : ℂ) (1 / 2) := by
  intro y hy
  by_contra hy'
  rw [mem_closedBall_zero_iff, not_le] at hy'
  have hO : IsOpen {x : ℂ | 1 / 2 < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hCo : IsOpen (certCluster (3 / 4) t (extW w)) :=
    isOpen_certCluster hpole (by norm_num) ht (extW_continuousOn w)
  obtain ⟨x, hxO, hxC⟩ := mem_closure_iff.1 hy _ hO hy'
  have hxn : 1 / 2 < ‖x‖ := hxO
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hxn
    norm_num at hxn
  obtain ⟨j, hj⟩ := hzd ({x : ℂ | 1 / 2 < ‖x‖} ∩ certCluster (3 / 4) t (extW w)) (hO.inter hCo)
    ⟨x, ⟨hxO, hxC⟩, hxC.1, hx0⟩
  have hraw := certRaw_pos_of_mem_cluster hj.2 (by simpa using (hz j).2)
  have h3 := hC3 j hraw
  have h4 : 1 / 2 < ‖(z j : ℂ)‖ := hj.1
  linarith

/-- The contact set reaches the circle `|x| = 1/2` (CertRel C3b and compactness of the closure). -/
theorem exists_norm_half_mem_closure (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t) {w : DiscW}
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    (hC3 : ∀ j, 0 < certRaw t w (z j) → ‖(z j : ℂ)‖ ≤ 1 / 2)
    (hC3b : ∀ n : ℕ, ∃ j, 0 < certRaw t w (z j) ∧ (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖(z j : ℂ)‖) :
    ∃ x ∈ closure (certCluster (3 / 4) t (extW w)), ‖x‖ = 1 / 2 := by
  have hsub := closure_cluster_subset_half hpole ht hz hzd hC3
  have hcpt : IsCompact (closure (certCluster (3 / 4) t (extW w))) :=
    (isCompact_closedBall (0 : ℂ) (1 / 2)).of_isClosed_subset isClosed_closure hsub
  have hmemC : ∀ j, 0 < certRaw t w (z j) → (z j : ℂ) ∈ certCluster (3 / 4) t (extW w) := fun j hj =>
    ⟨(hz j).1, Or.inr (by rw [extW_apply]; unfold certRaw at hj; linarith)⟩
  have hne : (closure (certCluster (3 / 4) t (extW w))).Nonempty := by
    obtain ⟨j, hj⟩ := hC3b 0
    exact ⟨z j, subset_closure (hmemC j hj.1)⟩
  obtain ⟨x, hxC, hxmax⟩ := hcpt.exists_isMaxOn hne continuous_norm.continuousOn
  have hxmax' : ∀ y ∈ closure (certCluster (3 / 4) t (extW w)), ‖y‖ ≤ ‖x‖ := fun y hy => isMaxOn_iff.1 hxmax y hy
  have hxle : ‖x‖ ≤ 1 / 2 := mem_closedBall_zero_iff.1 (hsub hxC)
  refine ⟨x, hxC, le_antisymm hxle ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 2 * (1 / 2 - ‖x‖) by linarith)
  have hn2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨j, hjpos, hjn⟩ := hC3b n
  have hj := hxmax' (z j) (subset_closure (hmemC j hjpos))
  linarith

/-- **A code witness gives a certificate (fp-S2h, z1; CHATGPT Section 3).** A relation witness `w` of `CertRel` for a
locally finite measure gives a supersolution certificate `CertSuper ν t (extW w)`. -/
theorem certSuper_of_certRel {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (hpole : FrozenGreenDiscPole) {t : ℝ}
    (ht : 0 < t) {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {b : ℕ → closedBall (0 : ℂ) (3 / 4)} (hb : ∀ j, ‖(b j : ℂ)‖ = 3 / 4)
    (hbd : ∀ O : Set ℂ, IsOpen O → (O ∩ sphere (0 : ℂ) (3 / 4)).Nonempty → ∃ j, (b j : ℂ) ∈ O)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {idx : ℕ → Finset ℕ → ℕ → ℕ} {m : ℕ → ℝ} {D : ℕ → ℂ → ℝ}
    (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (hD0 : ∀ k x, 0 ≤ D k x)
    (hDmem : ∀ k, D k ∈ nonnegTest (3 / 4))
    (hdense : ∀ φ ∈ nonnegTest (3 / 4), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (3 / 4),
      |φ x - D k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (D k) x| < ε)
    (hm : ∀ k J n, m (idx k J n) = ∫ x, D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν)
    {w : DiscW} (hw : CertRel z b U idx (certL D) m t w) :
    CertSuper ν t (extW w) := by
  have hW : ContinuousOn (extW w) (closedBall (0 : ℂ) (3 / 4)) := extW_continuousOn w
  have hW0 : ∀ x, x ∉ closedBall (0 : ℂ) (3 / 4) → extW w x = 0 := fun x hx => extW_eq_zero_of_notMem hx
  have hAm : MeasurableSet (interior (closure (certCluster (3 / 4) t (extW w)))) := isOpen_interior.measurableSet
  have hA : interior (closure (certCluster (3 / 4) t (extW w))) ⊆ closedBall (0 : ℂ) (3 / 4) :=
    interior_subset.trans (closure_minimal (fun y hy => ball_subset_closedBall hy.1) isClosed_closedBall)
  -- the Laplacian identity on the dense class, from the moment identities of the relation
  have hid : ∀ k, ∫ x, extW w x * Laplacian.laplacian (D k) x =
      ∫ x, D k x ∂(ν.restrict (interior (closure (certCluster (3 / 4) t (extW w))))) := by
    intro k
    have h1 : certL D k w = (certI z U idx m t w k).toReal := (hw.2.2.2.2 k).2
    rw [certI_eq_lintegral hpole ht hopen hne hreg hz hzd hD hD0 hm w k] at h1
    have h2 : ∫ x, extW w x * Laplacian.laplacian (D k) x =
        (∫⁻ x in interior (closure (certCluster (3 / 4) t (extW w))), ENNReal.ofReal (D k x) ∂ν).toReal := h1
    rw [h2]
    exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hD0 k))
      (hD k).1.continuous.aestronglyMeasurable).symm
  -- boundary values on the circle
  have hb0 : ∀ j, extW w (b j : ℂ) = 0 := fun j => (extW_apply w (b j)).trans (hw.2.1 j)
  have hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), extW w x = 0 :=
    eq_zero_on_sphere_of_dense hW (fun j => (b j : ℂ)) (fun j => mem_sphere_zero_iff_norm.2 (hb j)) hbd hb0
  -- the obstacle on the closed disc
  have hobs : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 →
      -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ extW w x := by
    intro x hx hx0
    by_cases hxb : x ∈ ball (0 : ℂ) (3 / 4)
    · exact obstacle_extW hpole hzd hw.1 x ⟨hxb, hx0⟩
    · have hs : x ∈ sphere (0 : ℂ) (3 / 4) := by
        rw [mem_closedBall_zero_iff] at hx
        rw [mem_ball_zero_iff, not_lt] at hxb
        exact mem_sphere_zero_iff_norm.2 (le_antisymm hx hxb)
      rw [hsph x hs]
      have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := 3 / 4)) 0 x
      have := mul_nonneg ht.le hG
      linarith
  have hcert : CertReal ν t (extW w) := by
    unfold CertReal
    refine ⟨hW, hobs, hsph, closure_cluster_subset_half hpole ht hz hzd hw.2.2.1, ?_, ?_⟩
    · exact exists_norm_half_mem_closure hpole ht hz hzd hw.2.2.1 hw.2.2.2.1
    · refine ⟨(hW.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ => ⟨?_, ?_, ?_⟩⟩
      · exact (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1)
      · exact integrable_zero_measure
      · rw [integral_zero_measure, sub_zero]
        exact lap_identity_test hW hW0 hAm hA hDmem hdense hid hφ
  refine ⟨hcert, ?_⟩
  refine ⟨hW, ⟨(hW.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ hφ0 hφi => ?_⟩, hobs⟩
  rw [lap_identity_test hW hW0 hAm hA hDmem hdense hid hφ]
  exact setIntegral_le_integral hφi (ae_of_all _ fun x => hφ0 x)

end MatedCRT
