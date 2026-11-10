import MatedCRT.FirstPass.S2h.CertMoment

/-!
# Forward certificate relation: the clauses C1-C3 and the witness (fp-S2h, z1)

The forward direction of the code relation (CHATGPT-cone-good-set.md Section 3, C1-C3 (15)-(18)): a certificate `w` of
`CertReal` (Family.lean) restricted to `B̄_{3/4}` gives the witness of `CertRel` for the data `z` (punctured dense) and `b`
(on the circle). Clause C4 (the Laplacian identity against the restricted moments) is the next step (CertForward2).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The witness `C(B̄_{3/4}, ℝ)` of a candidate continuous on `B̄_{3/4}`: the restriction of `w`. -/
noncomputable def discOfCert {w : ℂ → ℝ} (hw : ContinuousOn w (closedBall (0 : ℂ) (3 / 4))) : DiscW :=
  ⟨(closedBall (0 : ℂ) (3 / 4)).domRestrict w, continuousOn_iff_continuous_domRestrict.1 hw⟩

/-- **Clauses C1-C3 of the relation (fp-S2h, z1).** For a certificate `w` of `CertReal`, with witness `w'` agreeing with
`w` on `B̄_{3/4}`: the raw field is nonnegative at the data points (C1), the boundary values vanish at the circle data
(C2), positive raw data lie in `B̄_{1/2}` (C3), and positive raw data approach the circle `|x| = 1/2` (C3, second part). -/
theorem certRel_clauses_C1_C3 {ν : Measure ℂ} {t : ℝ} (hpole : FrozenGreenDiscPole) (ht : 0 < t) {w : ℂ → ℝ}
    (hw : CertReal ν t w) {z : ℕ → closedBall (0 : ℂ) (3 / 4)}
    (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {b : ℕ → closedBall (0 : ℂ) (3 / 4)} (hb : ∀ j, ‖(b j : ℂ)‖ = 3 / 4)
    (w' : DiscW) (hw' : ∀ y : closedBall (0 : ℂ) (3 / 4), w' y = w y) :
    (∀ j, 0 ≤ certRaw t w' (z j)) ∧ (∀ j, w' (b j) = 0) ∧
      (∀ j, 0 < certRaw t w' (z j) → ‖(z j : ℂ)‖ ≤ 1 / 2) ∧
      (∀ n : ℕ, ∃ j, 0 < certRaw t w' (z j) ∧ (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖(z j : ℂ)‖) := by
  have hraw : ∀ j, certRaw t w' (z j) = w (z j) + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (z j : ℂ) := by
    intro j
    unfold certRaw
    rw [hw' (z j)]
  refine ⟨fun j => ?_, fun j => ?_, fun j hj => ?_, fun n => ?_⟩
  · rw [hraw j]
    have := hw.2.1 (z j : ℂ) (z j).2 (hz j).2
    linarith
  · rw [hw' (b j)]
    exact hw.2.2.1 (b j : ℂ) (mem_sphere_zero_iff_norm.2 (hb j))
  · rw [hraw j] at hj
    have hmem : (z j : ℂ) ∈ certCluster (3 / 4) t w := ⟨(hz j).1, Or.inr (by linarith)⟩
    exact mem_closedBall_zero_iff.1 (hw.2.2.2.1 (subset_closure hmem))
  · -- the point of the contact set at distance `1/2` gives positive data at distance close to `1/2`
    obtain ⟨x, hxcl, hx⟩ := hw.2.2.2.2.1
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hbnd : (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖x‖ := by
      rw [hx]
      linarith
    have hClo : IsOpen (certCluster (3 / 4) t w) := isOpen_certCluster hpole (by norm_num) ht hw.1
    have hCo : IsOpen (certCluster (3 / 4) t w \ {0}) := hClo.sdiff isClosed_singleton
    have hsub : certCluster (3 / 4) t w ⊆ closure (certCluster (3 / 4) t w \ {0}) := by
      intro y hy
      have h1 := (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter hClo hy
      have heq : (certCluster (3 / 4) t w ∩ {(0 : ℂ)}ᶜ) = certCluster (3 / 4) t w \ {0} := by
        ext y
        simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_sdiff]
      rw [heq] at h1
      exact h1
    have hxC : x ∈ closure (certCluster (3 / 4) t w \ {0}) := closure_minimal hsub isClosed_closure hxcl
    have hVo : IsOpen {y : ℂ | (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    obtain ⟨y, hyV, hyC⟩ := mem_closure_iff.1 hxC _ hVo hbnd
    obtain ⟨j, hj⟩ := hzd ({y : ℂ | (1 / 2 : ℝ) * (1 - 1 / ((n : ℝ) + 2)) < ‖y‖} ∩
        (certCluster (3 / 4) t w \ {0})) (hVo.inter hCo)
      ⟨y, ⟨hyV, hyC⟩, hyC.1.1, hyC.2⟩
    refine ⟨j, ?_, hj.1⟩
    rw [hraw j]
    have hlt : -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (z j : ℂ) < w (z j) := by
      rcases hj.2.1.2 with h0 | h1
      · exact absurd (mem_singleton_iff.2 h0) hj.2.2
      · exact h1
    linarith

end MatedCRT
