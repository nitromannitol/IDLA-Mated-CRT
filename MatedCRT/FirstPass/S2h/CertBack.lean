import MatedCRT.FirstPass.S2h.CertCode

/-!
# The backward direction of the certificate code (fp-S2h, z1; CHATGPT-cone-good-set.md Sections 3-4)

A code in the analytic set `B` gives certificates for the measure: the moments `certI` of a witness are lintegrals of
the test functions over the interior of the closure of its contact set (`certI_eq_lintegral`), so the Laplacian of the
extended witness is the measure restricted to that set on the dense class of test functions, hence on all test
functions. Dense boundary data `b` on the circle `|x| = 3/4` gives the vanishing of the witness there.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- **Restricted moments of a witness (fp-S2h, z1; CHATGPT (12)).** For a witness `w` of `CertRel` with code `m` of a
locally finite measure, the restricted moment `certI k` is the lintegral of `D k` over the interior of the closure of the
contact set of `w`. -/
theorem certI_eq_lintegral {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (hpole : FrozenGreenDiscPole) {t : ℝ}
    (ht : 0 < t) {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {idx : ℕ → Finset ℕ → ℕ → ℕ} {m : ℕ → ℝ} {D : ℕ → ℂ → ℝ}
    (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (hD0 : ∀ k x, 0 ≤ D k x)
    (hm : ∀ k J n, m (idx k J n) = ∫ x, D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν)
    (w : DiscW) (k : ℕ) :
    certI z U idx m t w k =
      ∫⁻ x in interior (closure (certCluster (3 / 4) t (extW w))), ENNReal.ofReal (D k x) ∂ν := by
  have hDc : HasCompactSupport (D k) := (hD k).2.1
  have hDcont : Continuous (D k) := (hD k).1.continuous
  have hmom := sup_charged_moment_eq (ν := ν) hDcont hDc (hD0 k) U hopen
    (certD z U t w) (fun i hi => by
      rw [certD_iff_subset_closure_cluster hpole ht hopen hne hreg hz hzd w i] at hi
      exact hi.trans (closure_certCluster_sdiff_zero_subset.trans (closedBall_subset_ball (by norm_num))))
  unfold certI
  simp only [hm]
  rw [hmom, iUnion_certD_eq_interior hpole ht hopen hne hreg hz hzd w,
    closure_certCluster_sdiff_zero hpole (by norm_num) ht (extW_continuousOn w)]

/-- **Dense boundary data on the circle (fp-S2h, z1).** There are points `b j` of norm `3/4`, dense on the sphere
`∂B_{3/4}`: every open set meeting the sphere contains some `b j`. -/
theorem exists_sphere_dense_data :
    ∃ b : ℕ → closedBall (0 : ℂ) (3 / 4), (∀ j, ‖(b j : ℂ)‖ = 3 / 4) ∧
      ∀ O : Set ℂ, IsOpen O → (O ∩ sphere (0 : ℂ) (3 / 4)).Nonempty → ∃ j, (b j : ℂ) ∈ O := by
  have hX : Nonempty ↥(sphere (0 : ℂ) (3 / 4)) :=
    ⟨⟨((3 / 4 : ℝ) : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ↥(sphere (0 : ℂ) (3 / 4))
  refine ⟨fun j => ⟨(u j : ℂ), sphere_subset_closedBall (u j).2⟩, fun j => mem_sphere_zero_iff_norm.1 (u j).2, ?_⟩
  intro O hO hne
  obtain ⟨x, hxO, hxp⟩ := hne
  have hO' : IsOpen (Subtype.val ⁻¹' O : Set ↥(sphere (0 : ℂ) (3 / 4))) :=
    hO.preimage continuous_subtype_val
  obtain ⟨j, hj⟩ := hu.exists_mem_open hO' ⟨⟨x, hxp⟩, hxO⟩
  exact ⟨j, hj⟩

end MatedCRT
