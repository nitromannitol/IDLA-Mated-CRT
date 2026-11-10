import MatedCRT.FirstPass.S2h.CertForward
import MatedCRT.FirstPass.S2h.CertMoment

/-!
# The Laplacian clause C4 of the witness (fp-S2h, z1; CHATGPT-cone-good-set.md (12) and (20))

For a certificate `w` of `CertReal ν t` with witness `w'` (`discOfCert`, extended by `extW`), the charged balls of
CHATGPT (9) are exactly the balls inside the interior of the closure of the punctured contact set. Hence the restricted
moments `certI` of `CertRel` are `ν`-integrals of the test function `D k` over `A = interior (closure (certCluster 3/4 t w))`,
and the Laplacian pairing `L k w'` equals `∫_A D_k dν`, by the Laplacian clause of `CertReal` (HasLaplacian with negative
part `0`, Armitage-Gardiner / Duplantier-Sheffield Laplacian of a measure).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The contact set depends only on the candidate on the open disc `B_R`. -/
theorem certCluster_congr (R t : ℝ) {w v : ℂ → ℝ} (h : ∀ x ∈ ball (0 : ℂ) R, w x = v x) :
    certCluster R t w = certCluster R t v := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rcases hx' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by rw [← h x hx]; exact h1)
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rcases hx' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by rw [h x hx]; exact h1)

/-- The witness `w'` of `discOfCert` extended by `extW` agrees with the candidate on the closed disc `B̄_{3/4}`. -/
theorem extW_eq_of_closedBall {w : ℂ → ℝ} {w' : DiscW} (hw' : ∀ y : closedBall (0 : ℂ) (3 / 4), w' y = w y) :
    ∀ x ∈ closedBall (0 : ℂ) (3 / 4), extW w' x = w x := fun x hx =>
  (extW_apply w' ⟨x, hx⟩).trans (hw' ⟨x, hx⟩)

/-- The contact set of the extended witness is the contact set of the candidate. -/
theorem certCluster_extW_eq (t : ℝ) {w : ℂ → ℝ} {w' : DiscW}
    (hw' : ∀ y : closedBall (0 : ℂ) (3 / 4), w' y = w y) :
    certCluster (3 / 4) t (extW w') = certCluster (3 / 4) t w :=
  certCluster_congr (3 / 4) t fun x hx => extW_eq_of_closedBall hw' x (ball_subset_closedBall hx)

/-- Removing the pole does not change the closure of an open contact set (Armitage-Gardiner: the pole is a
removable point of the closure of the cluster, `Dense.open_subset_closure_inter`). -/
theorem closure_certCluster_sdiff_zero (hpole : FrozenGreenDiscPole) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    {w : ℂ → ℝ} (hw : ContinuousOn w (closedBall (0 : ℂ) R)) :
    closure (certCluster R t w \ {0}) = closure (certCluster R t w) := by
  have hClo : IsOpen (certCluster R t w) := isOpen_certCluster hpole hR ht hw
  refine Subset.antisymm (closure_mono sdiff_subset) ?_
  refine closure_minimal ?_ isClosed_closure
  intro y hy
  have h1 := (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter hClo hy
  have heq : (certCluster R t w ∩ {(0 : ℂ)}ᶜ) = certCluster R t w \ {0} := by
    ext y
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_sdiff]
  rw [heq] at h1
  exact h1

/-- The closure of the punctured contact set lies in the closed disc `B̄_{3/4}`. -/
theorem closure_certCluster_sdiff_zero_subset {t : ℝ} {w : ℂ → ℝ} :
    closure (certCluster (3 / 4) t w \ {0}) ⊆ closedBall (0 : ℂ) (3 / 4) :=
  closure_minimal (fun _ hx => ball_subset_closedBall hx.1.1) isClosed_closedBall

/-- The interior of the closure of the punctured contact set of the extended witness is the interior of the closure
of the contact set of the candidate. -/
theorem interior_closure_extW_eq (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t) {w : ℂ → ℝ} {w' : DiscW}
    (hw' : ∀ y : closedBall (0 : ℂ) (3 / 4), w' y = w y) :
    interior (closure (certCluster (3 / 4) t (extW w') \ {0})) =
      interior (closure (certCluster (3 / 4) t w)) := by
  have hwc : ContinuousOn (extW w') (closedBall (0 : ℂ) (3 / 4)) := extW_continuousOn w'
  rw [closure_certCluster_sdiff_zero hpole (by norm_num) ht hwc, certCluster_extW_eq t hw']

/-- The charged balls of CHATGPT (9) for the extended witness exhaust the interior of the closure of the punctured
contact set (`certD_iff_subset_closure_cluster` and `interior_closure_eq_iUnion`). -/
theorem iUnion_certD_eq_interior (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    (w : DiscW) :
    (⋃ (i : ℕ), ⋃ (_ : certD z U t w i), U i) =
      interior (closure (certCluster (3 / 4) t (extW w) \ {0})) := by
  rw [interior_closure_eq_iUnion hopen hreg]
  ext x
  simp only [mem_iUnion, exists_prop, certD_iff_subset_closure_cluster hpole ht hopen hne hreg hz hzd]

/-- **Clause C4 of the witness (fp-S2h, z1; CHATGPT (12), (20)).** Let `w` be a certificate of `CertReal ν t` and let
`w'` be its witness on `B̄_{3/4}`. For a family `D k` of nonnegative test functions on `B_{3/4}` and moments `m` with
the cutoff form of CHATGPT (12), the restricted moment `certI k` is finite and equals `∫_A D_k dν` on
`A = interior (closure (certCluster 3/4 t w))`, and the Laplacian pairing `L k w'` equals the same integral. -/
theorem certC4_of_cert {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] (hpole : FrozenGreenDiscPole) {t : ℝ}
    (ht : 0 < t) {w : ℂ → ℝ} (hw : CertReal ν t w)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {idx : ℕ → Finset ℕ → ℕ → ℕ} {m : ℕ → ℝ} {D : ℕ → ℂ → ℝ}
    (hD : ∀ k, IsTestFunction (ball (0 : ℂ) (3 / 4)) (D k)) (hD0 : ∀ k x, 0 ≤ D k x)
    (hm : ∀ k J n, m (idx k J n) = ∫ x, D k x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν)
    {w' : DiscW} (hw' : ∀ y : closedBall (0 : ℂ) (3 / 4), w' y = w y) (k : ℕ) :
    certI z U idx m t w' k < ⊤ ∧
      ∫ x, extW w' x * Laplacian.laplacian (D k) x = (certI z U idx m t w' k).toReal := by
  have hDc : HasCompactSupport (D k) := (hD k).2.1
  have hDcont : Continuous (D k) := (hD k).1.continuous
  have hDsupp : tsupport (D k) ⊆ ball (0 : ℂ) (3 / 4) := (hD k).2.2
  -- the Laplacian pairing of the witness is the Laplacian pairing of the candidate
  have hint_eq : ∫ x, extW w' x * Laplacian.laplacian (D k) x =
      ∫ x, w x * Laplacian.laplacian (D k) x := by
    congr 1
    funext x
    by_cases hx : x ∈ closedBall (0 : ℂ) (3 / 4)
    · rw [extW_eq_of_closedBall hw' x hx]
    · have h0 : Laplacian.laplacian (D k) x = 0 :=
        laplacian_eq_zero_of_notMem_tsupport (fun h => hx (ball_subset_closedBall (hDsupp h)))
      rw [h0, mul_zero, mul_zero]
  -- the Laplacian clause of the certificate, with negative part `0`
  have hLap := ((hw.2.2.2.2.2).2 (D k) (hD k)).2.2
  rw [integral_zero_measure, sub_zero] at hLap
  have hLk : ∫ x, extW w' x * Laplacian.laplacian (D k) x =
      ∫ x, D k x ∂(ν.restrict (interior (closure (certCluster (3 / 4) t w)))) :=
    hint_eq.trans hLap
  -- the restricted moment is the lintegral over the charged union
  have hmom := sup_charged_moment_eq (ν := ν) hDcont hDc (hD0 k) U hopen
    (certD z U t w') (fun i hi => by
      rw [certD_iff_subset_closure_cluster hpole ht hopen hne hreg hz hzd w' i] at hi
      exact hi.trans (closure_certCluster_sdiff_zero_subset.trans (closedBall_subset_ball (by norm_num))))
  have hcI : certI z U idx m t w' k =
      ∫⁻ x in interior (closure (certCluster (3 / 4) t w)), ENNReal.ofReal (D k x) ∂ν := by
    unfold certI
    simp only [hm]
    rw [hmom, iUnion_certD_eq_interior hpole ht hopen hne hreg hz hzd w',
      interior_closure_extW_eq hpole ht hw']
  have hDint : IntegrableOn (D k) (interior (closure (certCluster (3 / 4) t w))) ν :=
    (hDcont.integrable_of_hasCompactSupport hDc).integrableOn
  have hofReal : ENNReal.ofReal (∫ x, D k x ∂(ν.restrict (interior (closure (certCluster (3 / 4) t w))))) =
      ∫⁻ x in interior (closure (certCluster (3 / 4) t w)), ENNReal.ofReal (D k x) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hDint (ae_of_all _ (hD0 k))
  have hcert : certI z U idx m t w' k = ENNReal.ofReal (∫ x, extW w' x * Laplacian.laplacian (D k) x) := by
    rw [hcI, hLk, hofReal]
  have hnn : 0 ≤ ∫ x, extW w' x * Laplacian.laplacian (D k) x := by
    rw [hLk]
    exact integral_nonneg (hD0 k)
  refine ⟨?_, ?_⟩
  · rw [hcert]
    exact ENNReal.ofReal_lt_top
  · rw [hcert, ENNReal.toReal_ofReal hnn]

end MatedCRT
