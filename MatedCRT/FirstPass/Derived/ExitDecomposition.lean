import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.StrongMarkov
import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped

/-!
# The walk at its exit time from a finite set: stopped path, post-exit path, rectangle identity

For the simple random walk `srwLaw m a` on the mated-CRT map and a finite exit datum `A`
(`FiniteExitData m A`, `a ∈ A`), write `τ = vExitTime A`, `stoppedPath A x = (n ↦ x (τ ∧ n))` for the
path stopped at its exit time, `postExit A x = (k ↦ x (τ + k))` for the path after the exit, and
`splice A v y u = (n ↦ y n for n < τ y, v for n = τ y, u (n - τ y) for n > τ y)`.  Almost surely
`splice A (x_τ) (stoppedPath A x) (postExit A x) = x`, and the strong Markov property at `τ` gives the
rectangle identity
`P(stoppedPath ∈ B, x_τ = v, postExit ∈ C) = P(stoppedPath ∈ B, x_τ = v) · P^v(C)`
for measurable `B`, `C`.  These are the hypotheses of the conditional-product mixture decomposition
used for the coupling of the walks from two nearby starting points at their exit from a ball
(Berestycki–Gwynne (2020), Proposition 6.12, Step 1).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitDecomposition

open MeasureTheory Set
open scoped ENNReal
open Lemma68Window Lemma68WalkBridge Lemma68ShellParam
open MatedCRT.FirstPass36 (FiniteExitData)

/-- The path stopped at its first exit time from `A`: `n ↦ x (min (τ_A x) n)` (the path itself if it never
exits). -/
noncomputable def stoppedPath (A : Set ℤ) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun n => x (min (vExitTime A x) (n : ℕ∞)).toNat

/-- The path after its first exit time from `A`: `k ↦ x (τ_A x + k)`. -/
noncomputable def postExit (A : Set ℤ) (x : ℕ → ℤ) : ℕ → ℤ :=
  WalkPotential.pathShift (vExitTime A x).toNat x

/-- The concatenation of a path `y` stopped at its exit time from `A`, the exit position `v`, and a path `u`
started at the exit position: `n ↦ y n` for `n < τ_A y`, `v` for `n = τ_A y`, `u (n - τ_A y)` for
`n > τ_A y`. -/
noncomputable def splice (A : Set ℤ) (v : ℤ) (y u : ℕ → ℤ) : ℕ → ℤ :=
  fun n => if n < (vExitTime A y).toNat then y n
    else if n = (vExitTime A y).toNat then v else u (n - (vExitTime A y).toNat)

lemma stoppedPath_of_le {A : Set ℤ} {x : ℕ → ℤ} {k n : ℕ} (hk : vExitTime A x = (k : ℕ∞))
    (hn : n ≤ k) : stoppedPath A x n = x n := by
  have h : min (vExitTime A x) (n : ℕ∞) = (n : ℕ∞) := by
    rw [hk]
    exact min_eq_right (by exact_mod_cast hn)
  simp only [stoppedPath, h, ENat.toNat_natCast]

lemma stoppedPath_of_top {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x = ⊤) :
    stoppedPath A x = x := by
  funext n
  have hmin : min (vExitTime A x) (n : ℕ∞) = (n : ℕ∞) := by
    rw [h]
    exact min_eq_right le_top
  simp only [stoppedPath, hmin, ENat.toNat_natCast]

lemma vExitTime_stoppedPath (A : Set ℤ) (x : ℕ → ℤ) :
    vExitTime A (stoppedPath A x) = vExitTime A x := by
  by_cases h : vExitTime A x = ⊤
  · rw [stoppedPath_of_top h]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
    have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
    obtain ⟨hxk, hj⟩ := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A x k).1 hk'
    rw [hk', MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec]
    refine ⟨?_, fun j hj' => ?_⟩
    · rw [stoppedPath_of_le hk' le_rfl]
      exact hxk
    · rw [stoppedPath_of_le hk' hj'.le]
      exact hj j hj'

/-- On `{τ_A < ∞}` the path is recovered from its stopped path, its exit position and its post-exit path. -/
lemma splice_stoppedPath_postExit {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x < ⊤) :
    splice A (vExitPosition A x) (stoppedPath A x) (postExit A x) = x := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
  have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
  have hK : (vExitTime A (stoppedPath A x)).toNat = k := by
    rw [vExitTime_stoppedPath, hk', ENat.toNat_natCast]
  have hKx : (vExitTime A x).toNat = k := by rw [hk', ENat.toNat_natCast]
  have hv : vExitPosition A x = x k := by simp only [vExitPosition, hKx]
  funext n
  by_cases hn : n < k
  · simp only [splice, hK, hn, ↓reduceIte]
    exact stoppedPath_of_le hk' hn.le
  · by_cases hn' : n = k
    · subst hn'
      simp [splice, hK, hv]
    · simp only [splice, hK, hn, hn', ↓reduceIte, postExit, WalkPotential.pathShift, hKx]
      congr 1
      omega

/-- The coordinates of a path before its (natural number) exit index lie in `A`. -/
lemma mem_of_lt_toNat {A : Set ℤ} {y : ℕ → ℤ} {j : ℕ} (h : j < (vExitTime A y).toNat) : y j ∈ A := by
  by_cases ht : vExitTime A y = ⊤
  · rw [ht, ENat.toNat_top] at h
    omega
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 ht
    have hk' : vExitTime A y = (k : ℕ∞) := hk.symm
    rw [hk', ENat.toNat_natCast] at h
    exact ((MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A y k).1 hk').2 j h

/-- If the walk exits `A` (finite time) its exit position is outside `A`. -/
lemma vExitPosition_notMem {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x < ⊤) :
    vExitPosition A x ∉ A := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
  have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
  have hKx : (vExitTime A x).toNat = k := by rw [hk', ENat.toNat_natCast]
  have := ((MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A x k).1 hk').1
  simpa only [vExitPosition, hKx] using this

/-- The exit time of a splice with exit position `v ∉ A` is the exit index of the stopped part. -/
lemma vExitTime_splice {A : Set ℤ} {v : ℤ} (hv : v ∉ A) (y u : ℕ → ℤ) :
    vExitTime A (splice A v y u) = ((vExitTime A y).toNat : ℕ∞) := by
  rw [MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec]
  refine ⟨by simp [splice, hv], fun j hj => ?_⟩
  simp only [splice, hj, ↓reduceIte]
  exact mem_of_lt_toNat hj

/-- The post-exit path of a splice with exit position `v ∉ A`: `v` followed by `u`. -/
lemma postExit_splice {A : Set ℤ} {v : ℤ} (hv : v ∉ A) (y u : ℕ → ℤ) :
    postExit A (splice A v y u) = fun n => if n = 0 then v else u n := by
  have hK : (vExitTime A (splice A v y u)).toNat = (vExitTime A y).toNat := by
    rw [vExitTime_splice hv, ENat.toNat_natCast]
  funext n
  simp only [postExit, WalkPotential.pathShift, hK, splice]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- The post-exit path of a splice does not depend on the stopped part. -/
lemma postExit_splice_eq {A : Set ℤ} {v : ℤ} (hv : v ∉ A) (y y' u : ℕ → ℤ) :
    postExit A (splice A v y u) = postExit A (splice A v y' u) := by
  rw [postExit_splice hv, postExit_splice hv]

/-- The coupling event: the post-exit paths agree. -/
def exitContinuationEvent (A : Set ℤ) : Set ((ℕ → ℤ) × (ℕ → ℤ)) :=
  {p | postExit A p.1 = postExit A p.2}

/-- Splices with the same exit position `v ∉ A` and the same post-exit path lie in the coupling event. -/
lemma splice_pair_mem_exitContinuationEvent {A : Set ℤ} {v : ℤ} (hv : v ∉ A) (y y' u : ℕ → ℤ) :
    (splice A v y u, splice A v y' u) ∈ exitContinuationEvent A :=
  postExit_splice_eq hv y y' u

lemma measurable_splice (A : Set ℤ) (v : ℤ) :
    Measurable (fun p : (ℕ → ℤ) × (ℕ → ℤ) => splice A v p.1 p.2) := by
  refine measurable_pi_iff.2 fun n => ?_
  have hK : Measurable fun p : (ℕ → ℤ) × (ℕ → ℤ) => (vExitTime A p.1).toNat :=
    ((measurable_of_countable ENat.toNat).comp (measurable_vExitTime A)).comp measurable_fst
  have h1 : MeasurableSet {p : (ℕ → ℤ) × (ℕ → ℤ) | n < (vExitTime A p.1).toNat} :=
    measurableSet_lt measurable_const hK
  have h2 : MeasurableSet {p : (ℕ → ℤ) × (ℕ → ℤ) | n = (vExitTime A p.1).toNat} :=
    measurableSet_eq_fun measurable_const hK
  have hy : Measurable fun p : (ℕ → ℤ) × (ℕ → ℤ) => p.1 n :=
    (measurable_pi_apply n).comp measurable_fst
  have hu : Measurable fun p : (ℕ → ℤ) × (ℕ → ℤ) => p.2 (n - (vExitTime A p.1).toNat) := by
    have : Measurable fun q : ℕ × (ℕ → ℤ) => q.2 (n - q.1) :=
      measurable_from_prod_countable_right fun j => measurable_pi_apply (n - j)
    exact this.comp (hK.prodMk measurable_snd)
  exact Measurable.ite h1 hy (Measurable.ite h2 measurable_const hu)

/-- Almost surely the walk from `a ∈ A` leaves `A`. -/
lemma ae_exit_lt_top {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ} (ha : a ∈ A) :
    ∀ᵐ x ∂srwLaw m a, vExitTime A x < ⊤ := by
  have hmeas : MeasurableSet {x : ℕ → ℤ | vExitTime A x < ⊤} :=
    measurable_vExitTime A (Set.to_countable (Iio (⊤ : ℕ∞))).measurableSet
  have h1 := MatedCRT.FirstPass36.srwLaw_vExitTime_lt_top_fp36 hA a ha
  exact ae_iff.2 ((prob_compl_eq_zero_iff hmeas).2 h1)

/-- Almost surely the path is recovered from its stopped path and post-exit path. -/
theorem ae_splice_stoppedPath_postExit {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ}
    (ha : a ∈ A) :
    ∀ᵐ x ∂srwLaw m a, splice A (vExitPosition A x) (stoppedPath A x) (postExit A x) = x := by
  filter_upwards [ae_exit_lt_top hA ha] with x hx using splice_stoppedPath_postExit hx

/-- The stopped path is `𝓕_τ`-measurable. -/
lemma measurable_stoppedPath_stop (A : Set ℤ) :
    Measurable[(isStoppingTime_vExitTime A).measurableSpace] (stoppedPath A) := by
  refine (@measurable_pi_iff _ _ _ (isStoppingTime_vExitTime A).measurableSpace _ _).2 fun n => ?_
  have hm := (isStoppingTime_vExitTime A).min_const n
  have h1 := measurable_coord_toNat_stop hm (H := (id : ℤ → ℤ))
  exact h1.mono (hm.measurableSpace_mono (isStoppingTime_vExitTime A) (fun w => min_le_left _ _))
    le_rfl

/-- The exit position is `𝓕_τ`-measurable. -/
lemma measurable_vExitPosition_stop (A : Set ℤ) :
    Measurable[(isStoppingTime_vExitTime A).measurableSpace] (vExitPosition A) :=
  measurable_coord_toNat_stop (isStoppingTime_vExitTime A) (H := (id : ℤ → ℤ))

lemma measurable_stoppedPath (A : Set ℤ) : Measurable (stoppedPath A) :=
  (measurable_stoppedPath_stop A).mono (isStoppingTime_vExitTime A).measurableSpace_le le_rfl

lemma measurable_postExit (A : Set ℤ) : Measurable (postExit A) :=
  measurable_postTimePath_stop (isStoppingTime_vExitTime A)

/-- **Rectangle identity at the exit time.**  For the walk from `a ∈ A`, a finite exit datum `A`, and
measurable `B`, `C`: `P(stopped ∈ B, x_τ = v, post ∈ C) = P(stopped ∈ B, x_τ = v) · P^v(C)`. -/
theorem srwLaw_exit_rectangle {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ}
    (ha : a ∈ A) (v : ℤ) {B C : Set (ℕ → ℤ)} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    srwLaw m a (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ postExit A ⁻¹' C)
      = srwLaw m a (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v}) * srwLaw m v C := by
  have hT : IsStoppingTime coordFiltration (vExitTime A) := isStoppingTime_vExitTime A
  have hBset : MeasurableSet[hT.measurableSpace]
      (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ {w | vExitTime A w < ⊤}) :=
    (((measurable_stoppedPath_stop A) hB).inter
      ((measurable_vExitPosition_stop A) (measurableSet_singleton v))).inter
      (measurableSet_lt_top_stop hT)
  have hBmeas := hT.measurableSpace_le _ hBset
  have hnull : srwLaw m a {w | vExitTime A w < ⊤}ᶜ = 0 := ae_iff.1 (ae_exit_lt_top hA ha)
  have hpost := measurable_postExit A
  have h1 : srwLaw m a (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ postExit A ⁻¹' C)
      = srwLaw m a ((stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ {w | vExitTime A w < ⊤})
          ∩ postExit A ⁻¹' C) := by
    rw [← measure_inter_conull hnull
      (s := stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ postExit A ⁻¹' C)]
    congr 1
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have h2 : srwLaw m a (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v})
      = srwLaw m a (stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ {w | vExitTime A w < ⊤}) :=
    (measure_inter_conull hnull).symm
  rw [h1, h2]
  set Bset := stoppedPath A ⁻¹' B ∩ vExitPosition A ⁻¹' {v} ∩ {w | vExitTime A w < ⊤} with hBset_def
  let H : (ℕ → ℤ) → ℝ≥0∞ := C.indicator 1
  have hH : Measurable H := measurable_const.indicator hC
  have e1 : srwLaw m a (Bset ∩ postExit A ⁻¹' C)
      = ∫⁻ w in Bset, {w | vExitTime A w < ⊤}.indicator
          (fun w => H (postTimePath (fun n w => w n) (vExitTime A) w)) w ∂srwLaw m a := by
    rw [Set.inter_comm, ← Measure.restrict_apply (hpost hC), ← lintegral_indicator_one (hpost hC)]
    refine setLIntegral_congr_fun hBmeas (fun w hw => ?_)
    have hwlt : vExitTime A w < ⊤ := hw.2
    have hpe : postTimePath (fun n w => w n) (vExitTime A) w = postExit A w := rfl
    simp only [H, Set.indicator_of_mem (show w ∈ {w | vExitTime A w < ⊤} from hwlt), hpe]
    rfl
  have e2 := lintegral_postTime m a hT hH hBset
  have e3 : ∫⁻ w in Bset, {w | vExitTime A w < ⊤}.indicator
        (fun w => ∫⁻ x, H x ∂srwLaw m (w (vExitTime A w).toNat)) w ∂srwLaw m a
      = ∫⁻ _ in Bset, srwLaw m v C ∂srwLaw m a := by
    refine setLIntegral_congr_fun hBmeas (fun w hw => ?_)
    have hwlt : vExitTime A w < ⊤ := hw.2
    have hwv : w (vExitTime A w).toNat = v := hw.1.2
    simp only [Set.indicator_of_mem (show w ∈ {w | vExitTime A w < ⊤} from hwlt), hwv]
    exact lintegral_indicator_one hC
  rw [e1, e2, e3, setLIntegral_const, mul_comm]

/-- The coupling event of the post-exit paths is measurable. -/
lemma measurableSet_exitContinuationEvent (A : Set ℤ) : MeasurableSet (exitContinuationEvent A) := by
  have : exitContinuationEvent A = ⋂ n : ℕ, {p | postExit A p.1 n = postExit A p.2 n} := by
    ext p
    simp only [exitContinuationEvent, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h n => by rw [h], fun h => funext h⟩
  rw [this]
  exact MeasurableSet.iInter fun n => measurableSet_eq_fun
    (((measurable_pi_apply n).comp (measurable_postExit A)).comp measurable_fst)
    (((measurable_pi_apply n).comp (measurable_postExit A)).comp measurable_snd)

/-- For `v ∈ A` the walk from `a ∈ A` almost surely does not exit `A` at `v`. -/
lemma srwLaw_exitPosition_null {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ}
    (ha : a ∈ A) {v : ℤ} (hv : v ∈ A) : srwLaw m a (vExitPosition A ⁻¹' {v}) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_exit_lt_top hA ha] with x hx
  intro hxv
  exact vExitPosition_notMem hx (by rw [show vExitPosition A x = v from hxv]; exact hv)

end ExitDecomposition
end MatedCRT
