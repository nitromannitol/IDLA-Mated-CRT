import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.StrongMarkov
import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped

/-!
# The walk at its exit time from a finite set: stopped path, post-exit path, rectangle identity

For the simple random walk `srwLaw m a` on the mated-CRT map and a finite exit datum `A`
(`FiniteExitData m A`, `a ∈ A`), write `τ = vExitTime A`, `stoppedPath A x = (n ↦ x (τ ∧ n))` for the
path stopped at its exit time, `postExit A x = (k ↦ x (τ + k))` for the path after the exit, and
`splice A y u = (n ↦ y n for n ≤ τ y, u (n - τ y) for n > τ y)`.  Almost surely
`splice A (stoppedPath A x) (postExit A x) = x`, and the strong Markov property at `τ` gives the
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

/-- The concatenation of a path `y` stopped at its exit time from `A` with a path `u` started at the exit
position: `n ↦ y n` for `n ≤ τ_A y` and `n ↦ u (n - τ_A y)` for `n > τ_A y`. -/
noncomputable def splice (A : Set ℤ) (y u : ℕ → ℤ) : ℕ → ℤ :=
  fun n => if n ≤ (vExitTime A y).toNat then y n else u (n - (vExitTime A y).toNat)

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

/-- On `{τ_A < ∞}` the path is recovered from its stopped path and its post-exit path. -/
lemma splice_stoppedPath_postExit {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x < ⊤) :
    splice A (stoppedPath A x) (postExit A x) = x := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
  have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
  have hK : (vExitTime A (stoppedPath A x)).toNat = k := by
    rw [vExitTime_stoppedPath, hk', ENat.toNat_natCast]
  have hKx : (vExitTime A x).toNat = k := by rw [hk', ENat.toNat_natCast]
  funext n
  by_cases hn : n ≤ k
  · simp only [splice, hK, hn, ↓reduceIte]
    exact stoppedPath_of_le hk' hn
  · simp only [splice, hK, hn, ↓reduceIte, postExit, WalkPotential.pathShift, hKx]
    congr 1
    omega

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
    ∀ᵐ x ∂srwLaw m a, splice A (stoppedPath A x) (postExit A x) = x := by
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

end ExitDecomposition
end MatedCRT
