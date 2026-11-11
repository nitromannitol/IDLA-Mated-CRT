import MatedCRT.FirstPass.S6r.OneTest.ParamStrongMarkov

/-!
# The one-test estimate at `T` with the parametric test (parametric `conditional_one_test`)

Parametric version of `conditional_one_test` (Count.lean): the test ball `D₀ = B_{c₀R}(x)` and its exit time `σ_D`
depend on the `𝓕_T`-measurable parameter `ρ` (radius and centre chosen at the shell hit). The test
end is `L = T + σ_ρ(post-T path)`, the count is `V = 1_{T<∞} ∑_{n < σ_ρ} 1{X_{T+n} ∉ A}`.

The conditional moments of `V` are the fixed-start moments at `X_T` by `StrongMarkovAtParam`
(`strongMarkovAt_occCount_param`, `_sq_param`). The bound is `oneTest_hone_shell` (generic in the count).
Named inputs: `hLst` (the test end is a stopping time), `hint1`, `hint2` (integrability), `hρ`, `hσ`, and the moment
bounds `hstep1`, `hstep2` (Steps 2-4, Lemmas 2.7, 2.9, 2.16, 2.18) that are not formalized here.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

variable {P : Type*} [MeasurableSpace P]

open Lemma68WalkBridge

/-- The parametric test end `L = T + σ_ρ(post-T path)` (ℕ∞-valued). -/
noncomputable def testEndParam (σ : P → (ℕ → ℤ) → ℕ) (ρ : (ℕ → ℤ) → P) (T : (ℕ → ℤ) → ℕ∞) (w : ℕ → ℤ) : ℕ∞ :=
  T w + ((σ (ρ w) (postTimePath (fun n w => w n) T w) : ℕ) : ℕ∞)

/-- The parametric one-test variable `V = 1_{T<∞} ∑_{n < σ_ρ} 1{X_{T+n} ∉ A}`. -/
noncomputable def testCountParam (A : Set ℤ) (σ : P → (ℕ → ℤ) → ℕ) (ρ : (ℕ → ℤ) → P) (T : (ℕ → ℤ) → ℕ∞)
    (w : ℕ → ℤ) : ℝ :=
  {w' | T w' < ⊤}.indicator (fun w' => occCount A (σ (ρ w')) (postTimePath (fun n w => w n) T w')) w

omit [MeasurableSpace P] in
/-- On the parametric test-success event, the parametric count vanishes (pointwise version of
`testCount_eq_zero_of_testFail`). -/
theorem testCountParam_eq_zero {A : Set ℤ} {σ : P → (ℕ → ℤ) → ℕ} {ρ : (ℕ → ℤ) → P} {T : (ℕ → ℤ) → ℕ∞}
    {w : ℕ → ℤ}
    (hw : w ∈ testFailSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T (testEndParam σ ρ T)) :
    testCountParam A σ ρ T w = 0 := by
  by_cases hT : T w < ⊤
  · obtain ⟨t, htT⟩ : ∃ t : ℕ, T w = t := ⟨(T w).toNat, (ENat.natCast_toNat hT.ne).symm⟩
    have ht : (T w).toNat = t := by rw [htT]; rfl
    unfold testCountParam occCount
    rw [Set.indicator_of_mem (show w ∈ {w' | T w' < ⊤} from hT)]
    apply Finset.sum_eq_zero
    intro n hn
    have hnσ : n < σ (ρ w) (postTimePath (fun n w => w n) T w) := Finset.mem_range.1 hn
    have hmem : w (t + n) ∈ A := by
      refine hw (t + n) ?_ ?_
      · rw [htT]; exact_mod_cast Nat.le_add_right t n
      · unfold testEndParam; rw [htT]; exact_mod_cast Nat.add_lt_add_left hnσ t
    simp only [postTimePath, ht]
    exact Set.indicator_of_notMem (by simpa using hmem) _
  · unfold testCountParam
    exact Set.indicator_of_notMem (show w ∉ {w' | T w' < ⊤} from hT) _

omit [MeasurableSpace P] in
/-- The test end `T + σ_ρ(post-T path)` covers the count window: `T + n < L` for `n < σ_ρ`, on `{T < ∞}`. -/
theorem testEndParam_cover {σ : P → (ℕ → ℤ) → ℕ} {ρ : (ℕ → ℤ) → P} {T : (ℕ → ℤ) → ℕ∞} {w : ℕ → ℤ}
    (hw : T w < ⊤) (n : ℕ) (hn : n < σ (ρ w) (postTimePath (fun n w => w n) T w)) :
    T w + (n : ℕ∞) < testEndParam σ ρ T w := by
  unfold testEndParam
  obtain ⟨t, htT⟩ : ∃ t : ℕ, T w = t := ⟨(T w).toNat, (ENat.natCast_toNat hw.ne).symm⟩
  rw [htT]
  exact_mod_cast Nat.add_lt_add_left hn t

omit [MeasurableSpace P] in
/-- Pointwise vanishing of the count on the test-failure event, for an abstract test end `L` that covers the
count window (`hcov`); the parametric test end `testEndParam` is the case `L = T + σ_ρ`. -/
theorem testCountParam_eq_zero_of_cover {A : Set ℤ} {σ : P → (ℕ → ℤ) → ℕ} {ρ : (ℕ → ℤ) → P}
    {T L : (ℕ → ℤ) → ℕ∞}
    (hcov : ∀ w, T w < ⊤ → ∀ n : ℕ, n < σ (ρ w) (postTimePath (fun n w => w n) T w) → T w + (n : ℕ∞) < L w)
    {w : ℕ → ℤ} (hw : w ∈ testFailSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T L) :
    testCountParam A σ ρ T w = 0 := by
  by_cases hT : T w < ⊤
  · unfold testCountParam occCount
    rw [Set.indicator_of_mem (show w ∈ {w' | T w' < ⊤} from hT)]
    apply Finset.sum_eq_zero
    intro n hn
    have hnσ : n < σ (ρ w) (postTimePath (fun n w => w n) T w) := Finset.mem_range.1 hn
    have hcov' := hcov w hT n hnσ
    have hmem : w ((T w).toNat + n) ∈ A := by
      refine hw ((T w).toNat + n) ?_ ?_
      · push_cast
        rw [ENat.natCast_toNat hT.ne]
        exact le_self_add
      · push_cast
        rw [ENat.natCast_toNat hT.ne]
        exact hcov'
    simp only [postTimePath]
    exact Set.indicator_of_notMem (by simpa using hmem) _
  · unfold testCountParam
    exact Set.indicator_of_notMem (show w ∉ {w' | T w' < ⊤} from hT) _

/-- **The one-test estimate at `T` for an abstract test end `L` covering the count window** (the general form of
`conditional_one_test_param`, used with `L` the exit-time test end of `ExitQAe`-type instances). -/
theorem conditional_one_test_gen (m : ℤ → ℤ → ℕ) (a : ℤ) {A : Set ℤ} (hA : MeasurableSet A)
    {σ : P → (ℕ → ℤ) → ℕ} (hσ : Measurable (fun q : P × (ℕ → ℤ) => σ q.1 q.2))
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ) {τU : (ℕ → ℤ) → ℕ∞} {mm R : (ℕ → ℤ) → ℝ}
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C))
    {L : (ℕ → ℤ) → ℕ∞} (hLst : IsStoppingTime coordFiltration L)
    (hcov : ∀ w, T w < ⊤ → ∀ n : ℕ, n < σ (ρ w) (postTimePath (fun n w => w n) T w) → T w + (n : ℕ∞) < L w)
    (hint1 : Integrable (testCountParam A σ ρ T) (srwLaw m a))
    (hint2 : Integrable ({w | T w < ⊤}.indicator
      (fun w => occCount A (σ (ρ w)) (postTimePath (fun n w => w n) T w) ^ 2)) (srwLaw m a))
    (hm : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU, 0 < mm ω)
    (hRr : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU, r ^ 2 ≤ R ω ∧ R ω ≤ 1)
    (hstep1 : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU,
      c * ε⁻¹ * mm ω ≤ ∫ w, occCount A (σ (ρ ω)) w ∂(srwLaw m (ω (T ω).toNat)))
    (hstep2 : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU,
      ∫ w, occCount A (σ (ρ ω)) w ^ 2 ∂(srwLaw m (ω (T ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * mm ω ^ 2) :
    ∀ᵐ ω ∂srwLaw m a, ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU →
      (srwLaw m a)[(testFailSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T L).indicator
        (fun _ => (1 : ℝ)) | hT.measurableSpace] ω
        ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by
  have hSM1 := strongMarkovAt_occCount_param m a A hσ hT hρ hint1
  have hSM2 := strongMarkovAt_occCount_sq_param m a A hσ hT hρ hint2
  unfold StrongMarkovAtParam at hSM1 hSM2
  have hV2 : Integrable (fun ω => testCountParam A σ ρ T ω ^ 2) (srwLaw m a) := by
    have e : (fun ω => testCountParam A σ ρ T ω ^ 2)
        = fun ω => {w | T w < ⊤}.indicator
            (fun w => occCount A (σ (ρ w)) (postTimePath (fun n w => w n) T w) ^ 2) ω := by
      funext ω
      by_cases h : T ω < ⊤
      · simp [testCountParam, Set.indicator, h]
      · simp [testCountParam, Set.indicator, h]
    rw [e]
    exact hint2
  have hfirst : ∀ᵐ ω ∂srwLaw m a, ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU →
      c * ε⁻¹ * mm ω ≤ (srwLaw m a)[testCountParam A σ ρ T | hT.measurableSpace] ω := by
    filter_upwards [hSM1] with ω hω hωP
    have hTlt : T ω < ⊤ := lt_of_lt_of_le hωP.1 le_top
    have hcond : (srwLaw m a)[testCountParam A σ ρ T | hT.measurableSpace] ω
        = ∫ w, occCount A (σ (ρ ω)) w ∂(srwLaw m (ω (T ω).toNat)) := by
      have e : testCountParam A σ ρ T
          = {ω' | T ω' < ⊤}.indicator
              (fun ω' => occCount A (σ (ρ ω')) (postTimePath (fun n w => w n) T ω')) := rfl
      rw [e]
      rw [hω]
      exact Set.indicator_of_mem (show ω ∈ {ω' | T ω' < ⊤} from hTlt) _
    rw [hcond]
    exact hstep1 ω hωP
  have hsecond : ∀ᵐ ω ∂srwLaw m a, ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU →
      (srwLaw m a)[fun ω => testCountParam A σ ρ T ω ^ 2 | hT.measurableSpace] ω
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * mm ω ^ 2 := by
    filter_upwards [hSM2] with ω hω hωP
    have hTlt : T ω < ⊤ := lt_of_lt_of_le hωP.1 le_top
    have hcond : (srwLaw m a)[fun ω => testCountParam A σ ρ T ω ^ 2 | hT.measurableSpace] ω
        = ∫ w, occCount A (σ (ρ ω)) w ^ 2 ∂(srwLaw m (ω (T ω).toNat)) := by
      have e : (fun ω => testCountParam A σ ρ T ω ^ 2)
          = fun ω => {ω' | T ω' < ⊤}.indicator
              (fun ω' => occCount A (σ (ρ ω')) (postTimePath (fun n w => w n) T ω') ^ 2) ω := by
        funext ω
        by_cases h : T ω < ⊤
        · simp [testCountParam, Set.indicator, h]
        · simp [testCountParam, Set.indicator, h]
      rw [e]
      rw [hω]
      exact Set.indicator_of_mem (show ω ∈ {ω' | T ω' < ⊤} from hTlt) _
    rw [hcond]
    exact hstep2 ω hωP
  have hFm : MeasurableSet (testFailSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T L) :=
    measurableSet_testFailSet coordFiltration (fun n => coord_measurable n) hA hT hLst
  exact oneTest_hone_shell (𝓖 := hT.measurableSpace) hT.measurableSpace_le hFm
    (fun _ hω => testCountParam_eq_zero_of_cover hcov hω) hint1 hV2 hc hC hε hr hr1 hq0c hm hRr hfirst hsecond

/-- **The one-test estimate at `T` with a parametric test** (parametric `conditional_one_test`): the test end is
`L = T + σ_ρ(post-T path)`, ℕ∞-valued. Corollary of `conditional_one_test_gen`. -/
theorem conditional_one_test_param (m : ℤ → ℤ → ℕ) (a : ℤ) {A : Set ℤ} (hA : MeasurableSet A)
    {σ : P → (ℕ → ℤ) → ℕ} (hσ : Measurable (fun q : P × (ℕ → ℤ) => σ q.1 q.2))
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ) {τU : (ℕ → ℤ) → ℕ∞} {mm R : (ℕ → ℤ) → ℝ}
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C))
    (hLst : IsStoppingTime coordFiltration (testEndParam σ ρ T))
    (hint1 : Integrable (testCountParam A σ ρ T) (srwLaw m a))
    (hint2 : Integrable ({w | T w < ⊤}.indicator
      (fun w => occCount A (σ (ρ w)) (postTimePath (fun n w => w n) T w) ^ 2)) (srwLaw m a))
    (hm : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU, 0 < mm ω)
    (hRr : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU, r ^ 2 ≤ R ω ∧ R ω ≤ 1)
    (hstep1 : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU,
      c * ε⁻¹ * mm ω ≤ ∫ w, occCount A (σ (ρ ω)) w ∂(srwLaw m (ω (T ω).toNat)))
    (hstep2 : ∀ ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU,
      ∫ w, occCount A (σ (ρ ω)) w ^ 2 ∂(srwLaw m (ω (T ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * mm ω ^ 2) :
    ∀ᵐ ω ∂srwLaw m a, ω ∈ prefixSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T τU →
      (srwLaw m a)[(testFailSet (fun (n : ℕ) (w : ℕ → ℤ) => w n) A T (testEndParam σ ρ T)).indicator
        (fun _ => (1 : ℝ)) | hT.measurableSpace] ω
        ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 :=
  conditional_one_test_gen m a hA hσ hT hρ hc hC hε hr hr1 hq0c hLst
    (fun _ hw _ hn => testEndParam_cover hw _ hn) hint1 hint2 hm hRr hstep1 hstep2

end Lemma68Window
end MatedCRT
