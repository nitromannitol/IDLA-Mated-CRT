import MatedCRT.FirstPass.S6r.Amplification
import MatedCRT.FirstPass.S6r.OneTest

/-!
# The one-test estimate at the stopping times `T_j` (PRO notes step 8 `one_test_from_boundary`,
step 14 `conditional_one_test`; chat (7.50))

The one-test variable is the occupation count of the sites outside `A` visited before the exit time `σ` of the
discrete interior of the test ball (PRO step 8: `V_occ = ∑_{n < σ_D} 1{X_n ∉ A}`). It is started at the stopping
time `T_j`. Its conditional moments given `𝓕_{T_j}` are the fixed-start moments at `X_{T_j}`, by the strong Markov
property at `T_j` (PRO step 14). The test-success event `{V = 0}` contains the no-escape event of the test window
`[T_j, L_j)`, `L_j = T_j + σ`, so the test-failure set of `prefix_bad_bound` is the event `{V = 0}`.

Named inputs (hypotheses of the statements that use them, not proved here):
* `StrongMarkovAt`: the strong Markov property at `T` for the post-`T` functionals (PRO step 14); the path laws
  `Pb ω b` are the walk law started at `b` in the environment `ω` (conditioning on `(h, η)`);
* `hstep1`, `hstep2`: the fixed-start one-test moment bounds (PRO step 8, printed Steps 2-4 with the corrected
  good event) at the starts `X_{T_j}` on the prefix event `P_j`, with the scales `m = μ_h(B_{c₀R}(x))`, `r² ≤ R ≤ 1`;
* `hLst`: the test end `L_j = T_j + σ` is a stopping time; `hV1`, `hV2`: integrability of the count and its square;
* `σ` is an abstract path functional: the exit time of the discrete interior `I(D)` (its definition is not
  formalized here).

Terminology: second-moment method (Paley-Zygmund) and good annuli (Armstrong-Kuusi-Mourrat); strong Markov
property at a stopping time (Duplantier-Sheffield, Berestycki-Powell for the LQG-walk setting).
-/

open MeasureTheory

namespace MatedCRT
namespace Lemma68Window

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]

/-- The post-`T` path `n ↦ X_{T + n}` (the strong Markov shift); meaningful on `{T < ∞}`. -/
def postTimePath (X : ℕ → Ω → E) (T : Ω → ℕ∞) (ω : Ω) : ℕ → E :=
  fun n => X ((T ω).toNat + n) ω

/-- Occupation count of the test (PRO step 8): `V_occ(w) = ∑_{n < σ(w)} 1{w_n ∉ A}`. -/
noncomputable def occCount (A : Set E) (σ : (ℕ → E) → ℕ) (w : ℕ → E) : ℝ :=
  ∑ n ∈ Finset.range (σ w), Aᶜ.indicator (fun _ => (1 : ℝ)) (w n)

/-- The one-test variable started at the stopping time `T` (zero on `{T = ∞}`). -/
noncomputable def testCount (A : Set E) (σ : (ℕ → E) → ℕ) (X : ℕ → Ω → E) (T : Ω → ℕ∞)
    (ω : Ω) : ℝ :=
  {ω' | T ω' < ⊤}.indicator (fun ω' => occCount A σ (postTimePath X T ω')) ω

/-- The test end `L = T + σ(post-T path)`: the exit of the discrete interior at time `T + σ`. -/
noncomputable def testEnd (σ : (ℕ → E) → ℕ) (X : ℕ → Ω → E) (T : Ω → ℕ∞) (ω : Ω) : ℕ∞ :=
  T ω + ((σ (postTimePath X T ω) : ℕ) : ℕ∞)

/-- Named input: the strong Markov property at `T` for the post-`T` functional `G` (PRO step 14).
On `{T < ∞}`, `E[G(post-T path) | 𝓕_T] = ∫ G dP_{X_T}`, with `P_b = Pb ω b` the walk law from `b`. -/
def StrongMarkovAt (μ : Measure Ω) {𝓕 : Filtration ℕ mΩ} {T : Ω → ℕ∞} (hT : IsStoppingTime 𝓕 T)
    (X : ℕ → Ω → E) (Pb : Ω → E → Measure (ℕ → E)) (G : (ℕ → E) → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, μ[{ω' | T ω' < ⊤}.indicator (fun ω' => G (postTimePath X T ω')) | hT.measurableSpace] ω
    = {ω' | T ω' < ⊤}.indicator (fun ω' => ∫ w, G w ∂(Pb ω' (X (T ω').toNat ω'))) ω

omit mΩ [MeasurableSpace E] in
/-- On the test-success event `F = testFailSet X A T L` (no escape from `A` during `[T, L)`), the count
vanishes: every term of the sum `∑_{n < σ}` is `1_{A}` evaluated at a time of the test window. -/
theorem testCount_eq_zero_of_testFail {A : Set E} {σ : (ℕ → E) → ℕ} {X : ℕ → Ω → E} {T : Ω → ℕ∞}
    {ω : Ω} (hω : ω ∈ testFailSet X A T (testEnd σ X T)) : testCount A σ X T ω = 0 := by
  by_cases hT : T ω < ⊤
  · obtain ⟨t, htT⟩ : ∃ t : ℕ, T ω = t := ⟨(T ω).toNat, (ENat.natCast_toNat hT.ne).symm⟩
    have ht : (T ω).toNat = t := by rw [htT]; rfl
    have hω' : ∀ m : ℕ, T ω ≤ (m : ℕ∞) → (m : ℕ∞) < testEnd σ X T ω → X m ω ∈ A := hω
    unfold testCount occCount
    rw [Set.indicator_of_mem (show ω ∈ {ω' | T ω' < ⊤} from hT)]
    apply Finset.sum_eq_zero
    intro n hn
    have hnσ : n < σ (postTimePath X T ω) := Finset.mem_range.1 hn
    have hmem : X (t + n) ω ∈ A := by
      refine hω' (t + n) ?_ ?_
      · rw [htT]; exact_mod_cast Nat.le_add_right t n
      · unfold testEnd; rw [htT]; exact_mod_cast Nat.add_lt_add_left hnσ t
    simp only [postTimePath, ht]
    exact Set.indicator_of_notMem (by simpa using hmem) _
  · unfold testCount
    exact Set.indicator_of_notMem (show ω ∉ {ω' | T ω' < ⊤} from hT) _

omit mΩ [MeasurableSpace E] in
/-- The square of the count is the count of the square (indicator commutes with squaring). -/
theorem testCount_sq_eq (A : Set E) (σ : (ℕ → E) → ℕ) (X : ℕ → Ω → E) (T : Ω → ℕ∞) :
    (fun ω => testCount A σ X T ω ^ 2)
      = {ω' | T ω' < ⊤}.indicator (fun ω' => occCount A σ (postTimePath X T ω') ^ 2) := by
  funext ω
  unfold testCount
  simp only [Set.indicator_apply]
  split_ifs <;> simp

/-- The one-test estimate (PRO step 14, chat (7.50)) at the stopping time `T` for the prefix event `P`: the
conditional probability given `𝓕_T` of the test failure `F` is at most `1 - q0/(1 + log(1/r))²` a.s. on `P`.
This is `hone` of `prefix_bad_bound`, with the strong Markov transport `hSM1`, `hSM2` and the fixed-start
moments `hstep1`, `hstep2` at the starts `X_T` (the one-test lemma is applied only at `T`). -/
theorem conditional_one_test {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E}
    (hA : MeasurableSet A) {σ : (ℕ → E) → ℕ} (Pb : Ω → E → Measure (ℕ → E))
    {T : Ω → ℕ∞} (hT : IsStoppingTime 𝓕 T) {τU : Ω → ℕ∞} {m R : Ω → ℝ}
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C))
    (hLst : IsStoppingTime 𝓕 (testEnd σ X T))
    (hV1 : Integrable (testCount A σ X T) μ)
    (hV2 : Integrable (fun ω => testCount A σ X T ω ^ 2) μ)
    (hSM1 : StrongMarkovAt μ hT X Pb (occCount A σ))
    (hSM2 : StrongMarkovAt μ hT X Pb (fun w => occCount A σ w ^ 2))
    (hm : ∀ ω ∈ prefixSet X A T τU, 0 < m ω)
    (hRr : ∀ ω ∈ prefixSet X A T τU, r ^ 2 ≤ R ω ∧ R ω ≤ 1)
    (hstep1 : ∀ ω ∈ prefixSet X A T τU,
      c * ε⁻¹ * m ω ≤ ∫ w, occCount A σ w ∂(Pb ω (X (T ω).toNat ω)))
    (hstep2 : ∀ ω ∈ prefixSet X A T τU,
      ∫ w, occCount A σ w ^ 2 ∂(Pb ω (X (T ω).toNat ω))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2) :
    ∀ᵐ ω ∂μ, ω ∈ prefixSet X A T τU →
      μ[(testFailSet X A T (testEnd σ X T)).indicator (fun _ => (1 : ℝ)) | hT.measurableSpace] ω
        ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by
  have hfirst : ∀ᵐ ω ∂μ, ω ∈ prefixSet X A T τU →
      c * ε⁻¹ * m ω ≤ μ[testCount A σ X T | hT.measurableSpace] ω := by
    filter_upwards [hSM1] with ω hω hωP
    have hTlt : T ω < ⊤ := lt_of_lt_of_le hωP.1 le_top
    have hcond : μ[testCount A σ X T | hT.measurableSpace] ω
        = ∫ w, occCount A σ w ∂(Pb ω (X (T ω).toNat ω)) := by
      have e : testCount A σ X T
          = {ω' | T ω' < ⊤}.indicator (fun ω' => occCount A σ (postTimePath X T ω')) := rfl
      rw [e, hω]
      exact Set.indicator_of_mem (show ω ∈ {ω' | T ω' < ⊤} from hTlt) _
    rw [hcond]
    exact hstep1 ω hωP
  have hsecond : ∀ᵐ ω ∂μ, ω ∈ prefixSet X A T τU →
      μ[fun ω => testCount A σ X T ω ^ 2 | hT.measurableSpace] ω
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R ω)) ^ 2 * m ω ^ 2 := by
    filter_upwards [hSM2] with ω hω hωP
    have hTlt : T ω < ⊤ := lt_of_lt_of_le hωP.1 le_top
    have hω' : μ[{ω' | T ω' < ⊤}.indicator (fun ω' => occCount A σ (postTimePath X T ω') ^ 2)
          | hT.measurableSpace] ω
        = {ω' | T ω' < ⊤}.indicator (fun ω' => ∫ w, occCount A σ w ^ 2 ∂(Pb ω' (X (T ω').toNat ω'))) ω :=
      hω
    have hcond : μ[fun ω => testCount A σ X T ω ^ 2 | hT.measurableSpace] ω
        = ∫ w, occCount A σ w ^ 2 ∂(Pb ω (X (T ω).toNat ω)) := by
      rw [testCount_sq_eq, hω']
      exact Set.indicator_of_mem (show ω ∈ {ω' | T ω' < ⊤} from hTlt) _
    rw [hcond]
    exact hstep2 ω hωP
  exact oneTest_hone_shell (𝓖 := hT.measurableSpace) hT.measurableSpace_le
    (measurableSet_testFailSet 𝓕 hX hA hT hLst) (fun _ hω => testCount_eq_zero_of_testFail hω)
    hV1 hV2 hc hC hε hr hr1 hq0c hm hRr hfirst hsecond

/-- The shell bad-event bound (PRO step 14 at every `T_j`, then `prefix_bad_bound`):
`μ(B) ≤ (1 - q0/(1 + log(1/r))²)^(n+1)`, the input of `shell_product_le_half`. -/
theorem shell_bad_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E}
    (hA : MeasurableSet A) {σ : (ℕ → E) → ℕ} (Pb : Ω → E → Measure (ℕ → E))
    {T : ℕ → Ω → ℕ∞} (hT : ∀ k, IsStoppingTime 𝓕 (T k))
    {τU : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τU) {m R : ℕ → Ω → ℝ}
    {c C ε r q0 : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (hq0c : q0 ≤ c ^ 2 / (4 * C))
    (hLst : ∀ k, IsStoppingTime 𝓕 (testEnd σ X (T k)))
    (hV1 : ∀ k, Integrable (testCount A σ X (T k)) μ)
    (hV2 : ∀ k, Integrable (fun ω => testCount A σ X (T k) ω ^ 2) μ)
    (hSM1 : ∀ k, StrongMarkovAt μ (hT k) X Pb (occCount A σ))
    (hSM2 : ∀ k, StrongMarkovAt μ (hT k) X Pb (fun w => occCount A σ w ^ 2))
    (hm : ∀ k, ∀ ω ∈ prefixSet X A (T k) τU, 0 < m k ω)
    (hRr : ∀ k, ∀ ω ∈ prefixSet X A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hstep1 : ∀ k, ∀ ω ∈ prefixSet X A (T k) τU,
      c * ε⁻¹ * m k ω ≤ ∫ w, occCount A σ w ∂(Pb ω (X (T k ω).toNat ω)))
    (hstep2 : ∀ k, ∀ ω ∈ prefixSet X A (T k) τU,
      ∫ w, occCount A σ w ^ 2 ∂(Pb ω (X (T k ω).toNat ω))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2 * m k ω ^ 2)
    (n : ℕ) (hTT : ∀ j < n, ∀ ω, T j ω ≤ T (j + 1) ω)
    (hLT : ∀ j < n, ∀ ω, testEnd σ X (T j) ω ≤ T (j + 1) ω)
    (hcross : ∀ ω ∈ noEscapeSet X A τU, T n ω < τU ω)
    (hend : ∀ ω ∈ noEscapeSet X A τU, testEnd σ X (T n) ω ≤ τU ω) :
    μ.real (noEscapeSet X A τU) ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ (n + 1) :=
  prefix_bad_bound 𝓕 hX hA hT hLst hτ (oneTest_q_bounds hq0 hq01 hr hr1).2 n
    (fun k _ => conditional_one_test 𝓕 hX hA Pb (hT k) hc hC hε hr hr1 hq0c (hLst k)
      (hV1 k) (hV2 k) (hSM1 k) (hSM2 k) (hm k) (hRr k) (hstep1 k) (hstep2 k))
    hTT hLT hcross hend

end Lemma68Window
end MatedCRT
