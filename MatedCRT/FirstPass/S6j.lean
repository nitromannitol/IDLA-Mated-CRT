import MatedCRT.FirstPass.S4S6c.TestBound68
import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.FirstPass.S4S6c.StrongMarkovState

/-!
# FirstPass S6j: the conditional step of LEMMA68 for simple random walk

Source: write-up lines 836-860 (C15): at an almost surely finite stopping time `T`
of the walk, the conditional law of the future given `F_T` is the walk started at `X_T` (discrete strong Markov property,
Norris, *Markov Chains*, Theorem 1.4.2); the tower property then gives the conditional test probability given `F_T`.

The walk is `srwLaw m a` (S4S6c/StrongMarkovState.lean uses `srwLaw` and `pathHist`/`pathShift` of WalkPotential).
This file turns the integrated form of the strong Markov property `srwLaw_strong_markov_state` into the
conditional-expectation form that `C17_le_pow` (S6e/C17Induction.lean) consumes:

* `stoppedSigma τ hτ` is the σ-algebra `F_τ` of a walk random time `τ` (`IsWalkRandomTime`);
* `srwLaw_condExp_strong_markov`: `E[1_B | F_τ] = φ(X_τ)` a.s., where `B = {∃ k, τ = k ∧ shift_k ∈ G(X_k)}` and
  `φ(y) = P^y(G y)` (`atRandomTime`), with the value `0` on `{τ = ∞}`.
-/

open MeasureTheory Set Filter
open scoped ENNReal
open Function


namespace MatedCRT

open WalkPotential

namespace S6j

/-- The history σ-algebra `F_n = σ(x_0, …, x_n)` of the path space `ℕ → ℤ`. -/
@[instance_reducible]
def histSigma (n : ℕ) : MeasurableSpace (ℕ → ℤ) :=
  MeasurableSpace.comap (pathHist n) inferInstance

lemma histSigma_le (n : ℕ) : histSigma n ≤ (inferInstance : MeasurableSpace (ℕ → ℤ)) :=
  (measurable_pathHist n).comap_le

/-- A random time of the walk, with the stopping property `{τ = k} ∈ F_k` for every `k : ℕ`. -/
def IsWalkRandomTime (τ : (ℕ → ℤ) → ℕ∞) : Prop :=
  ∀ k : ℕ, MeasurableSet[histSigma k] {x | τ x = (k : ℕ∞)}

/-- The σ-algebra `F_τ` of a walk random time: the measurable events `S` with `S ∩ {τ = k} ∈ F_k` for every `k`. -/
@[instance_reducible]
def stoppedSigma (τ : (ℕ → ℤ) → ℕ∞) (hτ : IsWalkRandomTime τ) : MeasurableSpace (ℕ → ℤ) where
  MeasurableSet' S := MeasurableSet S ∧ ∀ k : ℕ, MeasurableSet[histSigma k] (S ∩ {x | τ x = (k : ℕ∞)})
  measurableSet_empty := ⟨MeasurableSet.empty, fun k => by
    rw [Set.empty_inter]; exact @MeasurableSet.empty _ (histSigma k)⟩
  measurableSet_compl := by
    rintro S ⟨hS, hSk⟩
    refine ⟨hS.compl, fun k => ?_⟩
    have hc : Sᶜ ∩ {x | τ x = (k : ℕ∞)} = {x | τ x = (k : ℕ∞)} \ (S ∩ {x | τ x = (k : ℕ∞)}) := by
      ext x; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]; tauto
    rw [hc]; exact (hτ k).diff (hSk k)
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, fun k => ?_⟩
    rw [Set.iUnion_inter]; exact MeasurableSet.iUnion fun i => (hf i).2 k

lemma stoppedSigma_le (τ : (ℕ → ℤ) → ℕ∞) (hτ : IsWalkRandomTime τ) :
    stoppedSigma τ hτ ≤ (inferInstance : MeasurableSpace (ℕ → ℤ)) :=
  fun _ hS => hS.1

/-- The test probability `φ(y) = P^y(G y)` of a state-dependent future event `G y`. -/
noncomputable def stateProb (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (y : ℤ) : ℝ :=
  (srwLaw m y (G y)).toReal

/-- The value `φ(X_τ)` at the random time `τ`, and `0` on `{τ = ∞}`. -/
noncomputable def atRandomTime (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞) (x : ℕ → ℤ) : ℝ :=
  if τ x = ⊤ then 0 else stateProb m G (x (τ x).toNat)

/-- The state-dependent future event after `τ`: the walk shifted at `τ` lies in `G (X_τ)` (the event `B` of
`srwLaw_strong_markov_state`). -/
def walkTestEvent (τ : (ℕ → ℤ) → ℕ∞) (G : ℤ → Set (ℕ → ℤ)) : Set (ℕ → ℤ) :=
  {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (x k)}

lemma stateProb_nonneg (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (y : ℤ) : 0 ≤ stateProb m G y :=
  ENNReal.toReal_nonneg

lemma stateProb_le_one (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (y : ℤ) : stateProb m G y ≤ 1 := by
  unfold stateProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := srwLaw m y) (s := G y))

lemma measurable_atRandomTime (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞)
    (hτ : IsWalkRandomTime τ) : Measurable (atRandomTime m G τ) := by
  have hτm : Measurable τ := by
    refine measurable_to_countable' fun k => ?_
    induction k using ENat.recTopCoe with
    | top =>
      have h : τ ⁻¹' {⊤} = (⋃ n : ℕ, {x | τ x = (n : ℕ∞)})ᶜ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists]
        constructor
        · intro hx n hn; exact ENat.natCast_ne_top n (hn.symm.trans hx)
        · intro h
          by_contra hne
          obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
          exact h n hn.symm
      rw [h]
      exact (MeasurableSet.iUnion fun n => histSigma_le n _ (hτ n)).compl
    | coe n => exact histSigma_le n _ (hτ n)
  let f : (ℕ → ℤ) × ℕ∞ → ℝ := fun p => if p.2 = ⊤ then 0 else stateProb m G (p.1 p.2.toNat)
  have hf : Measurable f := by
    refine measurable_from_prod_countable_left fun k => ?_
    induction k using ENat.recTopCoe with
    | top => simp only [f, ite_true]; exact measurable_const
    | coe n =>
      have : (fun x : ℕ → ℤ => f (x, (n : ℕ∞))) = fun x => stateProb m G (x n) := by
        ext x; simp [f]
      rw [this]
      exact (measurable_of_countable (stateProb m G)).comp (measurable_pi_apply n)
  exact hf.comp (measurable_id.prodMk hτm)

/-- `atRandomTime` is `F_τ`-measurable: on `{τ = k}` it is the function `φ(x_k)` of the history. -/
lemma measurable_atRandomTime_stopped (m : ℤ → ℤ → ℕ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞)
    (hτ : IsWalkRandomTime τ) : Measurable[stoppedSigma τ hτ] (atRandomTime m G τ) := by
  intro U hU
  refine ⟨measurable_atRandomTime m G τ hτ hU, fun k => ?_⟩
  have hφ : MeasurableSet[histSigma k] {x : ℕ → ℤ | stateProb m G (x k) ∈ U} := by
    refine MeasurableSpace.measurableSet_comap.2
      ⟨{f : Fin (k + 1) → ℤ | stateProb m G (f (Fin.last k)) ∈ U}, ?_, rfl⟩
    exact ((measurable_of_countable (stateProb m G)).comp (measurable_pi_apply (Fin.last k))) hU
  have hx : ∀ x : ℕ → ℤ, τ x = (k : ℕ∞) → atRandomTime m G τ x = stateProb m G (x k) := fun x h => by
    simp [atRandomTime, h]
  have hset : atRandomTime m G τ ⁻¹' U ∩ {x | τ x = (k : ℕ∞)} =
      {x | τ x = (k : ℕ∞)} ∩ {x | stateProb m G (x k) ∈ U} := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by show stateProb m G (x k) ∈ U; rw [← hx x h2]; exact h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨by show atRandomTime m G τ x ∈ U; rw [hx x h2]; exact h1, h2⟩
  show MeasurableSet[histSigma k] (atRandomTime m G τ ⁻¹' U ∩ {x | τ x = (k : ℕ∞)})
  rw [hset]
  exact (hτ k).inter hφ

lemma integrable_atRandomTime (m : ℤ → ℤ → ℕ) (a : ℤ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞)
    (hτ : IsWalkRandomTime τ) : Integrable (atRandomTime m G τ) (srwLaw m a) := by
  refine Integrable.of_bound (measurable_atRandomTime m G τ hτ).aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
  unfold atRandomTime
  split_ifs with h
  · simp
  · rw [Real.norm_eq_abs, abs_of_nonneg (stateProb_nonneg _ _ _)]
    exact stateProb_le_one _ _ _

/-- The fibre integral over `s ∩ {τ = k}`: there `atRandomTime = φ(X_k)`, and `φ(X_k) = (P^{X_k}(G(X_k))).toReal`. -/
lemma setIntegral_atRandomTime_fiber (m : ℤ → ℤ → ℕ) (a : ℤ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞)
    {s : Set (ℕ → ℤ)} (k : ℕ) (hs : MeasurableSet (s ∩ {x | τ x = (k : ℕ∞)})) :
    ∫ x in s ∩ {x | τ x = (k : ℕ∞)}, atRandomTime m G τ x ∂srwLaw m a =
      (∫⁻ x in s ∩ {x | τ x = (k : ℕ∞)}, srwLaw m (x k) (G (x k)) ∂srwLaw m a).toReal := by
  have hEq : EqOn (atRandomTime m G τ) (fun x => (srwLaw m (x k) (G (x k))).toReal)
      (s ∩ {x | τ x = (k : ℕ∞)}) := by
    intro x hx
    have h2 : τ x = (k : ℕ∞) := hx.2
    simp [atRandomTime, h2, stateProb]
  rw [setIntegral_congr_fun hs hEq]
  have hm : Measurable (fun x : ℕ → ℤ => srwLaw m (x k) (G (x k))) :=
    (measurable_of_countable (fun y : ℤ => srwLaw m y (G y))).comp (measurable_pi_apply k)
  refine integral_toReal hm.aemeasurable (ae_of_all _ fun x => ?_)
  exact lt_of_le_of_lt (prob_le_one) ENNReal.one_lt_top

/-- The integral over an `F_τ`-event splits over the fibres `{τ = k}` (`atRandomTime = 0` on `{τ = ∞}`). -/
lemma setIntegral_atRandomTime_eq_tsum (m : ℤ → ℤ → ℕ) (a : ℤ) (G : ℤ → Set (ℕ → ℤ)) (τ : (ℕ → ℤ) → ℕ∞)
    (hτ : IsWalkRandomTime τ) {s : Set (ℕ → ℤ)} (hs : MeasurableSet[stoppedSigma τ hτ] s) :
    ∫ x in s, atRandomTime m G τ x ∂srwLaw m a =
      ∑' k : ℕ, ∫ x in s ∩ {x | τ x = (k : ℕ∞)}, atRandomTime m G τ x ∂srwLaw m a := by
  have hsm : MeasurableSet s := hs.1
  have hfib : ∀ k : ℕ, MeasurableSet (s ∩ {x | τ x = (k : ℕ∞)}) := fun k =>
    hsm.inter (histSigma_le k _ (hτ k))
  have hdisj : Pairwise (Disjoint on fun k : ℕ => s ∩ {x | τ x = (k : ℕ∞)}) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun x hx hx' => hkk' ?_
    have h : (k : ℕ∞) = (k' : ℕ∞) := hx.2.symm.trans hx'.2
    exact_mod_cast h
  rw [← integral_iUnion hfib hdisj (integrable_atRandomTime m a G τ hτ).integrableOn]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hsm ?_ ?_
  · exact Set.iUnion_subset fun k => Set.inter_subset_left
  · intro x hx
    have htop : τ x = ⊤ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
      exact hx.2 (Set.mem_iUnion.2 ⟨n, hx.1, hn.symm⟩)
    simp [atRandomTime, htop]

/-- **Strong Markov property at a walk random time, conditional form.**
Under `srwLaw m a`, `E[1_B | F_τ] = φ(X_τ)` almost surely, where `B = walkTestEvent τ G` (the walk shifted at `τ`
lies in `G (X_τ)`) and `φ(y) = P^y(G y)` (`atRandomTime`). Discrete strong Markov property: Norris, *Markov Chains*,
Thm 1.4.2, in the form `srwLaw_strong_markov_state` (S4S6c/StrongMarkovState.lean). -/
theorem srwLaw_condExp_strong_markov (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : (ℕ → ℤ) → ℕ∞) (hτ : IsWalkRandomTime τ)
    (G : ℤ → Set (ℕ → ℤ)) (hG : ∀ y, MeasurableSet (G y)) :
    condExp (stoppedSigma τ hτ) (srwLaw m a) ((walkTestEvent τ G).indicator (fun _ => (1 : ℝ))) =ᵐ[srwLaw m a]
      atRandomTime m G τ := by
  have hB : MeasurableSet (walkTestEvent τ G) := by
    have hEq : walkTestEvent τ G = ⋃ k : ℕ, {x | τ x = (k : ℕ∞)} ∩ {x | pathShift k x ∈ G (x k)} := by
      ext x
      simp [walkTestEvent]
    rw [hEq]
    exact MeasurableSet.iUnion fun k =>
      (histSigma_le k _ (hτ k)).inter (measurableSet_future_at_state k hG)
  have hint_f : Integrable ((walkTestEvent τ G).indicator (fun _ => (1 : ℝ))) (srwLaw m a) :=
    (integrable_const (1 : ℝ)).indicator hB
  refine (ae_eq_condExp_of_forall_setIntegral_eq (stoppedSigma_le τ hτ) hint_f
    (fun s _ _ => (integrable_atRandomTime m a G τ hτ).integrableOn) ?_
    (measurable_atRandomTime_stopped m G τ hτ).aestronglyMeasurable).symm
  intro s hs _
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      s ∩ {x | τ x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
    intro k
    obtain ⟨F, hF, hEq⟩ := MeasurableSpace.measurableSet_comap.1 (hs.2 k)
    exact ⟨F, hF, hEq.symm⟩
  have hSM : srwLaw m a (s ∩ walkTestEvent τ G) =
      ∑' k : ℕ, ∫⁻ x in s ∩ {x | τ x = (k : ℕ∞)}, srwLaw m (x k) (G (x k)) ∂srwLaw m a :=
    srwLaw_strong_markov_state m a τ G hG hS
  have hfib : ∀ k : ℕ, ∫ x in s ∩ {x | τ x = (k : ℕ∞)}, atRandomTime m G τ x ∂srwLaw m a =
      (∫⁻ x in s ∩ {x | τ x = (k : ℕ∞)}, srwLaw m (x k) (G (x k)) ∂srwLaw m a).toReal :=
    fun k => setIntegral_atRandomTime_fiber m a G τ k (hs.1.inter (histSigma_le k _ (hτ k)))
  have hle : ∀ k : ℕ, ∫⁻ x in s ∩ {x | τ x = (k : ℕ∞)}, srwLaw m (x k) (G (x k)) ∂srwLaw m a ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ x in s ∩ {x | τ x = (k : ℕ∞)}, srwLaw m (x k) (G (x k)) ∂srwLaw m a
        ≤ ∫⁻ _ in s ∩ {x | τ x = (k : ℕ∞)}, (1 : ℝ≥0∞) ∂srwLaw m a := lintegral_mono fun x => prob_le_one
      _ ≤ 1 := by
        simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
        exact prob_le_one
  rw [setIntegral_indicator hB, setIntegral_const, smul_eq_mul, mul_one,
    setIntegral_atRandomTime_eq_tsum m a G τ hτ hs, tsum_congr hfib,
    ← ENNReal.tsum_toReal_eq hle, measureReal_def, hSM]

/-- The test event `G_j` of C15 at the state `y`: the walk started at `y` leaves `A` at a time before its exit from the
window `W y`. In the shifted frame at `T_j` this is `{∃ n, T_j ≤ n < T_{j+1}, X_n ∉ A}` (open-parts C15; bridge argument Step C).
Its complement is `TestBound68.stayIn W A y` (the walk stays in `A` until it exits `W y`). -/
def testEvent (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) : Set (ℕ → ℤ) :=
  {p | ∃ i : ℕ, (i : ℕ∞) < vExitTime (W y) p ∧ p i ∉ A}

lemma testEvent_compl (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) :
    (testEvent W A y)ᶜ = TestBound68.stayIn W A y := by
  ext p
  simp [testEvent, TestBound68.stayIn]

lemma measurableSet_testEvent (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) : MeasurableSet (testEvent W A y) := by
  have hEq : testEvent W A y = ⋃ i : ℕ, (⋂ j ∈ Set.Iic i, (fun p : ℕ → ℤ => p j) ⁻¹' W y) ∩
      (fun p : ℕ → ℤ => p i) ⁻¹' Aᶜ := by
    ext p
    simp [testEvent, natCast_lt_vExitTime_iff]
  rw [hEq]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.biInter (Set.finite_Iic i).countable fun j _ =>
      (measurable_pi_apply j) MeasurableSet.of_discrete
  · exact (measurable_pi_apply i) MeasurableSet.of_discrete

/-- **The conditional step of LEMMA68 for the concrete test events (C15).** For the random times `τ j`
(the stopping times `T_j` of C3) and the test events `G_j = walkTestEvent (τ j) (testEvent (W j) A)`, the conditional
test probability given `F_{τ j}` is at least `qStar / (1 + log(1/R_j))²` on `H_j`, almost surely.

Inputs:
* `hpt` is the per-test bound `srwLaw_y (stayIn) ≤ 1 - q(R_j)` at the state `y = X_{τ j}`: the conclusion of
  `printed_test_bound` (S4S6c/PerTest68.lean:82, the quenched B18/C15 bound) with the test radius `r := R j x`; its
  geometric hypotheses hold for `x ∈ H j` by the configuration (S6h.lean), and are not repeated here.
* `hfin` is the almost sure finiteness of `T_j` on `H_j`. The written argument (open-parts C15, "almost surely finite
  stopping time") states it but does not prove it; it is an input here.
* `hR` are the radius bounds of C3, `hq0`, `hq1` the constant bounds (`qStar = 1/(288 C_d² K²)` of `printed_test_bound`). -/
theorem hstep_concrete (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : ℕ → (ℕ → ℤ) → ℕ∞) (hτ : ∀ j, IsWalkRandomTime (τ j))
    (W : ℕ → ℤ → Set ℤ) (A : Set ℤ) (H : ℕ → Set (ℕ → ℤ)) (R : ℕ → (ℕ → ℤ) → ℝ) {qStar : ℝ}
    (hq0 : 0 ≤ qStar) (hq1 : qStar ≤ 1)
    (hR : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → 0 < R j x ∧ R j x ≤ 1)
    (hfin : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → τ j x < ⊤)
    (hpt : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ H j → τ j x < ⊤ →
      srwLaw m (x (τ j x).toNat) (TestBound68.stayIn (W j) A (x (τ j x).toNat)) ≤
        ENNReal.ofReal (1 - qStar / (1 + Real.log (1 / R j x)) ^ 2)) (j : ℕ) :
    ∀ᵐ x ∂srwLaw m a, x ∈ H j → qStar / (1 + Real.log (1 / R j x)) ^ 2 ≤
      condExp (stoppedSigma (τ j) (hτ j)) (srwLaw m a)
        ((walkTestEvent (τ j) (fun y => testEvent (W j) A y)).indicator (fun _ => (1 : ℝ))) x := by
  have hcond := srwLaw_condExp_strong_markov m a (τ j) (hτ j) (fun y => testEvent (W j) A y)
    (fun y => measurableSet_testEvent (W j) A y)
  filter_upwards [hcond, hfin j, hpt j, hR j] with x hcx hfx hptx hRx
  intro hxH
  rw [hcx]
  have hτx : τ j x ≠ ⊤ := (hfx hxH).ne
  unfold atRandomTime
  simp only [hτx, ↓reduceIte]
  show qStar / (1 + Real.log (1 / R j x)) ^ 2 ≤ (srwLaw m (x (τ j x).toNat) (testEvent (W j) A (x (τ j x).toNat))).toReal
  have hRpos := hRx hxH
  have hlog : 0 ≤ Real.log (1 / R j x) := Real.log_nonneg (one_le_one_div hRpos.1 hRpos.2)
  have hc1 : qStar / (1 + Real.log (1 / R j x)) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (1 + Real.log (1 / R j x)) ^ 2 := by nlinarith
    exact (div_le_self hq0 h1).trans hq1
  have hreal : (srwLaw m (x (τ j x).toNat) (TestBound68.stayIn (W j) A (x (τ j x).toNat))).toReal ≤
      1 - qStar / (1 + Real.log (1 / R j x)) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) (hptx hxH (hfx hxH))
  have hcompl : srwLaw m (x (τ j x).toNat) (TestBound68.stayIn (W j) A (x (τ j x).toNat)) =
      1 - srwLaw m (x (τ j x).toNat) (testEvent (W j) A (x (τ j x).toNat)) := by
    rw [← testEvent_compl, prob_compl_eq_one_sub (measurableSet_testEvent (W j) A (x (τ j x).toNat))]
  have hle : srwLaw m (x (τ j x).toNat) (testEvent (W j) A (x (τ j x).toNat)) ≤ 1 := prob_le_one
  rw [hcompl, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one] at hreal
  linarith

end S6j

end MatedCRT
