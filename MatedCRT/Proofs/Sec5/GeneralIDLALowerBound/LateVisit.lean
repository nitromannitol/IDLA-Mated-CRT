import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.LateCount
import MatedCRT.Proofs.IDLA.StrongMarkov

/-!
# Lemma 5.2: the upper tail of `L` (eq:strong-markov-reduction, eq:expected-value-of-l, lines 2187-2194)

With `p_z = P^z[τ_a < T_O]`, `θ = e^λ - 1` and the weight `Φ(S) = exp(θ ∑_{z ∈ O \ S} p_z)` of an aggregate `S`
(`remainingWeight`), one walker released from `S` satisfies `E[e^{λ 1{late}} Φ(S')] ≤ Φ(S)`, `S'` the next aggregate
(`lintegral_lateStep_le`): a late walker leaves `S` at a new site `z ∈ O`, after which it is a fresh walk from `z`
(strong Markov property at the exit time of `S`, `lintegral_hitTime_eq`), and `(1 + θ p_z) Φ(S ∪ {z}) ≤ Φ(S)`.
By induction over the walkers (`lintegral_lateCount_le`), `E[e^{λ L}] ≤ Φ(∅) = exp(θ μ)`, and Markov's inequality
gives `lateVisitCount_upperTail`. This is the exponential-moment form of `L ≤ L̂ = ∑_{z ∈ O} 1^z{τ_a < T}`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- `∑_{z ∈ O \ S} P^z[τ_a < T_O]`. -/
noncomputable def remainingMass (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (S : Set ℤ) : ℝ :=
  ∑' z : O, Sᶜ.indicator (fun w => hitBeforeExitProb m O a w) z

/-- The weight `Φ(S) = exp((e^λ - 1) ∑_{z ∈ O \ S} P^z[τ_a < T_O])`. -/
noncomputable def remainingWeight (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (l : ℝ) (S : Set ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((Real.exp l - 1) * remainingMass m O a S))

/-- `ψ(z) = 1{z ∈ O} Φ(S ∪ {z})`: the weight after a walker released from `S` is absorbed at `z ∈ O`. -/
noncomputable def lateWeight (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (l : ℝ) (S : Set ℤ) (z : ℤ) : ℝ≥0∞ :=
  O.indicator (fun z => remainingWeight m O a l (S ∪ {z})) z

/-- The event `{τ_a < T_O}` that the path hits `a` before exiting `O`. -/
def hitBeforeExitSet (O : Set ℤ) (a : ℤ) : Set (ℕ → ℤ) :=
  {y | vHitTime {a} y < vExitTime O y}

theorem remainingMass_empty (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) :
    remainingMass m O a ∅ = ∑' z : O, hitBeforeExitProb m O a z := by
  simp [remainingMass]

theorem remainingMass_nonneg (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (S : Set ℤ) : 0 ≤ remainingMass m O a S :=
  tsum_nonneg fun _ => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _

theorem summable_indicator_hitBeforeExitProb (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) (T : Set ℤ) :
    Summable (fun z : O => T.indicator (fun w => hitBeforeExitProb m O a w) z) :=
  Summable.of_nonneg_of_le (fun _ => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _)
    (fun z => Set.indicator_le_self' (fun _ _ => ENNReal.toReal_nonneg) (z : ℤ)) hsum

theorem remainingMass_eq_add (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) {S : Set ℤ} {z : ℤ} (hzO : z ∈ O) (hzS : z ∉ S) :
    remainingMass m O a S = hitBeforeExitProb m O a z + remainingMass m O a (S ∪ {z}) := by
  unfold remainingMass
  have hpt : ∀ w : O, Sᶜ.indicator (fun w => hitBeforeExitProb m O a w) w =
      ({z} : Set ℤ).indicator (fun w => hitBeforeExitProb m O a w) w +
        (S ∪ {z})ᶜ.indicator (fun w => hitBeforeExitProb m O a w) w := by
    intro w
    by_cases hw : (w : ℤ) = z
    · have h3 : z ∉ (S ∪ {z})ᶜ := by simp
      rw [hw, indicator_of_mem (mem_compl hzS), indicator_of_mem (mem_singleton z),
        indicator_of_notMem h3, add_zero]
    · have h1 : (w : ℤ) ∉ ({z} : Set ℤ) := hw
      rw [indicator_of_notMem h1, zero_add]
      by_cases hwS : (w : ℤ) ∈ S
      · have h4 : (w : ℤ) ∉ Sᶜ := by simp [hwS]
        have h5 : (w : ℤ) ∉ (S ∪ {z})ᶜ := by simp [hwS]
        rw [indicator_of_notMem h4, indicator_of_notMem h5]
      · have h5 : (w : ℤ) ∈ (S ∪ {z})ᶜ := by simp [hwS, hw]
        rw [indicator_of_mem (mem_compl hwS), indicator_of_mem h5]
  rw [tsum_congr hpt, Summable.tsum_add (summable_indicator_hitBeforeExitProb m O a hsum _)
    (summable_indicator_hitBeforeExitProb m O a hsum _)]
  congr 1
  have hsing : ∀ w : O, w ≠ ⟨z, hzO⟩ →
      ({z} : Set ℤ).indicator (fun w => hitBeforeExitProb m O a w) w = 0 := by
    intro w hw
    refine indicator_of_notMem ?_ _
    intro h
    exact hw (Subtype.ext h)
  rw [tsum_eq_single ⟨z, hzO⟩ hsing]
  exact indicator_of_mem (mem_singleton z) _

theorem remainingMass_union_of_not_mem (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) {S : Set ℤ} {z : ℤ}
    (hzO : z ∉ O) : remainingMass m O a (S ∪ {z}) = remainingMass m O a S := by
  unfold remainingMass
  refine tsum_congr fun w => ?_
  have hw : (w : ℤ) ≠ z := fun h => hzO (h ▸ w.2)
  by_cases hwS : (w : ℤ) ∈ S
  · have h4 : (w : ℤ) ∉ (S ∪ {z})ᶜ := by simp [hwS]
    have h5 : (w : ℤ) ∉ Sᶜ := by simp [hwS]
    rw [indicator_of_notMem h4, indicator_of_notMem h5]
  · have h4 : (w : ℤ) ∈ (S ∪ {z})ᶜ := by simp [hwS, hw]
    rw [indicator_of_mem h4, indicator_of_mem (mem_compl hwS)]

/-- A function of the first exit site from `S` is a measurable function of the path. -/
theorem measurable_comp_firstExitSite (S : Set ℤ) {β : Type*} [MeasurableSpace β] (c : Option ℤ → β) :
    Measurable fun x : ℕ → ℤ => c (firstExitSite S x) := by
  refine fun B _ => ?_
  have h : (fun x : ℕ → ℤ => c (firstExitSite S x)) ⁻¹' B =
      ⋃ o : Option ℤ, ⋃ (_ : c o ∈ B), {x : ℕ → ℤ | firstExitSite S x = o} := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨o, ho, hxo⟩ => hxo ▸ ho⟩
  rw [h]
  exact MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun _ =>
    Absorption.measurableSet_firstExitSite_eq S o

theorem hitBeforeExitProb_eq_lintegral (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a z : ℤ) :
    ∫⁻ y, (hitBeforeExitSet O a).indicator 1 y ∂srwLaw m z = ENNReal.ofReal (hitBeforeExitProb m O a z) := by
  rw [lintegral_indicator_one (show MeasurableSet (hitBeforeExitSet O a) from measurableSet_hitBeforeExit O a),
    hitBeforeExitProb, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

theorem measurable_hitTerm (S : Set ℤ) (k : ℕ) (g : ℤ → ℝ≥0∞) {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable ({x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator (fun x => g (x k) * F (pathShift k x))) :=
  (((measurable_of_countable g).comp (measurable_pi_apply k)).mul (hF.comp (measurable_pathShift k))).indicator
    (measurableSet_vHitTime_eq Sᶜ k)

theorem measurable_hitTerm' (S : Set ℤ) (k : ℕ) (g : ℤ → ℝ≥0∞) :
    Measurable ({x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator (fun x => g (x k))) :=
  ((measurable_of_countable g).comp (measurable_pi_apply k)).indicator (measurableSet_vHitTime_eq Sᶜ k)

theorem measurable_remainingWeight_aggStep (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (l : ℝ) (U S : Set ℤ) :
    Measurable fun x : ℕ → ℤ => remainingWeight m O a l (Absorption.aggStep U S x) := by
  have h : (fun x : ℕ → ℤ => remainingWeight m O a l (Absorption.aggStep U S x)) =
      fun x => (fun o => remainingWeight m O a l (Absorption.nextAgg U S o)) (firstExitSite S x) := by
    funext x
    rw [Absorption.aggStep_eq]
  rw [h]
  exact measurable_comp_firstExitSite S (fun o => remainingWeight m O a l (Absorption.nextAgg U S o))

/-- At a finite exit time `k` from `S`: `τ_{Sᶜ} = k`, `X_k ∉ S`, and `X_k` is the first exit site. -/
theorem exit_facts {S : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (hσ : vExitTime S x = k) :
    vHitTime Sᶜ x = k ∧ x k ∉ S ∧ firstExitSite S x = some (x k) := by
  refine ⟨?_, apply_vExitTime_not_mem hσ, Absorption.firstExitSite_eq_some_iff.2
    ⟨k, rfl, apply_vExitTime_not_mem hσ, fun j hj => mem_of_lt_vExitTime (by rw [hσ]; exact_mod_cast hj)⟩⟩
  show vExitTime Sᶜᶜ x = k
  rw [compl_compl]
  exact hσ

/-- On `{τ_{Sᶜ} = k}` only the `k`-th term of the decomposition over the values of `τ_{Sᶜ}` survives. -/
theorem tsum_indicator_hit_eq {S : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (hk : vHitTime Sᶜ x = k)
    (G : ℕ → (ℕ → ℤ) → ℝ≥0∞) :
    ∑' j : ℕ, {x : ℕ → ℤ | vHitTime Sᶜ x = j}.indicator (G j) x = G k x := by
  have hne : ∀ j : ℕ, j ≠ k → {x : ℕ → ℤ | vHitTime Sᶜ x = j}.indicator (G j) x = 0 := by
    intro j hj
    refine indicator_of_notMem ?_ _
    intro h
    have h' : vHitTime Sᶜ x = j := h
    rw [hk] at h'
    exact hj (by exact_mod_cast h'.symm)
  rw [tsum_eq_single k hne]
  exact indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime Sᶜ x = k} from hk) _

/-- A walk which hits `a` at time `t < T_O` and is shifted by `k ≤ t` still hits `a` before exiting `O`. -/
theorem shift_mem_hitBeforeExitSet {O : Set ℤ} {a : ℤ} {x : ℕ → ℤ} {k t : ℕ} (hkt : k ≤ t)
    (hτ : vHitTime {a} x = t) (htT : (t : ℕ∞) < vExitTime O x) :
    pathShift k x ∈ hitBeforeExitSet O a := by
  have hkT : (k : ℕ∞) < vExitTime O x := lt_of_le_of_lt (by exact_mod_cast hkt) htT
  have hO' : ∀ j ≤ k, x j ∈ O := fun j hj => natCast_lt_vExitTime_iff.1 hkT j hj
  have hτ' : vHitTime {a} (pathShift k x) = ((t - k : ℕ) : ℕ∞) := by
    unfold vHitTime
    rw [vExitTime_eq_natCast_iff]
    refine ⟨fun h => ?_, fun j hj => ?_⟩
    · have h3 := mem_of_lt_vExitTime h
      simp only [pathShift, Nat.sub_add_cancel hkt] at h3
      exact h3 (apply_vHitTime_eq hτ)
    · exact mem_of_lt_vExitTime (A := ({a} : Set ℤ)ᶜ) (x := x) (k := j + k)
        (by
          show ((j + k : ℕ) : ℕ∞) < vHitTime {a} x
          rw [hτ]
          exact_mod_cast (by omega : j + k < t))
  show vHitTime {a} (pathShift k x) < vExitTime O (pathShift k x)
  rw [hτ', ← lt_vExitTime_add_iff hO', Nat.sub_add_cancel hkt]
  exact htT

open Classical in
/-- Pointwise bound before the strong Markov property: a late walker leaves `S` at `z = X_σ ∈ O`, after which the
shifted walk hits `a` before exiting `O`. -/
theorem lateStep_pointwise_le (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) {l : ℝ} (hl : 0 ≤ l) {U : Set ℤ}
    (hU : O ⊆ U) (S : Set ℤ) (x : ℕ → ℤ) :
    ENNReal.ofReal (Real.exp (l * ((if IsLateVisit O a S x then 1 else 0 : ℕ) : ℝ))) *
        remainingWeight m O a l (Absorption.aggStep U S x) ≤
      remainingWeight m O a l (Absorption.aggStep U S x) + ENNReal.ofReal (Real.exp l - 1) *
        ∑' k : ℕ, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
          (fun x => lateWeight m O a l S (x k) * (hitBeforeExitSet O a).indicator 1 (pathShift k x)) x := by
  have hθ0 : 0 ≤ Real.exp l - 1 := by linarith [Real.add_one_le_exp l]
  by_cases hlate : IsLateVisit O a S x
  · obtain ⟨h1, h2⟩ := id hlate
    have hσne : vExitTime S x ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_lt h2) h1
    obtain ⟨k, hσ⟩ : ∃ k : ℕ, vExitTime S x = k := ⟨_, (ENat.natCast_toNat hσne).symm⟩
    have hτne : vHitTime {a} x ≠ ⊤ := ne_top_of_lt h2
    obtain ⟨t, hτ⟩ : ∃ t : ℕ, vHitTime {a} x = t := ⟨_, (ENat.natCast_toNat hτne).symm⟩
    have hkt : k ≤ t := by
      have h1' := h1
      rw [hσ, hτ] at h1'
      exact_mod_cast h1'
    have htT : (t : ℕ∞) < vExitTime O x := hτ ▸ h2
    have hkT : (k : ℕ∞) < vExitTime O x := lt_of_le_of_lt (by exact_mod_cast hkt) htT
    obtain ⟨hhit, hzS, hfes⟩ := exit_facts hσ
    have hzO : x k ∈ O := mem_of_lt_vExitTime hkT
    have hagg : Absorption.aggStep U S x = S ∪ {x k} := by
      rw [Absorption.aggStep_eq, hfes]
      simp [Absorption.nextAgg, hU hzO]
    have hHk : pathShift k x ∈ hitBeforeExitSet O a := shift_mem_hitBeforeExitSet hkt hτ htT
    rw [tsum_indicator_hit_eq hhit, ite_eq_left hlate, Nat.cast_one, mul_one, hagg]
    simp only [lateWeight, indicator_of_mem hzO, indicator_of_mem hHk, Pi.one_apply, mul_one]
    rw [show Real.exp l = 1 + (Real.exp l - 1) by ring, ENNReal.ofReal_add zero_le_one hθ0, ENNReal.ofReal_one,
      add_mul, one_mul]
    simp only [add_sub_cancel_left, le_refl]
  · rw [ite_eq_right hlate, Nat.cast_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_self_add

/-- Pointwise bound after the strong Markov property: `Φ(S') + θ 1{z ∈ O} p_z Φ(S ∪ {z}) ≤ Φ(S)`. -/
theorem lateStep_pointwise_le' (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) {l : ℝ} (hl : 0 ≤ l) {U : Set ℤ} (hU : O ⊆ U)
    (S : Set ℤ) (x : ℕ → ℤ) :
    remainingWeight m O a l (Absorption.aggStep U S x) + ENNReal.ofReal (Real.exp l - 1) *
        ∑' k : ℕ, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
          (fun x => lateWeight m O a l S (x k) * ENNReal.ofReal (hitBeforeExitProb m O a (x k))) x ≤
      remainingWeight m O a l S := by
  have hθ0 : 0 ≤ Real.exp l - 1 := by linarith [Real.add_one_le_exp l]
  induction hσ : vExitTime S x using ENat.recTopCoe with
  | top =>
    have hall : ∀ n, x n ∈ S := vExitTime_eq_top_iff.1 hσ
    have hnone : firstExitSite S x = none := Absorption.firstExitSite_eq_none_iff.2 hall
    have hzero : ∀ k : ℕ, x ∉ {x : ℕ → ℤ | vHitTime Sᶜ x = k} := fun k h => by
      have h' : vExitTime Sᶜᶜ x = k := h
      rw [compl_compl, hσ] at h'
      exact ENat.natCast_ne_top k h'.symm
    rw [ENNReal.tsum_eq_zero.2 fun k => indicator_of_notMem (hzero k) _, mul_zero, add_zero,
      Absorption.aggStep_eq, hnone]
    exact le_rfl
  | coe k =>
    obtain ⟨hhit, hzS, hfes⟩ := exit_facts hσ
    rw [tsum_indicator_hit_eq hhit, Absorption.aggStep_eq, hfes]
    by_cases hzO : x k ∈ O
    · have hnext : Absorption.nextAgg U S (some (x k)) = S ∪ {x k} := by
        simp [Absorption.nextAgg, hU hzO]
      simp only [hnext, lateWeight, indicator_of_mem hzO]
      unfold remainingWeight
      rw [remainingMass_eq_add m O a hsum hzO hzS]
      have hpz : 0 ≤ hitBeforeExitProb m O a (x k) := ENNReal.toReal_nonneg
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hθ0,
        ← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg hθ0 (mul_nonneg (Real.exp_pos _).le hpz))]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_add, Real.exp_add]
      have h1 := Real.add_one_le_exp ((Real.exp l - 1) * hitBeforeExitProb m O a (x k))
      have h2 := Real.exp_pos ((Real.exp l - 1) * remainingMass m O a (S ∪ {x k}))
      nlinarith [mul_le_mul_of_nonneg_right h1 h2.le]
    · have hψ0 : lateWeight m O a l S (x k) = 0 := indicator_of_notMem hzO _
      simp only [hψ0, zero_mul, mul_zero, add_zero]
      by_cases hzU : x k ∈ U
      · have hnext : Absorption.nextAgg U S (some (x k)) = S ∪ {x k} := by
          simp [Absorption.nextAgg, hzU]
        rw [hnext]
        unfold remainingWeight
        rw [remainingMass_union_of_not_mem m O a hzO]
      · have hnext : Absorption.nextAgg U S (some (x k)) = S := by
          simp [Absorption.nextAgg, hzU]
        rw [hnext]

open Classical in
/-- **One walker**: `E^0[e^{λ 1{late}} Φ(S')] ≤ Φ(S)`, `S'` the aggregate after the walker. -/
theorem lintegral_lateStep_le (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) {l : ℝ} (hl : 0 ≤ l) {U : Set ℤ} (hU : O ⊆ U)
    (S : Set ℤ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (l * ((if IsLateVisit O a S x then 1 else 0 : ℕ) : ℝ))) *
        remainingWeight m O a l (Absorption.aggStep U S x) ∂srwLaw m 0 ≤ remainingWeight m O a l S := by
  have hHm : MeasurableSet (hitBeforeExitSet O a) := measurableSet_hitBeforeExit O a
  have hΦagg := measurable_remainingWeight_aggStep m O a l U S
  have hT1 : ∀ k : ℕ, Measurable ({x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
      (fun x => lateWeight m O a l S (x k) * (hitBeforeExitSet O a).indicator 1 (pathShift k x))) := fun k =>
    measurable_hitTerm S k (lateWeight m O a l S) (measurable_one.indicator hHm)
  have hT2 : ∀ k : ℕ, Measurable ({x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
      (fun x => lateWeight m O a l S (x k) * ENNReal.ofReal (hitBeforeExitProb m O a (x k)))) := fun k =>
    measurable_hitTerm' S k fun z => lateWeight m O a l S z * ENNReal.ofReal (hitBeforeExitProb m O a z)
  have hSM : ∀ k : ℕ, ∫⁻ x, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
        (fun x => lateWeight m O a l S (x k) * (hitBeforeExitSet O a).indicator 1 (pathShift k x)) x
        ∂srwLaw m 0 =
      ∫⁻ x, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
        (fun x => lateWeight m O a l S (x k) * ENNReal.ofReal (hitBeforeExitProb m O a (x k))) x ∂srwLaw m 0 := by
    intro k
    rw [lintegral_hitTime_eq m Sᶜ (lateWeight m O a l S) (measurable_one.indicator hHm) k 0]
    simp only [hitBeforeExitProb_eq_lintegral]
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (l * ((if IsLateVisit O a S x then 1 else 0 : ℕ) : ℝ))) *
        remainingWeight m O a l (Absorption.aggStep U S x) ∂srwLaw m 0
      ≤ ∫⁻ x, (remainingWeight m O a l (Absorption.aggStep U S x) + ENNReal.ofReal (Real.exp l - 1) *
          ∑' k : ℕ, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
            (fun x => lateWeight m O a l S (x k) * (hitBeforeExitSet O a).indicator 1 (pathShift k x)) x)
          ∂srwLaw m 0 := lintegral_mono fun x => lateStep_pointwise_le m O a hl hU S x
    _ = ∫⁻ x, (remainingWeight m O a l (Absorption.aggStep U S x) + ENNReal.ofReal (Real.exp l - 1) *
          ∑' k : ℕ, {x : ℕ → ℤ | vHitTime Sᶜ x = k}.indicator
            (fun x => lateWeight m O a l S (x k) * ENNReal.ofReal (hitBeforeExitProb m O a (x k))) x)
          ∂srwLaw m 0 := by
        rw [lintegral_add_left hΦagg, lintegral_add_left hΦagg, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum fun k => (hT1 k).aemeasurable,
          lintegral_tsum fun k => (hT2 k).aemeasurable]
        simp only [hSM]
    _ ≤ ∫⁻ _, remainingWeight m O a l S ∂srwLaw m 0 :=
        lintegral_mono fun x => lateStep_pointwise_le' m O a hsum hl hU S x
    _ = remainingWeight m O a l S := by rw [lintegral_const, measure_univ, mul_one]

/-- **The walkers**: `E[e^{λ L}] ≤ Φ(S)` for `k` walkers released from `S`. -/
theorem lintegral_lateCount_le (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) {l : ℝ} (hl : 0 ≤ l) {U : Set ℤ} (hU : O ⊆ U) :
    ∀ (k : ℕ) (S : Set ℤ), ∫⁻ ys, ENNReal.ofReal (Real.exp (l * lateCount U O a S (List.ofFn ys)))
      ∂walkersLaw m (fun _ : Fin k => (0 : ℤ)) ≤ remainingWeight m O a l S
  | 0, S => by
    have h0 : ∀ ys : Fin 0 → ℕ → ℤ, List.ofFn ys = [] := fun _ => List.ofFn_zero
    have hθ0 : 0 ≤ Real.exp l - 1 := by linarith [Real.add_one_le_exp l]
    simp only [h0, lateCount, Nat.cast_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_const,
      measure_univ, mul_one]
    unfold remainingWeight
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hθ0 (remainingMass_nonneg m O a S)))
  | k + 1, S => by
    have hF : Measurable fun ys : Fin (k + 1) → ℕ → ℤ =>
        ENNReal.ofReal (Real.exp (l * lateCount U O a S (List.ofFn ys))) :=
      (measurable_of_countable fun j : ℕ => ENNReal.ofReal (Real.exp (l * j))).comp
        (measurable_lateCount U O a (k + 1) S)
    rw [Absorption.lintegral_walkersLaw_succ m _ _ hF]
    refine le_trans (lintegral_mono fun x => ?_) (lintegral_lateStep_le m O a hsum hl hU S)
    simp only [Absorption.ofFn_cons', lateCount, Nat.cast_add, mul_add, Real.exp_add, ENNReal.ofReal_mul,
      Real.exp_nonneg]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (lintegral_lateCount_le m O a hsum hl hU k _)

/-- The Chernoff bound for the upper tail of `L`: `P[L ≥ k] ≤ exp(-λ k + (e^λ - 1) μ)`, for the IDLA cluster and for
the cluster with walkers stopped upon exiting `O` (the content of `LateVisitUpperTailStep`). -/
theorem lateVisitCount_upperTail (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (n : ℕ) (l k : ℝ) (hl : 0 ≤ l)
    (hsum : Summable (fun z : O => hitBeforeExitProb m O a z)) :
    walkerSequenceLaw m 0 {xs | k ≤ (lateVisitCount (idlaCluster xs) O a xs n : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z)) ∧
      walkerSequenceLaw m 0 {xs | k ≤ (lateVisitCount (stoppedIDLACluster O xs) O a xs n : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z)) := by
  have key : ∀ U : Set ℤ, O ⊆ U → ∀ L : (ℕ → ℕ → ℤ) → ℕ,
      (∀ xs, L xs = lateCount U O a ∅ (List.ofFn fun i : Fin n => xs i)) →
      walkerSequenceLaw m 0 {xs | k ≤ (L xs : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z)) := by
    intro U hU L hL
    set f : (Fin n → ℕ → ℤ) → ℝ≥0∞ :=
      fun ys => ENNReal.ofReal (Real.exp (l * lateCount U O a ∅ (List.ofFn ys))) with hf
    have hfm : Measurable f := (measurable_of_countable fun j : ℕ => ENNReal.ofReal (Real.exp (l * j))).comp
      (measurable_lateCount U O a n ∅)
    have hset : {xs : ℕ → ℕ → ℤ | k ≤ (L xs : ℝ)} ⊆ (fun xs : ℕ → ℕ → ℤ => fun i : Fin n => xs i) ⁻¹'
        {ys | ENNReal.ofReal (Real.exp (l * k)) ≤ f ys} := by
      intro xs hxs
      show ENNReal.ofReal (Real.exp (l * k)) ≤
        ENNReal.ofReal (Real.exp (l * lateCount U O a ∅ (List.ofFn fun i : Fin n => xs i)))
      rw [← hL xs]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxs hl))
    have hmeas : MeasurableSet {ys : Fin n → ℕ → ℤ | ENNReal.ofReal (Real.exp (l * k)) ≤ f ys} :=
      measurableSet_le measurable_const hfm
    calc walkerSequenceLaw m 0 {xs | k ≤ (L xs : ℝ)}
        ≤ walkerSequenceLaw m 0 ((fun xs : ℕ → ℕ → ℤ => fun i : Fin n => xs i) ⁻¹'
            {ys | ENNReal.ofReal (Real.exp (l * k)) ≤ f ys}) := measure_mono hset
      _ = walkersLaw m (fun _ => 0) {ys | ENNReal.ofReal (Real.exp (l * k)) ≤ f ys} := by
          rw [← walkerSequenceLaw_map_fin m 0 n, Measure.map_apply (measurable_restrictFin n) hmeas]
      _ = ENNReal.ofReal (Real.exp (-(l * k))) * (ENNReal.ofReal (Real.exp (l * k)) *
            walkersLaw m (fun _ => 0) {ys | ENNReal.ofReal (Real.exp (l * k)) ≤ f ys}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
            Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-(l * k))) * ∫⁻ ys, f ys ∂walkersLaw m (fun _ => 0) :=
          mul_le_mul' le_rfl (mul_meas_ge_le_lintegral₀ hfm.aemeasurable _)
      _ ≤ ENNReal.ofReal (Real.exp (-(l * k))) * remainingWeight m O a l ∅ :=
          mul_le_mul' le_rfl (lintegral_lateCount_le m O a hsum hl hU n ∅)
      _ = ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z)) := by
          unfold remainingWeight
          rw [remainingMass_empty, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ⟨key univ (subset_univ _) _ fun xs => lateVisitCount_eq_lateCount univ O a xs n,
    key O subset_rfl _ fun xs => lateVisitCount_eq_lateCount O O a xs n⟩

end MatedCRT
