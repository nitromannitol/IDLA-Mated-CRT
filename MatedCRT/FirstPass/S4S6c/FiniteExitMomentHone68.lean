import MatedCRT.FirstPass.S4S6c.FiniteExitMoment68
import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S4S6c.WalkBridge68
import MatedCRT.FirstPass.S6r.OneTest.Count

/-!
# Integrability of the test count on finite test domains (fp-S4S6c-exit-moment, items (2) and (3))

Stage 1: monotonicity of the exit time in the set, the stopping-time bridge to `S6j.IsWalkRandomTime`,
the geometric tail of the post-`T` exit time (strong Markov at `T`, `FiniteExitMoment68.srwLaw_tail_le`),
and measurability of the post-`T` event.
-/

namespace MatedCRT
namespace FiniteExitMomentHone68

open MeasureTheory Set Filter
open Lemma68WalkBridge Lemma68Window Function
open scoped ENNReal

/-- The first exit time is monotone in the set: `I ⊆ G` gives `τ_I ≤ τ_G` (Armitage–Gardiner). -/
lemma vExitTime_mono_set {I G : Set ℤ} (hIG : I ⊆ G) (x : ℕ → ℤ) :
    vExitTime I x ≤ vExitTime G x := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  rw [← hn] at hlt
  have h2 := natCast_lt_vExitTime_iff.1 hlt
  have h3 : (n : ℕ∞) < vExitTime G x :=
    natCast_lt_vExitTime_iff.2 fun j hj => hIG (h2 j hj)
  rw [hn] at h3
  exact lt_irrefl _ h3

/-- A natural number below the `toNat` of an `ℕ∞` value is below the value. -/
lemma natCast_lt_of_lt_toNat (n : ℕ) (z : ℕ∞) (h : n < z.toNat) : (n : ℕ∞) < z := by
  induction z using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    rw [ENat.toNat_natCast] at h
    exact_mod_cast h

/-- A stopping time for the coordinate filtration is a walk random time (`S6j.IsWalkRandomTime`). -/
lemma isWalkRandomTime_of_isStoppingTime {τ : (ℕ → ℤ) → ℕ∞} (hτ : IsStoppingTime coordFiltration τ) :
    S6j.IsWalkRandomTime τ := by
  intro k
  have hle : MeasurableSet[coordFiltration k] {x : ℕ → ℤ | τ x ≤ (k : ℕ∞)} := hτ k
  have hlt : MeasurableSet[coordFiltration k] {x : ℕ → ℤ | τ x < (k : ℕ∞)} :=
    hτ.measurableSet_lt_of_pred k
  have h1 : MeasurableSet[coordFiltration k] {x : ℕ → ℤ | τ x = (k : ℕ∞)} := by
    have hset : {x : ℕ → ℤ | τ x = (k : ℕ∞)} =
        {x : ℕ → ℤ | τ x ≤ (k : ℕ∞)} \ {x : ℕ → ℤ | τ x < (k : ℕ∞)} := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · intro h
        exact ⟨h.le, not_lt.2 h.ge⟩
      · rintro ⟨h1, h2⟩
        exact le_antisymm h1 (not_lt.1 h2)
    rw [hset]
    exact hle.diff hlt
  have h2 : coordFiltration k ≤ S6j.histSigma k := by
    unfold coordFiltration Filtration.natural
    refine iSup₂_le fun j hj => ?_
    have hm : Measurable[S6j.histSigma k] (fun x : ℕ → ℤ => x j) :=
      (measurable_pi_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1))).comp
        (comap_measurable (pathHist k))
    exact hm.comap_le
  exact h2 _ h1

/-- The set `{x | (T x)<⊤ ∧ c < τ_G(post-T path)}` is measurable for a walk random time `T`. -/
lemma measurableSet_postTime_gt {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T) (G : Set ℤ) (c : ℕ) :
    MeasurableSet {x : ℕ → ℤ | T x < ⊤ ∧ (c : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} := by
  have hset : {x : ℕ → ℤ | T x < ⊤ ∧ (c : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} =
      ⋃ k : ℕ, {x : ℕ → ℤ | T x = (k : ℕ∞)} ∩
        (fun x : ℕ → ℤ => fun n => x (k + n)) ⁻¹' {y : ℕ → ℤ | (c : ℕ∞) < vExitTime G y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hT, hc⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hT.ne
      refine ⟨k, hk.symm, ?_⟩
      have htn : (T x).toNat = k := by rw [← hk, ENat.toNat_natCast]
      have hfun : (fun n => x (k + n)) = postTimePath (fun n w => w n) T x := by
        funext n
        simp only [postTimePath, htn]
      rw [hfun]
      exact hc
    · rintro ⟨k, hk, hc⟩
      have htn : (T x).toNat = k := by rw [hk, ENat.toNat_natCast]
      have hfun : (fun n => x (k + n)) = postTimePath (fun n w => w n) T x := by
        funext n
        simp only [postTimePath, htn]
      refine ⟨by rw [hk]; exact ENat.natCast_lt_top k, ?_⟩
      rw [← hfun]
      exact hc
  rw [hset]
  refine MeasurableSet.iUnion fun k => ?_
  exact (S6j.histSigma_le k _ (hTw k)).inter
    ((Measurable.of_eval fun n => measurable_pi_apply (k + n))
      (measurableSet_natCast_lt_vExitTime G c))

/-- **Geometric tail of the post-`T` exit time.** For a walk random time `T`, the probability that `T < ⊤` and
the exit time of the post-`T` path from `G` exceeds `j L` is at most `2^{-j}`, from every start `a`, provided
`P_b(L < τ_G) ≤ 1/2` for all `b` (strong Markov at `T`, `srwLaw_strong_markov_state`). -/
lemma srwLaw_postTime_gt_le {m : ℤ → ℤ → ℕ} {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T)
    {G : Set ℤ} {L : ℕ} (hL : ∀ b : ℤ, srwLaw m b {x | (L : ℕ∞) < vExitTime G x} ≤ 1 / 2)
    (j : ℕ) (a : ℤ) :
    srwLaw m a {x | T x < ⊤ ∧ ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} ≤
      (1 / 2 : ℝ≥0∞) ^ j := by
  set E : Set (ℕ → ℤ) := {y | ((j * L : ℕ) : ℕ∞) < vExitTime G y} with hEdef
  have hEm : MeasurableSet E := measurableSet_natCast_lt_vExitTime G (j * L)
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      (univ : Set (ℕ → ℤ)) ∩ {x | T x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
    intro k
    obtain ⟨F, hF, hpre⟩ := MeasurableSpace.measurableSet_comap.1 (hTw k)
    exact ⟨F, hF, by rw [univ_inter]; exact hpre.symm⟩
  have key := srwLaw_strong_markov_state m a T (fun _ => E) (fun _ => hEm) hS
  have hevent : {x : ℕ → ℤ | T x < ⊤ ∧ ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} =
      univ ∩ {x : ℕ → ℤ | ∃ k : ℕ, T x = (k : ℕ∞) ∧ WalkPotential.pathShift k x ∈ E} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_univ, true_and]
    constructor
    · rintro ⟨hT, hc⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hT.ne
      refine ⟨k, hk.symm, ?_⟩
      have htn : (T x).toNat = k := by rw [← hk, ENat.toNat_natCast]
      have hfun : WalkPotential.pathShift k x = postTimePath (fun n w => w n) T x := by
        funext n
        simp only [WalkPotential.pathShift, postTimePath, htn]
      show ((j * L : ℕ) : ℕ∞) < vExitTime G (WalkPotential.pathShift k x)
      rw [hfun]
      exact hc
    · rintro ⟨k, hk, hE⟩
      have htn : (T x).toNat = k := by rw [hk, ENat.toNat_natCast]
      have hfun : WalkPotential.pathShift k x = postTimePath (fun n w => w n) T x := by
        funext n
        simp only [WalkPotential.pathShift, postTimePath, htn]
      refine ⟨by rw [hk]; exact ENat.natCast_lt_top k, ?_⟩
      rw [← hfun]
      exact hE
  rw [hevent, key]
  have hdisj : Pairwise (Disjoint on fun k : ℕ => univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj => hij ?_
    have hi' : T x = (i : ℕ∞) := hi.2
    have hj' : T x = (j : ℕ∞) := hj.2
    have h : ((i : ℕ) : ℕ∞) = (j : ℕ∞) := hi'.symm.trans hj'
    exact_mod_cast h
  have hmeas : ∀ k : ℕ, MeasurableSet (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) := fun k => by
    rw [univ_inter]
    exact S6j.histSigma_le k _ (hTw k)
  have hk : ∀ k : ℕ, ∫⁻ x in (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}), srwLaw m (x k) E ∂srwLaw m a ≤
      (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) := by
    intro k
    calc ∫⁻ x in (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}), srwLaw m (x k) E ∂srwLaw m a
        ≤ ∫⁻ _ in (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}), (1 / 2 : ℝ≥0∞) ^ j ∂srwLaw m a :=
          lintegral_mono fun x => FiniteExitMoment68.srwLaw_tail_le hL j (x k)
      _ = (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) :=
          setLIntegral_const _ _
  calc ∑' k : ℕ, ∫⁻ x in (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}), srwLaw m (x k) E ∂srwLaw m a
      ≤ ∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) :=
        ENNReal.tsum_le_tsum hk
    _ = (1 / 2 : ℝ≥0∞) ^ j * ∑' k : ℕ, srwLaw m a (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) :=
        ENNReal.tsum_mul_left
    _ = (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a (⋃ k : ℕ, univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}) := by
        rw [measure_iUnion hdisj hmeas]
    _ ≤ (1 / 2 : ℝ≥0∞) ^ j * 1 :=
        mul_le_mul_of_nonneg_left prob_le_one (by exact zero_le)
    _ = (1 / 2 : ℝ≥0∞) ^ j := mul_one _

end FiniteExitMomentHone68
end MatedCRT
