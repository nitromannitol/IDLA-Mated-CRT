import MatedCRT.FirstPass.S4S6c.FiniteExitMoment68
import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S4S6c.WalkBridge68
import MatedCRT.FirstPass.S6r.OneTest.Count
import MatedCRT.FirstPass.S4S6c.HoneWalk
import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S3i.StrongMarkov
import MatedCRT.FirstPass.S5c.GreenUpper

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

/-- Block bound for the `p`-th power of a natural number (`0 < p`). -/
lemma nat_pow_le_tsum_block (p L : ℕ) (hp : 0 < p) (hL : 0 < L) (n : ℕ) :
    ((n : ℝ≥0∞)) ^ p ≤ ∑' k : ℕ, (if k * L < n then (((k + 1) * L : ℕ) : ℝ≥0∞) ^ p else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow hp.ne']
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hdiv : (m / L) * L + m % L = m := by
      rw [mul_comm]
      exact Nat.div_add_mod m L
    have hmod := Nat.mod_lt m hL
    have hmod' : m % L + 1 ≤ L := hmod
    set q := m / L with hq
    have h1 : q * L < m + 1 := by linarith [Nat.zero_le (m % L)]
    have h2 : m + 1 ≤ (q + 1) * L := by
      rw [add_mul, one_mul]
      linarith
    have h2' : ((m + 1 : ℕ) : ℝ≥0∞) ≤ (((q + 1) * L : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h2
    calc (((m + 1 : ℕ)) : ℝ≥0∞) ^ p ≤ (((q + 1) * L : ℕ) : ℝ≥0∞) ^ p := by gcongr
      _ = (if q * L < m + 1 then (((q + 1) * L : ℕ) : ℝ≥0∞) ^ p else 0) := by simp [h1]
      _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ => if k * L < m + 1 then
          (((k + 1) * L : ℕ) : ℝ≥0∞) ^ p else 0) q

/-- `{T < ⊤}` is measurable for a walk random time. -/
lemma measurableSet_lt_top_of_walk {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T) :
    MeasurableSet {x : ℕ → ℤ | T x < ⊤} := by
  have hset : {x : ℕ → ℤ | T x < ⊤} = ⋃ k : ℕ, {x : ℕ → ℤ | T x = (k : ℕ∞)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      rw [hk]
      exact ENat.natCast_lt_top k
  rw [hset]
  exact MeasurableSet.iUnion fun k => S6j.histSigma_le k _ (hTw k)

/-- **Integrability of the post-`T` exit count on a finite test domain (core).** For a walk random time `T`
and `Z ≤ τ_G(post-T path)` almost surely on `{T < ⊤}`, the function `1_{T<⊤} (toNat Z)^p` is integrable for
every `p > 0` for which `∑_k ((k+1)L)^p 2^{-k} < ∞`. -/
lemma integrable_postTime_pow {m : ℤ → ℤ → ℕ} {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T)
    {G : Set ℤ} {L : ℕ} (hL0 : 0 < L)
    (hL : ∀ b : ℤ, srwLaw m b {x | (L : ℕ∞) < vExitTime G x} ≤ 1 / 2)
    {a : ℤ} {Z : (ℕ → ℤ) → ℕ∞} (hZm : Measurable fun x => (Z x).toNat)
    (hZ : ∀ᵐ x ∂srwLaw m a, T x < ⊤ → Z x ≤ vExitTime G (postTimePath (fun n w => w n) T x))
    (p : ℕ) (hp : 0 < p)
    (hfin : ∑' k : ℕ, (((k + 1) * L : ℕ) : ℝ≥0∞) ^ p * (1 / 2 : ℝ≥0∞) ^ k ≠ ⊤) :
    Integrable ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => ((Z x).toNat : ℝ) ^ p)) (srwLaw m a) := by
  have hTm := measurableSet_lt_top_of_walk hTw
  have hEm : ∀ j : ℕ, MeasurableSet {x : ℕ → ℤ | T x < ⊤ ∧
      ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} :=
    fun j => measurableSet_postTime_gt hTw G (j * L)
  have hfm : Measurable (fun x : ℕ → ℤ =>
      ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => (((Z x).toNat : ℕ) : ℝ≥0∞) ^ p)) x) :=
    ((measurable_from_nat.comp hZm).pow_const p).indicator hTm
  have hkey : ∀ᵐ x ∂srwLaw m a,
      ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => (((Z x).toNat : ℕ) : ℝ≥0∞) ^ p)) x ≤
        ∑' j : ℕ, {x : ℕ → ℤ | T x < ⊤ ∧
          ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)}.indicator
            (fun _ => (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p) x := by
    filter_upwards [hZ] with x hZx
    by_cases hT : T x < ⊤
    · rw [Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | T x < ⊤} from hT)]
      refine (nat_pow_le_tsum_block p L hp hL0 (Z x).toNat).trans (ENNReal.tsum_le_tsum fun j => ?_)
      by_cases hj : j * L < (Z x).toNat
      · have hlt : ((j * L : ℕ) : ℕ∞) < Z x := natCast_lt_of_lt_toNat _ _ hj
        have hmem : x ∈ {x : ℕ → ℤ | T x < ⊤ ∧
            ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} :=
          ⟨hT, lt_of_lt_of_le hlt (hZx hT)⟩
        rw [Set.indicator_of_mem hmem]
        simp only [hj, ↓reduceIte, le_refl]
      · simp [hj]
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℕ → ℤ | T x < ⊤} from hT)]
      exact zero_le
  have hlin : ∫⁻ x, ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => (((Z x).toNat : ℕ) : ℝ≥0∞) ^ p)) x
      ∂srwLaw m a ≤ ∑' j : ℕ, (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p * (1 / 2 : ℝ≥0∞) ^ j := by
    calc ∫⁻ x, ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => (((Z x).toNat : ℕ) : ℝ≥0∞) ^ p)) x ∂srwLaw m a
        ≤ ∫⁻ x, ∑' j : ℕ, {x : ℕ → ℤ | T x < ⊤ ∧
            ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)}.indicator
              (fun _ => (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p) x ∂srwLaw m a := lintegral_mono_ae hkey
      _ = ∑' j : ℕ, ∫⁻ x, {x : ℕ → ℤ | T x < ⊤ ∧
            ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)}.indicator
              (fun _ => (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p) x ∂srwLaw m a :=
          lintegral_tsum fun j => (measurable_const.indicator (hEm j)).aemeasurable
      _ = ∑' j : ℕ, (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p * srwLaw m a {x : ℕ → ℤ | T x < ⊤ ∧
            ((j * L : ℕ) : ℕ∞) < vExitTime G (postTimePath (fun n w => w n) T x)} :=
          tsum_congr fun j => lintegral_indicator_const (hEm j) _
      _ ≤ ∑' j : ℕ, (((j + 1) * L : ℕ) : ℝ≥0∞) ^ p * (1 / 2 : ℝ≥0∞) ^ j :=
          ENNReal.tsum_le_tsum fun j => mul_le_mul_of_nonneg_left
            (srwLaw_postTime_gt_le hTw hL j a) (by exact zero_le)
  have hfin' : ∫⁻ x, ({x : ℕ → ℤ | T x < ⊤}.indicator (fun x => (((Z x).toNat : ℕ) : ℝ≥0∞) ^ p)) x
      ∂srwLaw m a ≠ ⊤ := ne_top_of_le_ne_top hfin hlin
  have hint := integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hfin'
  refine hint.congr (ae_of_all _ fun x => ?_)
  dsimp only
  by_cases hT : T x < ⊤
  · rw [Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | T x < ⊤} from hT),
      Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | T x < ⊤} from hT),
      ENNReal.toReal_pow, ENNReal.toReal_natCast]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℕ → ℤ | T x < ⊤} from hT),
      Set.indicator_of_notMem (show x ∉ {x : ℕ → ℤ | T x < ⊤} from hT)]
    simp

end FiniteExitMomentHone68
end MatedCRT
