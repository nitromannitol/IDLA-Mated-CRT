import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6r.OneTest.Count
import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.StrongMarkovState
import MatedCRT.Proofs.IDLA.Measurable

/-!
# The test end is finite on a finite test domain (fp-S4S6c-exit-moment, item 3)

For a walk random time `T` and a finite vertex set `G`, the post-`T` path leaves `G` almost surely on `{T < ∞}`
(strong Markov at `T` and `ExitNull68.exit_null_of_finite`). Hence the test end `firstTime (T ≤ k ∧ x k ∉ I)`,
with the test interior `I ⊆ G`, is finite almost surely on `{T < ∞}` (`testEnd_ne_top_of_finite`).
-/

namespace MatedCRT
namespace FiniteExitTestEnd68

open MeasureTheory Set Filter
open Lemma68Window
open scoped ENNReal

/-- The post-`T` path leaves a finite set `G` a.s. on `{T < ∞}`: the event `{T < ∞, all post-T points in G}` is
null (strong Markov at `T`, from every start). -/
lemma srwLaw_postTime_top_null {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T)
    {G : Set ℤ} (hG : G.Finite) (a : ℤ) :
    srwLaw m a {x : ℕ → ℤ | T x < ⊤ ∧ vExitTime G (postTimePath (fun n w => w n) T x) = ⊤} = 0 := by
  set E : Set (ℕ → ℤ) := {y : ℕ → ℤ | vExitTime G y = ⊤} with hEdef
  have hEm : MeasurableSet E := measurable_vExitTime G (measurableSet_singleton _)
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      (univ : Set (ℕ → ℤ)) ∩ {x | T x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
    intro k
    obtain ⟨F, hF, hpre⟩ := MeasurableSpace.measurableSet_comap.1 (hTw k)
    exact ⟨F, hF, by rw [univ_inter]; exact hpre.symm⟩
  have key := srwLaw_strong_markov_state m a T (fun _ => E) (fun _ => hEm) hS
  have hevent : {x : ℕ → ℤ | T x < ⊤ ∧ vExitTime G (postTimePath (fun n w => w n) T x) = ⊤} =
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
      show vExitTime G (WalkPotential.pathShift k x) = ⊤
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
  have hz : ∀ k : ℕ, ∫⁻ x in (univ ∩ {x : ℕ → ℤ | T x = (k : ℕ∞)}), srwLaw m (x k) E ∂srwLaw m a = 0 := by
    intro k
    have h0 : ∀ x : ℕ → ℤ, srwLaw m (x k) E = 0 := fun x =>
      ExitNull68.exit_null_of_finite hlf hcons hG (x k)
    simp only [h0, lintegral_zero]
  simp only [hz, tsum_zero]

/-- Almost surely on `{T < ∞}` the post-`T` path leaves the finite set `G`. -/
lemma ae_post_exit_finite {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T)
    {G : Set ℤ} (hG : G.Finite) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, T x < ⊤ → ∃ n : ℕ, x ((T x).toNat + n) ∉ G := by
  have h := srwLaw_postTime_top_null hlf hcons hTw hG a
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx hT
  by_contra hcon
  apply hx
  show T x < ⊤ ∧ vExitTime G (postTimePath (fun n w => w n) T x) = ⊤
  refine ⟨hT, ?_⟩
  rw [vExitTime_eq_top_iff]
  intro n
  by_contra hn
  exact hcon ⟨n, hn⟩

/-- **Test end is finite on a finite test domain (item (3)).** If the test interiors `I x` (for `T x < ∞`) lie in
a finite vertex set `G`, then the test end `testE x = firstTime (T x ≤ k ∧ x k ∉ I x)` is almost surely finite on
`{T < ∞}`. The exit of the post-`T` path from `G` supplies the time `k`. -/
theorem testEnd_ne_top_of_finite {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {T : (ℕ → ℤ) → ℕ∞} (hTw : S6j.IsWalkRandomTime T)
    {G : Set ℤ} (hG : G.Finite) (a : ℤ) {I : (ℕ → ℤ) → Set ℤ}
    (hIG : ∀ᵐ x ∂srwLaw m a, T x < ⊤ → I x ⊆ G)
    {testE : (ℕ → ℤ) → ℕ∞}
    (hdef : ∀ x, testE x = Lemma68Omega.firstTime (fun k => T x ≤ (k : ℕ∞) ∧ x k ∉ I x)) :
    ∀ᵐ x ∂srwLaw m a, T x < ⊤ → testE x ≠ ⊤ := by
  filter_upwards [ae_post_exit_finite hlf hcons hTw hG a, hIG] with x hpost hIx hT
  obtain ⟨n, hn⟩ := hpost hT
  rw [hdef]
  have hT1 : T x = ((T x).toNat : ℕ∞) := (ENat.natCast_toNat hT.ne).symm
  have hle : T x ≤ (((T x).toNat + n : ℕ) : ℕ∞) := by
    rw [hT1]
    exact_mod_cast Nat.le_add_right _ _
  have hP : (T x ≤ (((T x).toNat + n : ℕ) : ℕ∞)) ∧ x ((T x).toNat + n) ∉ I x :=
    ⟨hle, fun h => hn (hIx hT h)⟩
  have hfin : Lemma68Omega.firstTime (fun k => T x ≤ (k : ℕ∞) ∧ x k ∉ I x) ≤
      (((T x).toNat + n : ℕ) : ℕ∞) :=
    (Lemma68Omega.firstTime_le_iff _ _).2 ⟨(T x).toNat + n, le_rfl, hP⟩
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hfin

end FiniteExitTestEnd68
end MatedCRT
