import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The Dirichlet problem on a finite vertex set and the decomposition of the proof of Lemma 3.1

Let `m` be a locally finite multigraph on `ℤ` and `A` a finite vertex set from every nonempty subset of which an edge
leaves (the escape property, `hesc`).

* `exists_lapSum_eq`: for boundary data `u` and a source `t`, there is `f = u` off `A` with
  `∑_{b ∼ a} m(a,b) (f(b) - f(a)) = t(a)` on `A`. The linear map `g ↦ lapSum g` on functions vanishing off `A` is
  injective by the maximum principle (`nonpos_of_lapSum_nonneg`), hence surjective.
* `exists_harmonic_decomposition`: the decomposition of lines 1036-1056. If `|Δu| ≤ C` on `A`, `|u| ≤ M` on the
  vertices outside `A` joined to `A`, and `w ≥ 0` vanishes off `A` with `Δw = -1` on `A` (the expected exit time),
  then the harmonic extension `f` of `u` satisfies `|f| ≤ M` on `A` and `|u - f| ≤ C w` everywhere.
-/

namespace MatedCRT.Tightness

open Set

variable {α : Type*} {m : α → α → ℕ} (hlf : IsLocallyFiniteMult m)

theorem lapSum_add' (v w : α → ℝ) (a : α) :
    lapSum hlf (fun b => v b + w b) a = lapSum hlf v a + lapSum hlf w a := by
  simp only [lapSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lapSum_smul' (c : ℝ) (v : α → ℝ) (a : α) :
    lapSum hlf (fun b => c * v b) a = c * lapSum hlf v a := by
  simp only [lapSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lapSum_sub_const (v : α → ℝ) (c : ℝ) (a : α) :
    lapSum hlf (fun b => v b - c) a = lapSum hlf v a := by
  simp only [lapSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The Dirichlet problem** on a finite set with the escape property: prescribed values `u` off `A` and
prescribed `lapSum` values `t` on `A`. -/
theorem exists_lapSum_eq {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {A : Set ℤ} (hA : A.Finite)
    (hesc : ∀ S ⊆ A, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0) (u t : ℤ → ℝ) :
    ∃ f : ℤ → ℝ, (∀ x ∉ A, f x = u x) ∧ ∀ a ∈ A, lapSum hlf f a = t a := by
  classical
  have : Fintype A := hA.fintype
  let ext0 : (A → ℝ) → ℤ → ℝ := fun g x => if h : x ∈ A then g ⟨x, h⟩ else 0
  have hext_add : ∀ g g' : A → ℝ, ext0 (g + g') = fun x => ext0 g x + ext0 g' x := by
    intro g g'
    funext x
    by_cases h : x ∈ A <;> simp [ext0, h]
  have hext_smul : ∀ (c : ℝ) (g : A → ℝ), ext0 (c • g) = fun x => c * ext0 g x := by
    intro c g
    funext x
    by_cases h : x ∈ A <;> simp [ext0, h]
  let L : (A → ℝ) →ₗ[ℝ] (A → ℝ) :=
    { toFun := fun g a => lapSum hlf (ext0 g) a
      map_add' := fun g g' => by
        funext a
        simp only [Pi.add_apply]
        rw [hext_add, lapSum_add']
      map_smul' := fun c g => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [hext_smul, lapSum_smul'] }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun g hg => ?_
    have hzero : ∀ a ∈ A, lapSum hlf (ext0 g) a = 0 := fun a ha => congrFun hg ⟨a, ha⟩
    have hoff : ∀ b ∉ A, ext0 g b = 0 := fun b hb => by simp [ext0, hb]
    have hle : ∀ a ∈ A, ext0 g a ≤ 0 :=
      nonpos_of_lapSum_nonneg hlf hA hesc (fun a ha => (hzero a ha).ge)
        fun a _ b _ hb => (hoff b hb).le
    have hge : ∀ a ∈ A, -ext0 g a ≤ 0 := by
      refine nonpos_of_lapSum_nonneg hlf hA hesc (w := fun x => -ext0 g x) (fun a ha => ?_)
        fun a _ b _ hb => by simp only [hoff b hb, neg_zero, le_refl]
      have h : lapSum hlf (fun x => -ext0 g x) a = -lapSum hlf (ext0 g) a := by
        have h' := lapSum_smul' hlf (-1) (ext0 g) a
        simp only [neg_one_mul] at h'
        exact h'
      linarith [hzero a ha]
    funext a
    have h1 := hle a a.2
    have h2 := hge a a.2
    have h3 : ext0 g a = g a := by simp [ext0]
    rw [Pi.zero_apply]
    linarith
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨ub, hub⟩ : ∃ ub : ℤ → ℝ, ub = fun x => if x ∈ A then 0 else u x := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hsurj fun a : A => t a - lapSum hlf ub a
  refine ⟨fun x => ext0 g x + ub x, fun x hx => by simp [ext0, hub, hx], fun a ha => ?_⟩
  have hsplit : lapSum hlf (fun x => ext0 g x + ub x) a = lapSum hlf (ext0 g) a + lapSum hlf ub a :=
    lapSum_add' hlf (ext0 g) ub a
  have key : lapSum hlf (ext0 g) a = t a - lapSum hlf ub a := congrFun hg ⟨a, ha⟩
  linarith

/-- **The decomposition `u = f + (u - f)`** (proof of Lemma 3.1, lines 1036-1056), on a finite set `A` with the escape
property: `f` is the harmonic extension of `u` from the complement of `A`, bounded on `A` by the bound `M` of `u` at
the neighbours of `A`; and `|u - f| ≤ C w` for any `w` vanishing off `A` with `lapSum w = -deg` on `A`, if
`|lapSum u| ≤ C deg` on `A`. -/
theorem exists_harmonic_decomposition {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {A : Set ℤ} (hA : A.Finite)
    (hesc : ∀ S ⊆ A, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0) {u w : ℤ → ℝ} {C M : ℝ}
    (hM : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∉ A → |u b| ≤ M)
    (hu : ∀ a ∈ A, |lapSum hlf u a| ≤ C * (mdeg m a : ℝ))
    (hw0 : ∀ x ∉ A, w x = 0) (hw : ∀ a ∈ A, lapSum hlf w a = -(mdeg m a : ℝ)) :
    ∃ f : ℤ → ℝ, (∀ x ∉ A, f x = u x) ∧ (∀ a ∈ A, lapSum hlf f a = 0) ∧ (∀ a ∈ A, |f a| ≤ M) ∧
      ∀ x, |u x - f x| ≤ C * w x := by
  obtain ⟨f, hfoff, hf⟩ := exists_lapSum_eq hlf hA hesc u fun _ => 0
  have hf' : ∀ a ∈ A, lapSum hlf f a = 0 := hf
  have hneg : ∀ (v : ℤ → ℝ) (a : ℤ), lapSum hlf (fun x => -v x) a = -lapSum hlf v a := fun v a => by
    have h := lapSum_smul' hlf (-1) v a
    simp only [neg_one_mul] at h
    exact h
  refine ⟨f, hfoff, hf', fun a ha => ?_, fun x => ?_⟩
  · have hup : ∀ a ∈ A, f a - M ≤ 0 := by
      refine nonpos_of_lapSum_nonneg hlf hA hesc (w := fun x => f x - M) (fun a ha => ?_) fun a ha b hab hb => ?_
      · have e1 : lapSum hlf (fun x => f x - M) a = lapSum hlf f a := lapSum_sub_const hlf f M a
        linarith [hf' a ha]
      · show f b - M ≤ 0
        rw [hfoff b hb]
        linarith [le_abs_self (u b), hM a ha b hab hb]
    have hlo : ∀ a ∈ A, -f a - M ≤ 0 := by
      refine nonpos_of_lapSum_nonneg hlf hA hesc (w := fun x => -f x - M) (fun a ha => ?_) fun a ha b hab hb => ?_
      · have e1 : lapSum hlf (fun x => -f x - M) a = lapSum hlf (fun x => -f x) a :=
          lapSum_sub_const hlf (fun x => -f x) M a
        linarith [hneg f a, hf' a ha]
      · show -f b - M ≤ 0
        rw [hfoff b hb]
        linarith [neg_abs_le (u b), hM a ha b hab hb]
    rw [abs_le]
    constructor <;> linarith [hup a ha, hlo a ha]
  · by_cases hx : x ∈ A
    · have hlap : ∀ a ∈ A, lapSum hlf (fun y => u y - f y) a = lapSum hlf u a := fun a ha => by
        have e := lapSum_sub hlf u f a
        rw [hf' a ha, sub_zero] at e
        exact e
      have hCw : ∀ a ∈ A, lapSum hlf (fun y => C * w y) a = -(C * (mdeg m a : ℝ)) := fun a ha => by
        rw [lapSum_smul' hlf C w a, hw a ha]
        ring
      have hup : ∀ a ∈ A, (u a - f a) - C * w a ≤ 0 := by
        refine nonpos_of_lapSum_nonneg hlf hA hesc (w := fun y => (u y - f y) - C * w y) (fun a ha => ?_)
          fun a _ b _ hb => ?_
        · have e1 : lapSum hlf (fun y => (u y - f y) - C * w y) a =
              lapSum hlf (fun y => u y - f y) a - lapSum hlf (fun y => C * w y) a :=
            lapSum_sub hlf (fun y => u y - f y) (fun y => C * w y) a
          linarith [hlap a ha, hCw a ha, neg_abs_le (lapSum hlf u a), hu a ha]
        · show (u b - f b) - C * w b ≤ 0
          rw [hfoff b hb, hw0 b hb]
          simp
      have hlo : ∀ a ∈ A, -(u a - f a) - C * w a ≤ 0 := by
        refine nonpos_of_lapSum_nonneg hlf hA hesc (w := fun y => -(u y - f y) - C * w y) (fun a ha => ?_)
          fun a _ b _ hb => ?_
        · have e1 : lapSum hlf (fun y => -(u y - f y) - C * w y) a =
              lapSum hlf (fun y => -(u y - f y)) a - lapSum hlf (fun y => C * w y) a :=
            lapSum_sub hlf (fun y => -(u y - f y)) (fun y => C * w y) a
          have e2 : lapSum hlf (fun y => -(u y - f y)) a = -lapSum hlf (fun y => u y - f y) a :=
            hneg (fun y => u y - f y) a
          linarith [hlap a ha, hCw a ha, le_abs_self (lapSum hlf u a), hu a ha]
        · show -(u b - f b) - C * w b ≤ 0
          rw [hfoff b hb, hw0 b hb]
          simp
      rw [abs_le]
      constructor <;> linarith [hup x hx, hlo x hx]
    · simp [hfoff x hx, hw0 x hx]

end MatedCRT.Tightness
