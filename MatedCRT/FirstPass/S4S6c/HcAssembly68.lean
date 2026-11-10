import MatedCRT.FirstPass.S4S6c.ExitPath68
import MatedCRT.FirstPass.S4S6c.RandomTimeTestBound
import MatedCRT.FirstPass.S4S6c.NextExitStop
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.FirstPass.S4S6c.TestBound68
import MatedCRT.FirstPass.S4S6c.WindowStop68
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The per-test bound hc of the printed Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C4, eq (C15))

`hc_of_local`: from a vertex `y` inside the sphere window `I(B_{4R/3}(z))`, the walk started at `y` stays in `A` until
its exit from the outer window `I(B_{2R}(z))` with probability at most `c`, provided every local test (from a vertex whose
closed cell meets `∂B_{4R/3}(z)`) has stay-in probability at most `c`, and the sphere exit is a.s. finite.

Route: the random-time one-test bound `srwLaw_test_bound_random_time` applied to the legal-prefix exit time `legalExit`
(the window exit time when the walk leaves at a positive time through legal steps, and `⊤` otherwise). `legalExit` is
determined by the first `k+1` coordinates (`legalExit_eq_pathHist`), so the measurability hypothesis holds; legality of
the walk is only almost sure (`FrontierSeparation.ae_srwStep_legal`). The path-level containment is
`ExitPath68.stayIn_shift_of_outer`.
-/

open MeasureTheory Set Function Metric
open scoped ENNReal

namespace MatedCRT

open WalkPotential

namespace HcAssembly68

/-- The legal prefix of the window `V`: the walk leaves `V` at a positive time, and all its steps before that time are
legal (`x (n+1) = x n` or an edge of the multigraph `m`). -/
abbrev LegalPrefix (m : ℤ → ℤ → ℕ) (V : Set ℤ) (x : ℕ → ℤ) : Prop :=
  vExitTime V x ≠ 0 ∧ ∀ n : ℕ, (n : ℕ∞) < vExitTime V x → (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)

open Classical in
/-- Legal-prefix exit time of the window `V` (Armitage-Gardiner inner vertices): `vExitTime V` on `LegalPrefix`, `⊤`
otherwise. -/
noncomputable def legalExit (m : ℤ → ℤ → ℕ) (V : Set ℤ) (x : ℕ → ℤ) : ℕ∞ :=
  if LegalPrefix m V x then vExitTime V x else ⊤

theorem legalExit_eq_of_cond {m : ℤ → ℤ → ℕ} {V : Set ℤ} {x : ℕ → ℤ} (hcond : LegalPrefix m V x) :
    legalExit m V x = vExitTime V x := by
  unfold legalExit
  simp only [eq_true hcond, ↓reduceIte]

theorem legalExit_eq_top_of_not {m : ℤ → ℤ → ℕ} {V : Set ℤ} {x : ℕ → ℤ} (hnc : ¬ LegalPrefix m V x) :
    legalExit m V x = ⊤ := by
  unfold legalExit
  simp only [eq_false hnc, ↓reduceIte]

/-- The legal-prefix exit time is determined by the first `k+1` coordinates. -/
theorem legalExit_eq_pathHist (m : ℤ → ℤ → ℕ) (V : Set ℤ) (k : ℕ) :
    ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      {x : ℕ → ℤ | legalExit m V x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
  refine ⟨{h | k ≠ 0 ∧ (∀ i : Fin (k + 1), (i : ℕ) < k → h i ∈ V) ∧ h (Fin.last k) ∉ V ∧
      ∀ i j : Fin (k + 1), (j : ℕ) = (i : ℕ) + 1 → (h j = h i ∨ m (h i) (h j) ≠ 0)}, ?_, ?_⟩
  · exact (Set.to_countable _).measurableSet
  · ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      rw [legalExit] at hx
      split_ifs at hx with hcond
      · obtain ⟨hpre, hexit⟩ := (NextExitStop.vExitTime_eq_coe_iff V x k).mp hx
        refine ⟨?_, fun i hi => hpre i hi, hexit, ?_⟩
        · rintro rfl
          exact hcond.1 (by simp [hx])
        · intro i j hj
          have hik : (i : ℕ) < k := by omega
          have hlt : (i : ℕ∞) < vExitTime V x := by
            rw [hx]
            exact_mod_cast hik
          have hl := hcond.2 (i : ℕ) hlt
          show x (j : ℕ) = x (i : ℕ) ∨ m (x (i : ℕ)) (x (j : ℕ)) ≠ 0
          rw [hj]
          exact hl
      · exact absurd hx (ENat.top_ne_natCast k)
    · rintro ⟨hk0, hVin, hlast, hleg⟩
      have hpre : ∀ i < k, x i ∈ V := fun i hi => hVin ⟨i, by omega⟩ hi
      have hexit : x k ∉ V := hlast
      have hvE : vExitTime V x = (k : ℕ∞) := (NextExitStop.vExitTime_eq_coe_iff V x k).mpr ⟨hpre, hexit⟩
      have hcond : LegalPrefix m V x := by
        refine ⟨?_, ?_⟩
        · rw [hvE]
          intro h0
          exact hk0 (by exact_mod_cast h0)
        · intro n hn
          rw [hvE] at hn
          have hnk : n < k := by exact_mod_cast hn
          exact hleg ⟨n, by omega⟩ ⟨n + 1, by omega⟩ rfl
      rw [legalExit_eq_of_cond hcond]
      exact hvE

/-- **Sphere exit cell, legal-prefix form.** On `{legalExit = k}` with `k ≠ 0`, the exit cell `x k` has closure meeting
the sphere `∂B_ρ(c)`. -/
theorem legalExit_exit_closure_meets_sphere {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {c : ℂ} {ρ : ℝ}
    (hconn : ∀ v, IsPreconnected (H v))
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    {x : ℕ → ℤ} {k : ℕ} (hk : legalExit m (innerVertices H (ball c ρ)) x = (k : ℕ∞)) (hk0 : k ≠ 0) :
    (closure (H (x k)) ∩ Metric.sphere c ρ).Nonempty := by
  by_cases hcond : LegalPrefix m (innerVertices H (ball c ρ)) x
  · rw [legalExit_eq_of_cond hcond] at hk
    obtain ⟨hpre, hexit⟩ := (NextExitStop.vExitTime_eq_coe_iff _ x k).mp hk
    obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
    have hlt : ((k₀ : ℕ) : ℕ∞) < vExitTime (innerVertices H (ball c ρ)) x := by
      rw [hk]
      exact_mod_cast Nat.lt_succ_self k₀
    have hmk : m (x k₀) (x (k₀ + 1)) ≠ 0 := by
      rcases hcond.2 k₀ hlt with h | h
      · exact absurd (by rw [h]; exact hpre k₀ (Nat.lt_succ_self k₀)) hexit
      · exact h
    exact ExitPath68.exit_closure_meets_sphere hconn hadj (hpre k₀ (Nat.lt_succ_self k₀)) hmk hexit
  · rw [legalExit_eq_top_of_not hcond] at hk
    exact absurd hk (ENat.top_ne_natCast k)

/-- **Per-test bound hc (LEMMA68 (C15), one centre).** From a vertex `y` of the sphere window `I(B_{4R/3}(z))`, the walk
stays in `A` until its exit from `I(B_{2R}(z))` with probability at most `c`, provided: the sphere exit is a.s. finite
(`hfin`), and every local test from a vertex whose closed cell meets `∂B_{4R/3}(z)` has stay-in probability at most `c`
(`hloc`). -/
theorem hc_of_local {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {d R ρ : ℝ} {z : ℂ} {P : ℤ → ℂ} {y : ℤ}
    {c : ℝ≥0∞}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hd : 0 ≤ d)
    (hsm : ∀ v, (closure (H v) ∩ closedBall z (2 * R)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y' ∈ closure (H v), dist x y' ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPb : ∀ b, P b ∈ H b) (hgeo : 4 * R / 3 + d + ρ + d < 2 * R) (hρ : d < ρ)
    (hy : y ∈ innerVertices H (ball z (4 * R / 3)))
    (hfin : ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices H (ball z (4 * R / 3))) x ≠ ⊤)
    (hloc : ∀ b ∈ {b : ℤ | (closure (H b) ∩ Metric.sphere z (4 * R / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A b) ≤ c) :
    srwLaw m y (TestBound68.stayIn (fun _ => innerVertices H (ball z (2 * R))) A y) ≤ c := by
  classical
  set V : Set ℤ := innerVertices H (ball z (4 * R / 3)) with hV
  set Wout : Set ℤ := innerVertices H (ball z (2 * R)) with hWout
  set Ysph : Set ℤ := {b : ℤ | (closure (H b) ∩ Metric.sphere z (4 * R / 3)).Nonempty} with hYsph
  have hG : ∀ b, MeasurableSet (TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A b) :=
    fun b => SuccessiveExitStop.measurableSet_stayInRegionOf
      (fun b => innerVertices H (ball (P b) ρ)) (fun _ => A) b
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      (univ : Set (ℕ → ℤ)) ∩ {x | legalExit m V x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
    intro k
    obtain ⟨F, hF, hEq⟩ := legalExit_eq_pathHist m V k
    exact ⟨F, hF, by rw [univ_inter, hEq]⟩
  have hSY : ∀ x ∈ (univ : Set (ℕ → ℤ)), ∀ k : ℕ, legalExit m V x = (k : ℕ∞) → x k ∈ Ysph := by
    intro x _ k hk
    by_cases hk0 : k = 0
    · exfalso
      subst hk0
      by_cases hcond : LegalPrefix m V x
      · rw [legalExit_eq_of_cond hcond] at hk
        exact hcond.1 (by simp [hk])
      · rw [legalExit_eq_top_of_not hcond] at hk
        exact ENat.top_ne_natCast 0 hk
    · exact legalExit_exit_closure_meets_sphere (c := z) (ρ := 4 * R / 3) hconn hadj hk hk0
  have hrand := srwLaw_test_bound_random_time m y (legalExit m V)
    (fun b => TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A b) hG (S := univ) hS
    (Y := Ysph) (c := c) hloc hSY
  simp only [univ_inter] at hrand
  -- the stay-in event lies in the shifted-test event plus the event `{legalExit = ⊤}`
  have hsub : {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime Wout x → x n ∈ A} ⊆
      {x | ∃ k : ℕ, legalExit m V x = (k : ℕ∞) ∧
          WalkPotential.pathShift k x ∈ TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A (x k)} ∪
        {x | legalExit m V x = ⊤} := by
    intro x hx
    by_cases htop : legalExit m V x = ⊤
    · exact Or.inr htop
    · left
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
      refine ⟨k, hk.symm, ?_⟩
      have hcond : LegalPrefix m V x := by
        by_contra hnc
        exact htop (legalExit_eq_top_of_not hnc)
      have hvE : vExitTime V x = (k : ℕ∞) := by
        rw [← legalExit_eq_of_cond hcond]
        exact hk.symm
      have hk0 : k ≠ 0 := fun h0 => hcond.1 (by simp [hvE, h0])
      obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
      have hlt : ((k₀ : ℕ) : ℕ∞) < vExitTime V x := by
        rw [hvE]
        exact_mod_cast Nat.lt_succ_self k₀
      have hleg := hcond.2 k₀ hlt
      exact ExitPath68.stayIn_shift_of_outer hconn hne hd hsm hadj hPb hgeo hρ hleg hvE hx
  -- almost surely: start at `y`, finite sphere exit, legal steps
  have hgood : ∀ᵐ x ∂srwLaw m y, x 0 = y ∧ vExitTime V x ≠ ⊤ ∧
      ∀ n : ℕ, (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) :=
    (srwLaw_ae_start m y).and (hfin.and (FrontierSeparation.ae_srwStep_legal m y))
  have htop0 : srwLaw m y {x | legalExit m V x = ⊤} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hgood)
    intro x hxtop hgx
    have hxtop' : legalExit m V x = ⊤ := hxtop
    have h0 : (0 : ℕ∞) < vExitTime V x :=
      WindowStop68.lt_vExitTime_of_forall (V := V) (w := x) (M := 0)
        (fun n hn => by rw [Nat.le_zero.mp hn, hgx.1]; exact hy)
    have hcond : LegalPrefix m V x := ⟨h0.ne', fun n _ => hgx.2.2 n⟩
    rw [legalExit_eq_of_cond hcond] at hxtop'
    exact hgx.2.1 hxtop'
  have hpart : srwLaw m y {x | ∃ k : ℕ, legalExit m V x = (k : ℕ∞) ∧
      WalkPotential.pathShift k x ∈ TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A (x k)} ≤ c :=
    le_trans hrand (mul_le_of_le_one_right (zero_le) prob_le_one)
  calc srwLaw m y (TestBound68.stayIn (fun _ => Wout) A y)
      ≤ srwLaw m y ({x | ∃ k : ℕ, legalExit m V x = (k : ℕ∞) ∧
          WalkPotential.pathShift k x ∈ TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A (x k)} ∪
        {x | legalExit m V x = ⊤}) := measure_mono hsub
    _ ≤ srwLaw m y {x | ∃ k : ℕ, legalExit m V x = (k : ℕ∞) ∧
          WalkPotential.pathShift k x ∈ TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A (x k)} +
        srwLaw m y {x | legalExit m V x = ⊤} := measure_union_le _ _
    _ ≤ c + 0 := by rw [htop0]; exact add_le_add hpart le_rfl
    _ = c := add_zero c

/-- **Start cell inside the sphere window (LEMMA68 C3, `H_{X_{T_j}} ⊂ B_{g+d}(z_j) ⊂ B_{4R/3}(z_j)`).** If the cell of
`y` has diameter at most `d` and contains a point `p` within `g` of the centre `c`, and `d + g < R'`, then `y` lies in the
inner window `I(B_{R'}(c))`. Discharges the start hypothesis `hy` of `hc_of_local`. -/
theorem start_mem_sphere_window {H : ℤ → Set ℂ} {d g R' : ℝ} {c p : ℂ} {y : ℤ}
    (hne : (H y).Nonempty) (hsm : ∀ x ∈ closure (H y), ∀ x' ∈ closure (H y), dist x x' ≤ d)
    (hp : p ∈ H y) (hpc : dist p c ≤ g) (hlt : d + g < R') :
    y ∈ innerVertices H (ball c R') := by
  refine ExitPath68.inner_of_near (ρ := d + g) hne (fun x hx => ?_) hlt
  have h1 := hsm x (subset_closure hx) p (subset_closure hp)
  have h2 := dist_triangle x p c
  linarith

end HcAssembly68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.HcAssembly68.hc_of_local
