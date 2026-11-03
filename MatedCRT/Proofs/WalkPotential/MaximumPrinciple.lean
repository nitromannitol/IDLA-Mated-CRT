import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# The maximum principle on a finite vertex set of a multigraph

For a locally finite edge multiplicity `m : α → α → ℕ` and a finite vertex set `U` from every nonempty subset of which
an edge leaves (`hesc`; e.g. `U` finite in an infinite connected graph): a function `w` which is subharmonic on `U`
(`∑_{b ∼ a} m(a,b) (w(b) - w(a)) ≥ 0`, i.e. `Δw ≥ 0`) and nonpositive at the neighbours of `U` outside `U` is
nonpositive on `U` (`nonpos_of_lapSum_nonneg`). On `ℤ`, every finite set has this escape property as soon as
consecutive integers are adjacent (`escape_of_adjacent_succ`).
-/

namespace MatedCRT

open Set

variable {α : Type*} {m : α → α → ℕ}

/-- **Maximum principle** on a finite set with the escape property. -/
theorem nonpos_of_lapSum_nonneg (hlf : IsLocallyFiniteMult m) {U : Set α} (hU : U.Finite)
    (hesc : ∀ S ⊆ U, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0) {w : α → ℝ}
    (hsub : ∀ a ∈ U, 0 ≤ lapSum hlf w a) (hbd : ∀ a ∈ U, ∀ b, m a b ≠ 0 → b ∉ U → w b ≤ 0) :
    ∀ a ∈ U, w a ≤ 0 := by
  intro a₀ ha₀U
  by_contra ha₀
  rw [not_le] at ha₀
  obtain ⟨c, hcU, hcmax⟩ := Set.exists_max_image U w hU ⟨a₀, ha₀U⟩
  have hcpos : 0 < w c := ha₀.trans_le (hcmax a₀ ha₀U)
  obtain ⟨a, haS, b, hbS, hab⟩ := hesc {a ∈ U | w a = w c} (fun x hx => hx.1) ⟨c, hcU, rfl⟩
  have haU : a ∈ U := haS.1
  have hwa : w a = w c := haS.2
  have hterm : ∀ d ∈ nbrs hlf a, (m a d : ℝ) * (w d - w a) ≤ 0 := by
    intro d hd
    refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
    rw [hwa, sub_nonpos]
    by_cases hdU : d ∈ U
    · exact hcmax d hdU
    · exact (hbd a haU d ((mem_nbrs hlf).1 hd) hdU).trans hcpos.le
  have hsum : ∑ d ∈ nbrs hlf a, (m a d : ℝ) * (w d - w a) = 0 :=
    le_antisymm (Finset.sum_nonpos hterm) (hsub a haU)
  have hb := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum b ((mem_nbrs hlf).2 hab)
  have hmab : (m a b : ℝ) ≠ 0 := by exact_mod_cast hab
  have hwb : w b = w c := by
    have := (mul_eq_zero.1 hb).resolve_left hmab
    linarith
  have hbU : b ∈ U := by
    by_contra hbU
    have := hbd a haU b hab hbU
    linarith
  exact hbS ⟨hbU, hwb⟩

/-- A vertex with an incident edge has positive degree. -/
theorem mdeg_ne_zero_of_ne_zero (hlf : IsLocallyFiniteMult m) {a b : α} (hab : m a b ≠ 0) : mdeg m a ≠ 0 := by
  rw [mdeg_eq_sum_nbrs hlf]
  intro h
  exact hab ((Finset.sum_eq_zero_iff.1 h) b ((mem_nbrs hlf).2 hab))

/-- On `ℤ`, if consecutive integers are adjacent, an edge leaves every nonempty finite set. -/
theorem escape_of_adjacent_succ {m : ℤ → ℤ → ℕ} (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) {U : Set ℤ} (hU : U.Finite) :
    ∀ S ⊆ U, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0 := by
  intro S hSU hne
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image S id (hU.subset hSU) hne
  refine ⟨a, ha, a + 1, fun h => ?_, hsucc a⟩
  have := hmax (a + 1) h
  simp only [id] at this
  omega

end MatedCRT
