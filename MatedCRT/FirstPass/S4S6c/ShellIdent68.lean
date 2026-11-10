import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6r.ShellOmegaStop
import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S6r.OneTest.WalkStateFirst
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped

/-!
# Identification of the shell test end with the walk-centred test end (q2, fp-S4S6c-6-8-identification)

For the shell exit `T_k = shellExit k` and the radius `R(z_k)` at the grid centre `z_k = shellCentre k`, the shell test
end `L_k = testEnd k` of ShellOmega (notes (7.35): the first exit of the disk `B_{R/4}(η(ε X_{T_k}))` at or after `T_k`)
is the one-test test end `testEndExit` of S6r/OneTest/Concrete at the walk-centred parameter
`walkParam (R ∘ shellCentre k) T_k` (S6r/OneTest/WalkStateFirst). The identity is pointwise, proved from the characterisations
`≤ n` of both sides (`firstTime_le_iff`, `testEndExit_le_iff`) and the `ℕ∞` antisymmetry `eq_of_forall_le_natCast_iff`.

The measurability of the radius `w ↦ R (shellCentre k w)` for the σ-algebra of `T_k` is `measurable_shellRadius_stopped`
(from `measurable_shellParam_stopped_at`, S6r/Shells/ChoiceStopped).
-/

namespace MatedCRT
namespace Lemma68ShellIdent

open MeasureTheory
open MatedCRT.Lemma68Omega

/-- Two `ℕ∞` values with the same comparisons against all naturals are equal. -/
theorem eq_of_forall_le_natCast_iff {X Y : ℕ∞} (h : ∀ a : ℕ, X ≤ a ↔ Y ≤ a) : X = Y := by
  induction X using ENat.recTopCoe with
  | top =>
    refine (?_ : Y = ⊤).symm
    by_contra hY
    obtain ⟨q, rfl⟩ := ENat.ne_top_iff_exists.1 hY
    exact ENat.natCast_ne_top q (top_le_iff.1 ((h q).2 le_rfl))
  | coe p =>
    have hp : Y ≤ p := (h p).1 le_rfl
    obtain ⟨q, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top p) hp)
    have h1 : p ≤ q := ENat.natCast_le_natCast.1 ((h q).2 le_rfl)
    have h2 : q ≤ p := ENat.natCast_le_natCast.1 hp
    rw [le_antisymm h1 h2]

variable (ε : ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r s d : ℝ) (R : ℂ → ℝ)

/-- The walk-centred test parameter of the shell exit `T_k = shellExit k`: radius `R(z_k)` at the grid centre
`z_k = shellCentre k`, centre `η(ε X_{T_k})` (`walkParam`, S6r/OneTest/WalkStateFirst). -/
noncomputable def shellWalkParam (k : ℕ) : (ℕ → ℤ) → ℝ × ℂ :=
  Lemma68Window.walkParam ε η (fun w => R (shellCentre ε η K r s d k w)) (shellExit ε η K r s d R k)

/-- **Identification of the test end (notes (7.35) = the one-test exit).** For every path `x`, the shell test end
`testEnd k` equals `testEndExit` at the walk-centred parameter with `T_k = shellExit k`: both are the first time `m ≥ T_k`
with `x m` outside the discrete interior `I(B_{R(z_k)/4}(η(ε x_{T_k})))`. -/
theorem testEnd_eq_testEndExit_shell (k : ℕ) (x : ℕ → ℤ) :
    Lemma68Omega.testEnd ε η K r s d R k x =
      Lemma68Window.testEndExit ε η (shellWalkParam ε η K r s d R k) (shellExit ε η K r s d R k) x := by
  apply eq_of_forall_le_natCast_iff
  intro n
  rw [Lemma68Window.testEndExit_le_iff]
  unfold Lemma68Omega.testEnd
  rw [firstTime_le_iff]
  simp only [shellWalkParam, Lemma68Window.walkParam, Lemma68Window.ballInterior]
  constructor
  · rintro ⟨m, hm, hT, hx⟩
    have hT' : shellExit ε η K r s d R k x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hT
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hT'
    have hjm : j ≤ m := by
      have h' := hT
      rw [← hj] at h'
      exact_mod_cast h'
    refine ⟨j, le_trans hjm hm, hj.symm, m - j, by omega, ?_⟩
    rw [show j + (m - j) = m by omega]
    exact hx
  · rintro ⟨j, hjn, hT, k', hk', hx⟩
    refine ⟨j + k', by omega, ?_, hx⟩
    rw [hT]
    exact_mod_cast Nat.le_add_right j k'

/-- The shell test end as a function of the path, in the walk-centred form (`funext` of the pointwise identity). -/
theorem testEnd_fun_eq_testEndExit_shell (k : ℕ) :
    Lemma68Omega.testEnd ε η K r s d R k =
      Lemma68Window.testEndExit ε η (shellWalkParam ε η K r s d R k) (shellExit ε η K r s d R k) :=
  funext (testEnd_eq_testEndExit_shell ε η K r s d R k)

/-- The radius `w ↦ R(z_k)` of the walk-centred parameter is measurable for the σ-algebra of the shell exit `T_k`
(the first component of the shell parameter `(R z_k, z_k)`, `measurable_shellParam_stopped_at`). -/
theorem measurable_shellRadius_stopped (k : ℕ) :
    Measurable[(Lemma68OmegaStop.isStoppingTime_shellExit ε η K r s d R k).measurableSpace]
      (fun w : ℕ → ℤ => R (shellCentre ε η K r s d k w)) :=
  (Lemma68ShellParam.measurable_shellParam_stopped_at ε η K r s d R k).fst

end Lemma68ShellIdent
end MatedCRT
