import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S6e.Admissible

/-!
# Almost sure finiteness of the killed exit time (`KilledExitAe`)

For simple random walk on a locally finite multigraph `m` with `m k (k + 1) ≠ 0` (`ExitNull68.exit_null_of_finite`),
the killed exit time `vExitTime (killed ε η Θ F0 r) x` is finite `srwLaw m a`-almost surely, because the killed set
lies in the finite set `F0`. This is hypothesis (c) of `Lemma68ShellPathAe.shell_ineqs_ae`. The lemma is stated here
without importing WalkBridge68 (`srw_killed_top_null` there), whose `measurable_logKernel` clashes with ShellPathAe.
-/

namespace MatedCRT
namespace Lemma68KilledExitAe

open MeasureTheory

/-- The killed exit time of simple random walk is finite almost surely: `τ_U ≠ ⊤` for `srwLaw m a`-a.e. path,
the killed set `U = killed ε η Θ F0 r` being contained in the finite set `F0`
(`ExitNull68.exit_null_of_finite`, the null set `{τ_U = ⊤}`). -/
theorem ae_killed_exit_ne_top {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (r : ℝ) :
    ∀ᵐ x ∂(srwLaw m a), vExitTime (Lemma68Admissible.killed ε η Θ F0 r) x ≠ ⊤ := by
  have hfin : (Lemma68Admissible.killed ε η Θ F0 r).Finite :=
    F0.finite_toSet.subset fun _ hv => hv.1
  have h := ExitNull68.exit_null_of_finite hlf hcons hfin a
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx
  exact hx

end Lemma68KilledExitAe
end MatedCRT
