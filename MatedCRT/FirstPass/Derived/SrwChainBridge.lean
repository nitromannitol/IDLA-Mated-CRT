import MatedCRT.Defs.RandomWalk
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Chain

/-!
# Simple random walk on a multigraph as a nearest-neighbour chain

Bonanno's hitting-law API (`HarmonicInfinity.hitLaw`, `IsNNChain`) is stated for a Markov kernel
`κ` on a state space `S` with a vertex map `π : S → V`. Here `S = V = ℤ`, `π = id`, `κ = srwKernel m`:

* `chainLaw_srwKernel`: the Ionescu-Tulcea law of the chain is `srwLaw m a`;
* `srwGraph m`: the simple graph on `ℤ` joining `x ≠ y` when `m x y ≠ 0` or `m y x ≠ 0`;
* `isNNChain_srwKernel`: `srwKernel m` is a nearest-neighbour chain on `srwGraph m`;
* `hitLaw_srwKernel_step`: first-step identity of the hitting law off the target set.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity

/-- The Ionescu-Tulcea law started at a point mass is the trajectory kernel at the constant history. -/
theorem trajMeasure_dirac_eq {S : Type} [MeasurableSpace S] [MeasurableSingletonClass S]
    (κ : (n : ℕ) → Kernel ((_ : Finset.Iic n) → S) S) [∀ n, IsMarkovKernel (κ n)] (z : S) :
    Kernel.trajMeasure (X := fun _ => S) (Measure.dirac z) κ = Kernel.traj κ 0 (fun _ => z) := by
  unfold Kernel.trajMeasure
  have h2 : ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm z) = fun _ => z := by
    funext i
    simp [MeasurableEquiv.piUnique]
  rw [Measure.map_dirac (f := (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm) z,
    Measure.dirac_bind (Kernel.measurable _), h2]

/-- The chain law of `srwKernel m` started at `a` is the walk law `srwLaw m a`. -/
theorem chainLaw_srwKernel (m : ℤ → ℤ → ℕ) (a : ℤ) :
    Markov.chainLaw (srwKernel m) a = srwLaw m a := by
  unfold Markov.chainLaw srwLaw
  rw [trajMeasure_dirac_eq]
  rfl

/-- The simple graph on `ℤ` joining `x ≠ y` when the multigraph has an edge between them. -/
def srwGraph (m : ℤ → ℤ → ℕ) : SimpleGraph ℤ where
  Adj x y := x ≠ y ∧ (m x y ≠ 0 ∨ m y x ≠ 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem srwKernel_apply (m : ℤ → ℤ → ℕ) (a : ℤ) : srwKernel m a = srwStep m a := by
  rfl

/-- Simple random walk on a multigraph is a nearest-neighbour chain on `srwGraph m`. -/
theorem isNNChain_srwKernel (m : ℤ → ℤ → ℕ) :
    IsNNChain (srwKernel m) (id : ℤ → ℤ) (id : ℤ → ℤ) (srwGraph m) where
  π_start _ := rfl
  kernel_eq _ := rfl
  step_null s := by
    rw [srwKernel_apply]
    set C : Set ℤ := {t | id t = id s ∨ (srwGraph m).Adj (id s) (id t)}ᶜ with hC
    have hsC : s ∉ C := fun h => h (Or.inl rfl)
    have hCm : ∀ b ∈ C, m s b = 0 := by
      intro b hb
      by_contra hne
      exact hb (Or.inr (show s ≠ b ∧ (m s b ≠ 0 ∨ m b s ≠ 0) from ⟨fun h => hb (Or.inl h.symm), Or.inl hne⟩))
    have hE : edgeMeasure m s C = 0 := by
      unfold edgeMeasure
      rw [Measure.sum_apply _ (MeasurableSet.of_discrete)]
      refine ENNReal.tsum_eq_zero.2 fun b => ?_
      by_cases hb : b ∈ C
      · simp [hCm b hb]
      · simp [Measure.dirac_apply' _ (MeasurableSet.of_discrete), hb]
    unfold srwStep
    split_ifs with h
    · rw [ProbabilityTheory.cond_apply (MeasurableSet.of_discrete)]
      simp [hE]
    · rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
      simp [hsC]

/-- **First-step identity of the hitting law.** From a vertex `s ∉ I`, the hitting law of `I` is the
`srwStep m s`-average of the hitting law from the next vertex. -/
theorem hitLaw_srwKernel_step (m : ℤ → ℤ → ℕ) (I W : Set ℤ) {s : ℤ} (hs : s ∉ I) :
    hitLaw (srwKernel m) (id : ℤ → ℤ) I W s =
      ∫⁻ t, hitLaw (srwKernel m) (id : ℤ → ℤ) I W t ∂srwStep m s := by
  unfold hitLaw
  rw [Markov.chainLaw_apply_eq_lintegral_consPath (srwKernel m) s (measurableSet_hitEvent _ _),
    srwKernel_apply]
  refine lintegral_congr fun t => ?_
  congr 1
  ext q
  exact consPath_mem_hitEvent_iff (I := id ⁻¹' I) (Z := id ⁻¹' W) hs q

end MatedCRT
