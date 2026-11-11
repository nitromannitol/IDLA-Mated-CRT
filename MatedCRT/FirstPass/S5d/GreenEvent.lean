import MatedCRT.FirstPass.S5d.StoppedComparison
import MatedCRT.Proofs.Sec5.StoppedPoleFiniteComparison
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The Green event of the stopped clause, pathwise

Deterministic content of the Green event of Lemma 5.2 (`GeneralIDLALowerBoundRelaxedStep`,
Steps/Sec5/IDLALowerBound.lean:40) for a finite killing set `I ⊆ ℤ` (referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md
§5.2–5.3). With `g_I = G_I / deg` (Armitage-Gardiner Green kernel), `q_I(a) = ∑_{b∈I} g_I(a,b)` and `κ = t/ε`:
* first Green inequality (5.5): `(1+s) q_I(a) ≤ κ g_I(a,0)`;
* second Green inequality (5.7): `e ≤ q_I(a) / g_I(a,a)`.
Both are converted to the form in which the relaxed step states them, using reversibility `G_I(b,a) = deg(a) g_I(a,b)`
(`greenKernel_symm_pole`), so that the factors `deg(a)` cancel.
-/

namespace MatedCRT

open Set

/-- A sum over the subtype of a finite set is the finite sum. -/
theorem tsum_subtype_eq_sum_finite {A : Set ℤ} (hA : A.Finite) (f : ℤ → ℝ) :
    ∑' b : A, f b = ∑ b ∈ hA.toFinset, f b := by
  rw [tsum_subtype A f, tsum_eq_sum (s := hA.toFinset)]
  · exact Finset.sum_congr rfl fun b hb => Set.indicator_of_mem (hA.mem_toFinset.1 hb) f
  · intro b hb
    rw [hA.mem_toFinset] at hb
    exact Set.indicator_of_notMem hb f

/-- `G_A(a,b) = deg(b) g_A(a,b)` (definition of the Green kernel `g_A = G_A / deg`). -/
theorem greenFn_eq_mdeg_mul_greenKernel (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) (hb : mdeg m b ≠ 0) :
    greenFn m A a b = (mdeg m b : ℝ) * greenKernel m A a b := by
  have h : (mdeg m b : ℝ) ≠ 0 := by exact_mod_cast hb
  unfold greenKernel
  field_simp

/-- The reversed Green sum over a finite killing set: `∑_{b∈I} G_I(b,a) = deg(a) ∑_{b∈I} g_I(a,b)`. -/
theorem tsum_greenFn_eq_mdeg_mul {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) {a : ℤ} :
    ∑' b : I, greenFn m I b a = (mdeg m a : ℝ) * ∑ b ∈ hI.toFinset, greenKernel m I a b := by
  have hd : mdeg m a ≠ 0 := mdeg_ne_zero_of_ne_zero hlf (hcons a)
  rw [tsum_subtype_eq_sum_finite hI (fun b => greenFn m I b a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [greenFn_eq_mdeg_mul_greenKernel m I b a hd, greenKernel_symm_pole hsymm hlf hcons hI b a]

/-- **First Green inequality, relaxed form** (referee §5.2 (5.5); the first conjunct of the relaxed Step's Green event):
if `(1+s) q_I(a) ≤ κ g_I(a,0)` then `(1+s) ∑_{b∈I} G_I(b,a) ≤ κ G_I(0,a)`. -/
theorem firstGreen_relaxed {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) {a : ℤ} {κ s : ℝ}
    (h5 : (1 + s) * ∑ b ∈ hI.toFinset, greenKernel m I a b ≤ κ * greenKernel m I a 0) :
    (1 + s) * ∑' b : I, greenFn m I b a ≤ κ * greenFn m I 0 a := by
  have hd : mdeg m a ≠ 0 := mdeg_ne_zero_of_ne_zero hlf (hcons a)
  have hdpos : (0 : ℝ) ≤ (mdeg m a : ℝ) := Nat.cast_nonneg _
  rw [tsum_greenFn_eq_mdeg_mul hsymm hlf hcons hI, greenFn_eq_mdeg_mul_greenKernel m I 0 a hd,
    greenKernel_symm_pole hsymm hlf hcons hI 0 a]
  calc (1 + s) * ((mdeg m a : ℝ) * ∑ b ∈ hI.toFinset, greenKernel m I a b)
      = (mdeg m a : ℝ) * ((1 + s) * ∑ b ∈ hI.toFinset, greenKernel m I a b) := by ring
    _ ≤ (mdeg m a : ℝ) * (κ * greenKernel m I a 0) := mul_le_mul_of_nonneg_left h5 hdpos
    _ = κ * ((mdeg m a : ℝ) * greenKernel m I a 0) := by ring

/-- **Second Green inequality, relaxed form** (referee §5.3 (5.7); the second conjunct of the relaxed Step's Green event):
`e ≤ q_I(a)/g_I(a,a)` gives `e ≤ ∑_{b∈I} G_I(b,a) / G_I(a,a)`. -/
theorem secondGreen_relaxed {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) {a : ℤ} {e : ℝ}
    (h7 : e ≤ (∑ b ∈ hI.toFinset, greenKernel m I a b) / greenKernel m I a a) :
    e ≤ (∑' b : I, greenFn m I b a) / greenFn m I a a := by
  have hd : mdeg m a ≠ 0 := mdeg_ne_zero_of_ne_zero hlf (hcons a)
  have hd' : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [tsum_greenFn_eq_mdeg_mul hsymm hlf hcons hI, greenFn_eq_mdeg_mul_greenKernel m I a a hd,
    mul_div_mul_left _ _ hd']
  exact h7

/-- **Pathwise first Green inequality** (referee §5.2, (5.3)–(5.5)): for a surplus `v` with the Laplacian identity
`Δ v = 1/deg - κ 1_{a=0}/deg(0)` on the finite killing set `I`, `v ≤ M` off `I`, `M ≤ c/(2ε)`, and on the targets
`Z ⊆ I`: the surplus lower bound `v ≥ c/ε` on `Z` and the exit-time bound `q_I ≤ C/ε` on `Z` give
`(1 + c/(2C)) q_I(a) ≤ κ g_I(a,0)` for `a ∈ Z`. Deterministic; no connectedness of `I` is needed. -/
theorem firstGreen_pathwise {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {I : Set ℤ} (hI : I.Finite) {κ ε c C M : ℝ} {v : ℤ → ℝ} {Z : Set ℤ} (hε : 0 < ε) (hC : 0 < C) (hc : 0 ≤ c)
    (hv : ∀ a ∈ I, mLaplacian m v a = (mdeg m a : ℝ)⁻¹ - κ * (if a = 0 then (mdeg m 0 : ℝ)⁻¹ else 0))
    (hvM : ∀ b ∉ I, v b ≤ M) (hM : M ≤ c / (2 * ε)) (hZ : Z ⊆ I) (hlow : ∀ a ∈ Z, c / ε ≤ v a)
    (hq : ∀ a ∈ Z, ∑ b ∈ hI.toFinset, greenKernel m I a b ≤ C / ε) :
    ∀ a ∈ Z, (1 + c / (2 * C)) * ∑ b ∈ hI.toFinset, greenKernel m I a b ≤ κ * greenKernel m I a 0 := by
  intro a ha
  have h1 := surplus_sub_le_greenComb hlf hcons hI κ hv hvM a (hZ ha)
  have e1 : c / ε = 2 * (c / (2 * ε)) := by field_simp
  exact firstGreen_of_surplus_bound hε hC hc (hq a ha) (by linarith [hlow a ha, hM, h1])

end MatedCRT
