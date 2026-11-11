import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.WalkPotential.Comparison
import MatedCRT.Proofs.Sec5.MeanValueInequality.Reversibility
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Finite-domain comparison at the source pole

Finite-domain lemmas behind the source-pole step. They are not the pole target
`StoppedInterior.StoppedSurplusPoleStep`, and no numbered result is claimed here.

Setting: an edge multiplicity `m : ℤ → ℤ → ℕ`, symmetric (undirected), locally finite
(`IsLocallyFiniteMult m`), with consecutive adjacency `m k (k + 1) ≠ 0` (consecutive cells
share an endpoint). The consecutive adjacency is the connectedness input of the simple random walk on `ℤ`, as in
`WalkPotential.GreenFirstStep`; it gives the escape property of finite sets (`escape_of_adjacent_succ`). The killed
domain `A` is finite (the finite killed domain); from this the killed Green kernels are finite
(inside `WalkPotential.mLaplacian_greenFn`), so finiteness of the kernels is not a separate hypothesis.

Notation (Armitage-Gardiner, Lawler-Limic): `greenKernel m S a b = g_S(a,b) = G_S(a,b)/deg(b)` is the
degree-normalized killed Green kernel of `S`, `mLaplacian m u a` is the degree-normalized Laplacian
`Δ_m u(a)`, and `poleQ m D a = q_D(a) = ∑_{b ∈ D} g_D(a,b)`.

Results:
* `lapSum_greenKernel_point`: `Δ_m g_S(·,b)(a) = -δ_{ab}/deg(b)` for `a ∈ S`, `S` finite
  (first-step identity `mLaplacian_greenFn`).
* `greenKernel_symm_pole`: `g_S(a,b) = g_S(b,a)` for finite `S` (the paper reverses finite walk paths; the Lean
  route is the discrete Green identity, `greenKernel_symm_of_firstStep`).
* `lapSum_poleQ`: `Δ_m q_D(a) = -1` in the `lapSum` normalization, i.e. `Δ_m q_D(a) = -1/deg(a)`, for `a ∈ D`.
* `poleComparison`: if `V = w + (t/ε) g_A(0,·)` with `Δ_m w ≤ 1/deg` on `D` and `V ≥ L` on the
  exterior vertex boundary of `D`, then `V(a) ≥ L - q_D(a)` for every `a ∈ D`, including `a = 0`.
* `sourceCapacity_pointwise`, `greenKernel_le_source_pole`, `poleQ_zero_le`, `sourceCapacity_inf`
  for the real infimum over admissible supersolutions,
  `ε · V_t^ε(0) ≥ (t - ε #D) g_D(0,0)`, with the infimum nonempty and bounded below.
-/

namespace MatedCRT

open Set Finset

/-! ### Linear algebra of the discrete Laplacian `lapSum` -/

theorem lapSum_add_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (u v : ℤ → ℝ) (a : ℤ) :
    lapSum hlf (fun x => u x + v x) a = lapSum hlf u a + lapSum hlf v a := by
  simp only [lapSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem lapSum_neg_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (F : ℤ → ℝ) (a : ℤ) :
    lapSum hlf (fun x => -F x) a = -lapSum hlf F a := by
  unfold lapSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem lapSum_const_sub_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (L : ℝ) (F : ℤ → ℝ) (a : ℤ) :
    lapSum hlf (fun x => L - F x) a = -lapSum hlf F a := by
  unfold lapSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem lapSum_sub_const_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (F : ℤ → ℝ) (c : ℝ) (a : ℤ) :
    lapSum hlf (fun x => F x - c) a = lapSum hlf F a := by
  unfold lapSum
  exact Finset.sum_congr rfl fun b _ => by ring

theorem lapSum_finset_sum_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ℤ → ℝ) (a : ℤ) :
    lapSum hlf (fun x => ∑ i ∈ s, f i x) a = ∑ i ∈ s, lapSum hlf (f i) a := by
  induction s using Finset.induction_on with
  | empty => simp [lapSum]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [lapSum_add_pole hlf, ih]

/-! ### Degree and Green kernel facts -/

theorem mdeg_cast_ne_zero_pole {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) : (mdeg m a : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 (mdeg_ne_zero_of_ne_zero hlf (hcons a))

theorem greenKernel_nonneg_pole (m : ℤ → ℤ → ℕ) (S : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m S a b := by
  unfold greenKernel greenFn
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- Symmetry of the normalized killed Green kernel on a finite set (reversal of finite walk paths). -/
theorem greenKernel_symm_pole {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (a b : ℤ) :
    greenKernel m S a b = greenKernel m S b a :=
  greenKernel_symm_of_firstStep hsymm hlf hS (fun x => mdeg_ne_zero_of_ne_zero hlf (hcons x))
    (WalkPotential.mLaplacian_greenFn hlf hcons hS) a b

/-- **First-step identity in the second variable**: `Δ_m g_S(·,b)(a) = -δ_{ab}/deg(b)` for `a ∈ S`. -/
theorem lapSum_greenKernel_point {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (b : ℤ) {a : ℤ} (ha : a ∈ S) :
    lapSum hlf (fun x => greenKernel m S x b) a =
      (mdeg m a : ℝ) * (-(if a = b then 1 else 0)) / (mdeg m b : ℝ) := by
  have hL := WalkPotential.mLaplacian_greenFn hlf hcons hS b a ha
  have hfun : (fun x => greenKernel m S x b) = fun x => (mdeg m b : ℝ)⁻¹ * greenFn m S x b := by
    funext x
    simp only [greenKernel, div_eq_inv_mul]
  rw [hfun, lapSum_const_mul hlf, ← mLaplacian_mul_mdeg hlf, hL]
  ring

/-- The source Green kernel `g_S(0,·)` has `Δ_m g_S(0,·)(a) = -δ_{a0}/deg(0)` on `S`, by symmetry. -/
theorem lapSum_greenKernel_source_pole {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) {a : ℤ}
    (ha : a ∈ S) :
    lapSum hlf (fun x => greenKernel m S 0 x) a =
      (mdeg m a : ℝ) * (-(if a = 0 then 1 else 0)) / (mdeg m 0 : ℝ) := by
  have hfun : (fun x => greenKernel m S 0 x) = fun x => greenKernel m S x 0 :=
    funext fun x => greenKernel_symm_pole hsymm hlf hcons hS 0 x
  rw [hfun]
  exact lapSum_greenKernel_point hlf hcons hS 0 ha

/-! ### The killed potential `q_D` -/

/-- The killed potential `q_D(a) = ∑_{b ∈ D} g_D(a, b)` of the finite set `D`. -/
noncomputable def poleQ (m : ℤ → ℤ → ℕ) (D : Finset ℤ) (a : ℤ) : ℝ :=
  ∑ b ∈ D, greenKernel m (D : Set ℤ) a b

/-- `Δ_m q_D(a) = -1/deg(a)` for `a ∈ D`, in the `lapSum` normalization `-1`. -/
theorem lapSum_poleQ {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {D : Finset ℤ} {a : ℤ} (ha : a ∈ D) :
    lapSum hlf (poleQ m D) a = -1 := by
  have hfun : poleQ m D = fun x => ∑ b ∈ D, greenKernel m (D : Set ℤ) x b := rfl
  rw [hfun, lapSum_finset_sum_pole hlf]
  rw [Finset.sum_congr rfl fun b _ =>
    lapSum_greenKernel_point hlf hcons D.finite_toSet b (Finset.mem_coe.2 ha)]
  rw [Finset.sum_eq_single a (fun b _ hba => by simp [Ne.symm hba]) (fun h => absurd ha h)]
  have hd := mdeg_cast_ne_zero_pole hlf hcons a
  simp [hd]

/-! ### The comparison -/

/-- **Finite-domain comparison**. If `V = w + (t/ε) g_A(0,·)` with
`Δ_m w ≤ 1/deg` on the finite set `D ⊆ A`, and `V ≥ L` on the exterior vertex boundary of `D`, then
`V(a) ≥ L - q_D(a)` for all `a ∈ D`, including the source vertex `a = 0`. -/
theorem poleComparison {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) {D : Finset ℤ}
    (hDA : (D : Set ℤ) ⊆ A) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) {w : ℤ → ℝ}
    (hw : ∀ a ∈ D, mLaplacian m w a ≤ (mdeg m a : ℝ)⁻¹) {L : ℝ}
    (hbd : ∀ b ∈ vBoundary m (D : Set ℤ), L ≤ w b + t / ε * greenKernel m A 0 b) :
    ∀ a ∈ D, L - poleQ m D a ≤ w a + t / ε * greenKernel m A 0 a := by
  have hc : 0 ≤ t / ε := div_nonneg ht hε.le
  -- superharmonicity of `V + q_D` on `D`
  have hsup : ∀ a ∈ D, lapSum hlf (fun x => w x + t / ε * greenKernel m A 0 x + poleQ m D x) a ≤ 0 := by
    intro a ha
    have hd := mdeg_cast_ne_zero_pole hlf hcons a
    have h1 : lapSum hlf w a ≤ 1 := by
      have h := lapSum_le_of_mLaplacian_le hlf (hw a ha)
      rwa [inv_mul_cancel₀ hd] at h
    have h2 : lapSum hlf (fun x => greenKernel m A 0 x) a ≤ 0 := by
      rw [lapSum_greenKernel_source_pole hsymm hlf hcons hA (hDA (Finset.mem_coe.2 ha))]
      refine div_nonpos_of_nonpos_of_nonneg ?_ (Nat.cast_nonneg _)
      split_ifs <;> simp
    have h3 : t / ε * lapSum hlf (fun x => greenKernel m A 0 x) a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc h2
    have h4 := lapSum_poleQ hlf hcons ha
    rw [lapSum_add_pole hlf, lapSum_add_pole hlf, lapSum_const_mul hlf]
    linarith
  have hsub : ∀ a ∈ (D : Set ℤ),
      0 ≤ lapSum hlf (fun x => L - (w x + t / ε * greenKernel m A 0 x + poleQ m D x)) a := by
    intro a ha
    rw [lapSum_const_sub_pole hlf]
    have h := hsup a (Finset.mem_coe.1 ha)
    linarith
  have hbd' : ∀ a ∈ (D : Set ℤ), ∀ b, m a b ≠ 0 → b ∉ (D : Set ℤ) →
      L - (w b + t / ε * greenKernel m A 0 b + poleQ m D b) ≤ 0 := by
    intro a ha b hab hbD
    have hb : b ∈ vBoundary m (D : Set ℤ) := ⟨hbD, a, ha, hab⟩
    have hq : poleQ m D b = 0 := by
      unfold poleQ
      exact Finset.sum_eq_zero fun x _ => greenKernel_eq_zero_of_not_mem m hbD x
    rw [hq, add_zero]
    linarith [hbd b hb]
  have key := nonpos_of_lapSum_nonneg hlf D.finite_toSet
    (escape_of_adjacent_succ hcons D.finite_toSet) hsub hbd'
  intro a ha
  have h : L - (w a + t / ε * greenKernel m A 0 a + poleQ m D a) ≤ 0 :=
    key a (Finset.mem_coe.2 ha)
  linarith

/-- The "in particular" consequence of the comparison: a boundary bound `V ≥ 2c/ε` and a
bound `sup_D q_D ≤ c/ε` give `V ≥ c/ε` throughout `D`, including at the source vertex `0 ∈ D`. -/
theorem poleComparison_lower_bound {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) {D : Finset ℤ}
    (hDA : (D : Set ℤ) ⊆ A) {t ε c : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) {w : ℤ → ℝ}
    (hw : ∀ a ∈ D, mLaplacian m w a ≤ (mdeg m a : ℝ)⁻¹)
    (hbd : ∀ b ∈ vBoundary m (D : Set ℤ), 2 * c / ε ≤ w b + t / ε * greenKernel m A 0 b)
    (hq : ∀ a ∈ D, poleQ m D a ≤ c / ε) :
    ∀ a ∈ D, c / ε ≤ w a + t / ε * greenKernel m A 0 a := by
  intro a ha
  have h := poleComparison hsymm hlf hcons hA hDA ht hε hw hbd a ha
  have h2 : 2 * c / ε = 2 * (c / ε) := by ring
  linarith [hq a ha, h2]

/-! ### The source capacity bound -/

/-- `g_D(0,b) ≤ g_D(0,0)` for `b ∈ D`: the killed kernel from `0` is maximal at the source. -/
theorem greenKernel_le_source_pole {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {D : Finset ℤ} {b : ℤ} (hb : b ∈ D) :
    greenKernel m (D : Set ℤ) 0 b ≤ greenKernel m (D : Set ℤ) 0 0 := by
  rw [greenKernel_symm_pole hsymm hlf hcons D.finite_toSet 0 b]
  have hUfin : ((D.erase 0 : Finset ℤ) : Set ℤ).Finite := (D.erase 0).finite_toSet
  have hsub : ∀ a ∈ ((D.erase 0 : Finset ℤ) : Set ℤ),
      0 ≤ lapSum hlf (fun x => greenKernel m (D : Set ℤ) x 0 - greenKernel m (D : Set ℤ) 0 0) a := by
    intro a ha
    have ha' := Finset.mem_erase.1 (Finset.mem_coe.1 ha)
    rw [lapSum_sub_const_pole hlf, lapSum_greenKernel_point hlf hcons D.finite_toSet 0
      (Finset.mem_coe.2 ha'.2)]
    simp [ha'.1]
  have hbd : ∀ a ∈ ((D.erase 0 : Finset ℤ) : Set ℤ), ∀ c, m a c ≠ 0 →
      c ∉ ((D.erase 0 : Finset ℤ) : Set ℤ) →
      greenKernel m (D : Set ℤ) c 0 - greenKernel m (D : Set ℤ) 0 0 ≤ 0 := by
    intro a _ c _ hcU
    by_cases hc0 : c = 0
    · subst hc0
      simp
    · have hcD : c ∉ (D : Set ℤ) := fun h =>
        hcU (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hc0, Finset.mem_coe.1 h⟩))
      rw [greenKernel_eq_zero_of_not_mem m hcD 0]
      linarith [greenKernel_nonneg_pole m (D : Set ℤ) 0 0]
  have key := nonpos_of_lapSum_nonneg hlf hUfin (escape_of_adjacent_succ hcons hUfin) hsub hbd
  by_cases hb0 : b = 0
  · subst hb0
    exact le_rfl
  · have hbU : b ∈ ((D.erase 0 : Finset ℤ) : Set ℤ) :=
      Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hb0, hb⟩)
    have h : greenKernel m (D : Set ℤ) b 0 - greenKernel m (D : Set ℤ) 0 0 ≤ 0 := key b hbU
    linarith

/-- `q_D(0) ≤ #D · g_D(0,0)`. -/
theorem poleQ_zero_le {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (D : Finset ℤ) :
    poleQ m D 0 ≤ (D.card : ℝ) * greenKernel m (D : Set ℤ) 0 0 := by
  unfold poleQ
  calc ∑ b ∈ D, greenKernel m (D : Set ℤ) 0 b
      ≤ ∑ _b ∈ D, greenKernel m (D : Set ℤ) 0 0 :=
        Finset.sum_le_sum fun b hb => greenKernel_le_source_pole hsymm hlf hcons hb
    _ = (D.card : ℝ) * greenKernel m (D : Set ℤ) 0 0 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Pointwise source-capacity comparison**: for every admissible `w`,
`w(a) + (t/ε) g_A(0,a) ≥ (t/ε) g_D(0,a) - q_D(a)` for all `a ∈ D`. -/
theorem sourceCapacity_pointwise {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite)
    {D : Finset ℤ} (hDA : (D : Set ℤ) ⊆ A) {W : Set ℤ} (hW : vBoundary m (D : Set ℤ) ⊆ W) {t ε : ℝ}
    (ht : 0 ≤ t) (hε : 0 < ε) {w : ℤ → ℝ} (hw : ∀ a ∈ D, mLaplacian m w a ≤ (mdeg m a : ℝ)⁻¹)
    (hobs : ∀ b ∈ W, -(t / ε * greenKernel m A 0 b) ≤ w b) :
    ∀ a ∈ D, t / ε * greenKernel m (D : Set ℤ) 0 a - poleQ m D a ≤
      w a + t / ε * greenKernel m A 0 a := by
  have hc : 0 ≤ t / ε := div_nonneg ht hε.le
  have hDfin : (D : Set ℤ).Finite := D.finite_toSet
  have hsub : ∀ a ∈ (D : Set ℤ), 0 ≤ lapSum hlf (fun x => -(w x + t / ε * greenKernel m A 0 x
      - t / ε * greenKernel m (D : Set ℤ) 0 x + poleQ m D x)) a := by
    intro a ha
    rw [lapSum_neg_pole hlf]
    have h1 : lapSum hlf w a ≤ 1 := by
      have h := lapSum_le_of_mLaplacian_le hlf (hw a (Finset.mem_coe.1 ha))
      rwa [inv_mul_cancel₀ (mdeg_cast_ne_zero_pole hlf hcons a)] at h
    have hgA := lapSum_greenKernel_source_pole hsymm hlf hcons hA (hDA ha)
    have hgD := lapSum_greenKernel_source_pole hsymm hlf hcons hDfin ha
    have hq := lapSum_poleQ hlf hcons (Finset.mem_coe.1 ha)
    simp only [lapSum_add_pole hlf, lapSum_sub hlf, lapSum_const_mul hlf]
    rw [hgA, hgD, hq]
    linarith
  have hbd : ∀ a ∈ (D : Set ℤ), ∀ b, m a b ≠ 0 → b ∉ (D : Set ℤ) →
      -(w b + t / ε * greenKernel m A 0 b - t / ε * greenKernel m (D : Set ℤ) 0 b + poleQ m D b) ≤ 0 := by
    intro a ha b hab hbD
    have hb : b ∈ vBoundary m (D : Set ℤ) := ⟨hbD, a, ha, hab⟩
    have hbW : b ∈ W := hW hb
    have hz : greenKernel m (D : Set ℤ) 0 b = 0 := by
      rw [greenKernel_symm_pole hsymm hlf hcons hDfin 0 b]
      exact greenKernel_eq_zero_of_not_mem m hbD 0
    have hq : poleQ m D b = 0 := by
      unfold poleQ
      exact Finset.sum_eq_zero fun x _ => greenKernel_eq_zero_of_not_mem m hbD x
    rw [hz, hq]
    have := hobs b hbW
    linarith
  have key := nonpos_of_lapSum_nonneg hlf hDfin (escape_of_adjacent_succ hcons hDfin) hsub hbd
  intro a ha
  have h : -(w a + t / ε * greenKernel m A 0 a - t / ε * greenKernel m (D : Set ℤ) 0 a + poleQ m D a) ≤ 0 :=
    key a (Finset.mem_coe.2 ha)
  linarith

/-- **Source-capacity lower bound**. For the real infimum
`sInf` over the admissible supersolutions `w` (`Δ_m w ≤ 1/deg` on `A`, `w ≥ -(t/ε) g_A(0,·)` on `W`), which is
nonempty (`w = 0` is admissible) and bounded below, `ε · V_t^ε(0) ≥ (t - ε #D) g_D(0,0)`, where
`V_t^ε(0) = sInf {w(0)} + (t/ε) g_A(0,0)`. -/
theorem sourceCapacity_inf {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) {D : Finset ℤ}
    (hDA : (D : Set ℤ) ⊆ A) (h0 : (0 : ℤ) ∈ D) {W : Set ℤ} (hW : vBoundary m (D : Set ℤ) ⊆ W)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    (t - ε * (D.card : ℝ)) * greenKernel m (D : Set ℤ) 0 0 ≤
      ε * (sInf ((fun w : ℤ → ℝ => w 0) '' {w : ℤ → ℝ |
          (∀ a ∈ A, mLaplacian m w a ≤ (mdeg m a : ℝ)⁻¹) ∧
            (∀ b ∈ W, -(t / ε * greenKernel m A 0 b) ≤ w b)}) +
        t / ε * greenKernel m A 0 0) := by
  have hc : 0 ≤ t / ε := div_nonneg ht hε.le
  have hεne : ε ≠ 0 := hε.ne'
  set S : Set ℝ := (fun w : ℤ → ℝ => w 0) '' {w : ℤ → ℝ |
          (∀ a ∈ A, mLaplacian m w a ≤ (mdeg m a : ℝ)⁻¹) ∧
            (∀ b ∈ W, -(t / ε * greenKernel m A 0 b) ≤ w b)} with hS_def
  have hlow : ∀ x ∈ S, (t / ε - D.card) * greenKernel m (D : Set ℤ) 0 0 - t / ε * greenKernel m A 0 0 ≤ x := by
    rintro x ⟨w, ⟨hL, hO⟩, rfl⟩
    have h1 := sourceCapacity_pointwise hsymm hlf hcons hA hDA hW ht hε
      (fun a ha => hL a (hDA (Finset.mem_coe.2 ha))) hO 0 h0
    have h2 := poleQ_zero_le hsymm hlf hcons D
    dsimp only
    linarith
  have hne : S.Nonempty := by
    refine ⟨(fun _ : ℤ => (0 : ℝ)) 0, (fun _ : ℤ => (0 : ℝ)), ⟨?_, ?_⟩, rfl⟩
    · intro a _
      have h0m : mLaplacian m (fun _ : ℤ => (0 : ℝ)) a = 0 := by simp [mLaplacian]
      rw [h0m]
      exact inv_nonneg.2 (Nat.cast_nonneg _)
    · intro b _
      have := mul_nonneg hc (greenKernel_nonneg_pole m A 0 b)
      show -(t / ε * greenKernel m A 0 b) ≤ 0
      linarith
  have hs : (t / ε - D.card) * greenKernel m (D : Set ℤ) 0 0 - t / ε * greenKernel m A 0 0 ≤ sInf S :=
    le_csInf hne hlow
  have hεt : ε * (t / ε) = t := by field_simp [hεne]
  have hmul := mul_le_mul_of_nonneg_left hs hε.le
  have e : ε * (sInf S + t / ε * greenKernel m A 0 0) =
      ε * sInf S + t * greenKernel m A 0 0 := by
    linear_combination (greenKernel m A 0 0) * hεt
  rw [e]
  have e1 : ε * ((t / ε - D.card) * greenKernel m (D : Set ℤ) 0 0 - t / ε * greenKernel m A 0 0) =
      (t - ε * D.card) * greenKernel m (D : Set ℤ) 0 0 - t * greenKernel m A 0 0 := by
    linear_combination (greenKernel m (D : Set ℤ) 0 0 - greenKernel m A 0 0) * hεt
  linarith

end MatedCRT
