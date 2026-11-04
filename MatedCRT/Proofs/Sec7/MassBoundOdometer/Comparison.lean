import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec4.GreenLaplacian
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-!
# Lemma 7.2: comparison of the stopped odometer with a sum of Green's kernels (proof, lines 3001-3024)

Deterministic potential theory on a symmetric, locally finite multigraph on `ℤ` in which `k ∼ k + 1`:

* `le_iSup_vBoundary_of_subharmonic` (eq:upper-bound-on-ut, line 3005): a nonnegative function `u`, vanishing off a
  finite set `W` and subharmonic on `W \ cl(Θ)`, satisfies `u ≤ sup_{∂Θ} u` off `Θ` (maximum principle on
  `W \ cl(Θ)`, whose boundary lies in `∂Θ ∪ Wᶜ`);
* `sum_greenKernel_le_of_laplacian` (the display of lines 3020-3023): if `Δu ≥ (deg)⁻¹ 1_F` on a finite set `D ⊇ F`
  and `u ≤ M` on `∂D`, then `𝔣 = ∑_{b ∈ F} g_D(·, b) ≤ M` on `D`, since `u + 𝔣 - M` is subharmonic on `D`
  (eq:discrete-green-laplacian, line 797, for `Δ g_D(·, b)`) and nonpositive on `∂D`;
* `stoppedOdometer_le_iSup_vBoundary`, `mLaplacian_stoppedOdometer_nonneg`: the first item for `u^ε_t`, which is
  subharmonic away from the origin (eq:laplacian-of-uteps).
-/

namespace MatedCRT.Sec7

open Set Metric

variable {m : ℤ → ℤ → ℕ}

/-- `lapSum` is unchanged by subtracting a constant. -/
theorem lapSum_sub_const (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (M : ℝ) (a : ℤ) :
    lapSum hlf (fun x => u x - M) a = lapSum hlf u a := by
  simp only [lapSum, sub_sub_sub_cancel_right]

theorem lapSum_nonneg_of_mLaplacian_nonneg (hlf : IsLocallyFiniteMult m) {u : ℤ → ℝ} {a : ℤ}
    (h : 0 ≤ mLaplacian m u a) : 0 ≤ lapSum hlf u a := by
  rw [← mLaplacian_mul_mdeg hlf]
  exact mul_nonneg h (Nat.cast_nonneg _)

/-- A nonnegative function is subharmonic at its zeros. -/
theorem mLaplacian_nonneg_of_eq_zero {u : ℤ → ℝ} (hu0 : ∀ x, 0 ≤ u x) {a : ℤ} (ha : u a = 0) :
    0 ≤ mLaplacian m u a := by
  unfold mLaplacian
  rw [ha]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (finsum_nonneg fun b => ?_)
  rw [sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (hu0 b)

/-- The boundary of a finite set is finite. -/
theorem vBoundary_finite (hlf : ∀ a, {b | m a b ≠ 0}.Finite) {Θ : Set ℤ} (hΘ : Θ.Finite) :
    (vBoundary m Θ).Finite := by
  refine (hΘ.biUnion fun a _ => hlf a).subset ?_
  rintro c ⟨-, a, ha, hac⟩
  exact mem_biUnion ha hac

/-- **eq:upper-bound-on-ut** (line 3005), general form: a nonnegative `u` vanishing off the finite set `W` and
subharmonic on `W \ cl(Θ)` is at most `sup_{∂Θ} u` off the finite set `Θ`. -/
theorem le_iSup_vBoundary_of_subharmonic (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) {W : Set ℤ} (hW : W.Finite) {u : ℤ → ℝ} (hu0 : ∀ x, 0 ≤ u x)
    (huW : ∀ x ∉ W, u x = 0) {Θ : Set ℤ} (hΘ : Θ.Finite)
    (hsub : ∀ x ∈ W, x ∉ vClosure m Θ → 0 ≤ mLaplacian m u x) {a : ℤ} (ha : a ∉ Θ) :
    u a ≤ ⨆ b : vBoundary m Θ, u b := by
  have := (vBoundary_finite hlf hΘ).to_subtype
  have hbdd : BddAbove (range fun c : vBoundary m Θ => u c) := (Set.finite_range _).bddAbove
  have hM0 : 0 ≤ ⨆ b : vBoundary m Θ, u b := Real.iSup_nonneg fun c => hu0 c
  have hle : ∀ b ∈ vBoundary m Θ, u b ≤ ⨆ b : vBoundary m Θ, u b := fun b hb => le_ciSup hbdd ⟨b, hb⟩
  by_cases hab : a ∈ vBoundary m Θ
  · exact hle a hab
  by_cases haW : a ∈ W
  swap
  · rw [huW a haW]
    exact hM0
  have hUfin : (W \ vClosure m Θ).Finite := hW.subset sdiff_subset
  have hsubU : ∀ x ∈ W \ vClosure m Θ, 0 ≤ lapSum hlf (fun x => u x - ⨆ b : vBoundary m Θ, u b) x := by
    intro x hx
    rw [lapSum_sub_const hlf]
    exact lapSum_nonneg_of_mLaplacian_nonneg hlf (hsub x hx.1 hx.2)
  have hbdU : ∀ x ∈ W \ vClosure m Θ, ∀ y, m x y ≠ 0 → y ∉ W \ vClosure m Θ →
      u y - ⨆ b : vBoundary m Θ, u b ≤ 0 := by
    intro x hx y hxy hyU
    by_cases hyW : y ∈ W
    · have hyc : y ∈ vClosure m Θ := by
        by_contra h
        exact hyU ⟨hyW, h⟩
      rcases hyc with hyΘ | hyb
      · exfalso
        refine hx.2 (Or.inr ⟨fun h => hx.2 (Or.inl h), y, hyΘ, ?_⟩)
        rw [hsymm]
        exact hxy
      · linarith [hle y hyb]
    · rw [huW y hyW]
      linarith
  have hmain : u a - ⨆ b : vBoundary m Θ, u b ≤ 0 :=
    nonpos_of_lapSum_nonneg (m := m) hlf hUfin (escape_of_adjacent_succ hsucc hUfin) hsubU hbdU a
      ⟨haW, fun h => h.elim ha hab⟩
  linarith

/-- **Comparison with a sum of Green's kernels** (lines 3008-3023): if `Δu ≥ (deg)⁻¹ 1_F` on the finite set `D`,
`u ≥ 0` and `u ≤ M` on `∂D`, then `∑_{b ∈ F} g_D(x, b) ≤ M` for `x ∈ D`. -/
theorem sum_greenKernel_le_of_laplacian (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {D : Set ℤ} (hD : D.Finite)
    (hR1 : ∀ b, ∀ a ∈ D, mLaplacian m (fun x => greenFn m D x b) a = -(if a = b then 1 else 0))
    {u : ℤ → ℝ} (hu0 : ∀ x, 0 ≤ u x) {F : Finset ℤ}
    (hΔ : ∀ x ∈ D, (if x ∈ F then ((mdeg m x : ℕ) : ℝ)⁻¹ else 0) ≤ mLaplacian m u x)
    {M : ℝ} (hbd : ∀ y ∈ vBoundary m D, u y ≤ M) {x : ℤ} (hx : x ∈ D) :
    ∑ b ∈ F, greenKernel m D x b ≤ M := by
  have hf0 : ∀ y ∉ D, ∑ b ∈ F, greenKernel m D y b = 0 := fun y hy =>
    Finset.sum_eq_zero fun b _ => by simp [greenKernel, greenFn_eq_zero_of_not_mem m hy b]
  have hΔf : ∀ y ∈ D, mLaplacian m (fun z => ∑ b ∈ F, greenKernel m D z b) y =
      -(if y ∈ F then ((mdeg m y : ℕ) : ℝ)⁻¹ else 0) := by
    intro y hy
    rw [mLaplacian_finset_sum hlf F (fun b z => greenKernel m D z b) y]
    have hterm : ∀ b ∈ F, mLaplacian m (fun z => greenKernel m D z b) y =
        -(((mdeg m b : ℕ) : ℝ)⁻¹ * if y = b then 1 else 0) := by
      intro b _
      have : (fun z => greenKernel m D z b) = fun z => ((mdeg m b : ℕ) : ℝ)⁻¹ * greenFn m D z b := by
        funext z
        unfold greenKernel
        rw [div_eq_inv_mul]
      rw [this, mLaplacian_const_mul, hR1 b y hy]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  have hsubD : ∀ y ∈ D, 0 ≤ lapSum hlf (fun z => u z + ∑ b ∈ F, greenKernel m D z b - M) y := by
    intro y hy
    rw [lapSum_sub_const hlf]
    refine lapSum_nonneg_of_mLaplacian_nonneg hlf ?_
    rw [mLaplacian_add_of_locallyFinite hlf, hΔf y hy]
    linarith [hΔ y hy]
  have hbdD : ∀ y ∈ D, ∀ y', m y y' ≠ 0 → y' ∉ D → u y' + ∑ b ∈ F, greenKernel m D y' b - M ≤ 0 := by
    intro y hy y' hyy' hy'D
    rw [hf0 y' hy'D]
    linarith [hbd y' ⟨hy'D, y, hy, hyy'⟩]
  have hmain : u x + ∑ b ∈ F, greenKernel m D x b - M ≤ 0 :=
    nonpos_of_lapSum_nonneg (m := m) hlf hD (escape_of_adjacent_succ hsucc hD) hsubD hbdD x hx
  linarith [hu0 x]

variable {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

/-- `u^ε_t = 0` off `Λ^ε_t` (everywhere on `ℤ`). -/
theorem stoppedOdometer_eq_zero_of_not_mem_cluster' (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (ha : a ∉ matedDiscreteCluster m ε η ρ t) : stoppedOdometer m ε η ρ t a = 0 :=
  le_antisymm (not_lt.1 fun h => ha (mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht h))
    (stoppedOdometer_nonneg hε ht a)

/-- `u^ε_t` is subharmonic away from the origin (eq:laplacian-of-uteps): `Δu^ε_t = (deg^ε)⁻¹` on `Λ^ε_t \ {0}` and
`u^ε_t = 0 ≤ u^ε_t` off `Λ^ε_t`. -/
theorem mLaplacian_stoppedOdometer_nonneg (hε : 0 < ε) (ht : 0 < t)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    {a : ℤ} (ha : a ≠ 0) : 0 ≤ mLaplacian m (stoppedOdometer m ε η ρ t) a := by
  by_cases haΛ : a ∈ matedDiscreteCluster m ε η ρ t
  · have h : mLaplacian m (stoppedOdometer m ε η ρ t) a = ((mdeg m a : ℕ) : ℝ)⁻¹ := hlap a haΛ ha
    rw [h]
    exact inv_nonneg.2 (Nat.cast_nonneg _)
  · exact mLaplacian_nonneg_of_eq_zero (fun x => stoppedOdometer_nonneg hε ht x)
      (stoppedOdometer_eq_zero_of_not_mem_cluster' hε ht haΛ)

/-- **eq:upper-bound-on-ut** (line 3005): for a finite `Θ ∋ 0`, `u^ε_t ≤ sup_{∂Θ} u^ε_t` off `Θ`. -/
theorem stoppedOdometer_le_iSup_vBoundary (hε : 0 < ε) (ht : 0 < t) (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    {Θ : Set ℤ} (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ) {a : ℤ} (ha : a ∉ Θ) :
    stoppedOdometer m ε η ρ t a ≤ ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b :=
  le_iSup_vBoundary_of_subharmonic hsymm hlf hsucc hfin (fun x => stoppedOdometer_nonneg hε ht x)
    (fun x hx => by simp [stoppedOdometer, hx]) hΘ
    (fun x _ hx => mLaplacian_stoppedOdometer_nonneg hε ht hlap fun h => hx (Or.inl (h ▸ h0))) ha

end MatedCRT.Sec7
