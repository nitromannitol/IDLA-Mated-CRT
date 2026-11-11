import MatedCRT.Proofs.Sec4.ConvergenceDivisible.HolderNets

/-! # Hölder classes on a compact set: exponents, dense families, finite nets

Deterministic ingredients of `OdometerMeasurableSelectionStep` (Lemma 4.6; GAPS
clarification 2026-11-06, position-indexed pigeonhole). For a compact `K` the classes
`HolderClassOn K m (holderExp j)` are indexed by `(m, j) : ℕ × ℕ`. Every Hölder continuous limit on `K`
lies in one of them. Each class is approximated by a countable family of functions continuous on `K`
(so that the envSigma deviation events of `EnvSigmaDeviation` apply), and by finite nets chosen from that
family. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- The Hölder exponent with index `j`: `1 / (j + 1)`. -/
noncomputable def holderExp (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma holderExp_pos (j : ℕ) : 0 < holderExp j := by
  unfold holderExp
  positivity

/-- The zero function lies in every Hölder class. -/
lemma holderClassOn_zero (K : Set ℂ) (m : ℕ) (α : ℝ) :
    HolderClassOn K m α (fun _ => 0) := by
  refine ⟨fun x _ => ?_, fun x _ y _ => ?_⟩
  · simp
  · simp only [sub_self, abs_zero]
    positivity

/-- The pointwise Hölder bound of a `HolderOnWith` function, in the `dist` form. -/
lemma holderOnWith_dist_le {K : Set ℂ} {w : ℂ → ℝ} {C χ : NNReal} (hH : HolderOnWith C χ w K)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    |w x - w y| ≤ (C : ℝ) * dist x y ^ (χ : ℝ) := by
  have h := hH x hx y hy
  have hr : ENNReal.ofReal ((C : ℝ) * dist x y ^ (χ : ℝ)) = (C : ENNReal) * edist x y ^ (χ : ℝ) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)]
  have hl : edist (w x) (w y) = ENNReal.ofReal |w x - w y| := by
    rw [edist_dist, Real.dist_eq]
  have h2 : ENNReal.ofReal |w x - w y| ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (χ : ℝ)) := by
    rw [← hl, hr]
    exact h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- A function Hölder continuous with some exponent on a compact set lies in some Hölder class
`HolderClassOn K m (holderExp j)`. -/
lemma exists_holderClass_of_isHolder {K : Set ℂ} (hK : IsCompact K) {w : ℂ → ℝ}
    (hc : ContinuousOn w K) (hw : IsHolderContinuousOn w K) :
    ∃ m j : ℕ, HolderClassOn K m (holderExp j) w := by
  obtain ⟨C, χ, hχ0, _, hH⟩ := hw
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
  set D : ℝ := 2 * (|R| + 1) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hdist : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D := by
    intro x hx y hy
    have hx' : dist x 0 ≤ R := hR hx
    have hy' : dist y 0 ≤ R := hR hy
    have h1 : dist x y ≤ dist x 0 + dist y 0 := dist_triangle_right x y 0
    linarith [le_abs_self R, abs_nonneg R]
  have hχpos : (0 : ℝ) < χ := by exact_mod_cast hχ0
  obtain ⟨j, hj⟩ : ∃ j : ℕ, holderExp j ≤ (χ : ℝ) := by
    refine ⟨⌈1 / (χ : ℝ)⌉₊, ?_⟩
    have h1 : 1 / (χ : ℝ) ≤ (⌈1 / (χ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    unfold holderExp
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hχpos] at h1
    nlinarith
  set α : ℝ := holderExp j with hα
  have hαpos : 0 < α := holderExp_pos j
  set M : ℝ := max B ((C : ℝ) * D ^ ((χ : ℝ) - α)) with hM
  have hCM : (C : ℝ) * D ^ ((χ : ℝ) - α) ≤ (⌈M⌉₊ : ℝ) :=
    le_trans (le_max_right _ _) (Nat.le_ceil M)
  refine ⟨⌈M⌉₊, j, ?_, ?_⟩
  · intro x hx
    have hbx := hB x hx
    rw [Real.norm_eq_abs] at hbx
    exact le_trans hbx (le_trans (le_max_left _ _) (Nat.le_ceil M))
  · intro x hx y hy
    have h1 := holderOnWith_dist_le hH hx hy
    have hsum : α + ((χ : ℝ) - α) ≠ 0 := by
      have : α + ((χ : ℝ) - α) = (χ : ℝ) := by ring
      rw [this]
      exact (NNReal.coe_pos.2 hχ0).ne'
    have hd : dist x y ^ (χ : ℝ) = dist x y ^ α * dist x y ^ ((χ : ℝ) - α) := by
      rw [← Real.rpow_add' dist_nonneg hsum]
      congr 1
      ring
    have h2 : dist x y ^ ((χ : ℝ) - α) ≤ D ^ ((χ : ℝ) - α) :=
      Real.rpow_le_rpow dist_nonneg (hdist x hx y hy) (by linarith)
    have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.2
    have hpow : (0 : ℝ) ≤ dist x y ^ α := by positivity
    calc |w x - w y| ≤ (C : ℝ) * dist x y ^ (χ : ℝ) := h1
      _ = (C : ℝ) * (dist x y ^ α * dist x y ^ ((χ : ℝ) - α)) := by rw [hd]
      _ ≤ (C : ℝ) * (dist x y ^ α * D ^ ((χ : ℝ) - α)) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          exact mul_le_mul_of_nonneg_left h2 hpow
      _ = ((C : ℝ) * D ^ ((χ : ℝ) - α)) * dist x y ^ α := by ring
      _ ≤ (⌈M⌉₊ : ℝ) * dist x y ^ α := mul_le_mul_of_nonneg_right hCM hpow

/-- A countable family, enumerated as `cen`, of functions continuous on `K` lying in the class
`(m, j)`, approximating every member of that class (the countable dense family of
`exists_countable_holder_dense`, enumerated; non-members are replaced by `0`). -/
lemma exists_dense_seq_holderClass {K : Set ℂ} (hK : IsCompact K) (m j : ℕ) :
    ∃ cen : ℕ → ℂ → ℝ,
      (∀ i, ContinuousOn (cen i) K ∧ HolderClassOn K m (holderExp j) (cen i)) ∧
      ∀ h : ℂ → ℝ, HolderClassOn K m (holderExp j) h → ∀ ε : ℝ, 0 < ε →
        ∃ i, ∀ x ∈ K, |h x - cen i x| < ε := by
  classical
  obtain ⟨D, hDc, hDcl, hDd⟩ := exists_countable_holder_dense (m := (m : ℝ)) hK (holderExp_pos j)
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1 hDc
  refine ⟨fun i => if HolderClassOn K m (holderExp j) (f i) then f i else fun _ => 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact ⟨holderClassOn_continuousOn (holderExp_pos j) hi, hi⟩
    · exact ⟨continuousOn_const, holderClassOn_zero K m _⟩
  · intro h hh ε hε
    obtain ⟨c, hcD, hc⟩ := hDd h hh ε hε
    obtain ⟨i, rfl⟩ := hf hcD
    refine ⟨i, fun x hx => ?_⟩
    have hi : HolderClassOn K m (holderExp j) (f i) := hDcl _ hcD
    simp only [hi, ite_true]
    exact hc x hx

/-- Finite nets of a class, chosen among the enumerated family: every member of the class lies
within `(1/2)^k` on `K` of one of finitely many `cen i`. -/
lemma exists_net_holderClass {K : Set ℂ} (hK : IsCompact K) (m j : ℕ) (cen : ℕ → ℂ → ℝ)
    (hcen : ∀ h : ℂ → ℝ, HolderClassOn K m (holderExp j) h → ∀ ε : ℝ, 0 < ε →
      ∃ i, ∀ x ∈ K, |h x - cen i x| < ε) (k : ℕ) :
    ∃ N : Finset ℕ, ∀ h : ℂ → ℝ, HolderClassOn K m (holderExp j) h →
      ∃ i ∈ N, ∀ x ∈ K, |h x - cen i x| < (1 / 2 : ℝ) ^ k := by
  classical
  set δ : ℝ := (1 / 2 : ℝ) ^ k / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨F, hFcl, hFnet⟩ := holder_finite_net_in_class (m := (m : ℝ)) hK (holderExp_pos j) hδpos
  have hsel : ∀ c : ℂ → ℝ, ∃ i : ℕ, HolderClassOn K m (holderExp j) c →
      ∀ x ∈ K, |c x - cen i x| < δ := by
    intro c
    by_cases hc : HolderClassOn K m (holderExp j) c
    · obtain ⟨i, hi⟩ := hcen c hc δ hδpos
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose g hg using hsel
  refine ⟨F.image g, fun h hh => ?_⟩
  obtain ⟨c, hcF, hc⟩ := hFnet h hh
  refine ⟨g c, Finset.mem_image_of_mem g hcF, fun x hx => ?_⟩
  have h1 := hc x hx
  have h2 := hg c (hFcl c hcF) x hx
  calc |h x - cen (g c) x| ≤ |h x - c x| + |c x - cen (g c) x| := abs_sub_le _ _ _
    _ < δ + δ := add_lt_add h1 h2
    _ = (1 / 2 : ℝ) ^ k := by rw [hδ]; ring

end MatedCRT
