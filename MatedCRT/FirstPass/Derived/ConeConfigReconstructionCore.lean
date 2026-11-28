import MatedCRT.FirstPass.Derived.ConeConfigReconstructionLabels
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionBlocks
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMeet
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionCellSide
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionRelabel

/-!
# The reconstruction recovers the local configuration, deterministically

Let `e` be a curve in the curve event `ReconCurveEvent α R a L δ M`, and `ξ = e ∘ φ` a curve parametrized by the mass of
a locally finite measure `μ` (`IsMassParam`). For every phase `θ ∈ [0, 1]`, for all large `n`, the local configuration
near the annulus `V = B_R(0) \ closedBall 0 α` of the true data at mesh `1/n` with phase `θ` (`phaseData`) is the value
of the reconstruction map `coneRecon` at the outer data and the residues of the two offsets
(`eventually_localConfig_eq_coneRecon`).

The proof (the answer to MQ-sbl-18, section "Recovering the formal configuration"): for large `n` the cells meeting the
annulus `{α/2 ≤ |z| ≤ 2R}` lie in one of the two time blocks (`good_of_mem_cell`), by uniform continuity of `φ` and `ξ`
on a compact window of quantum times; every vertex of `V` and every neighbour of such a vertex is such a cell
(`cellSideMult_ne_zero_inter_nonempty`); on these cells the synthetic label `reconLabel` gives the same point and the
same multiplicities (the block clocks are the quantum clock, `posBlockTime_eq`, `negBlockTime_eq`; the frontier-side
count is invariant under the reparametrization `φ`, `cellSideCount_comp_orderIso`); and local configurations forget the
labels (`localConfig_eq_of_strictMonoOn`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT

open LatticeProb (CountablePhaseSpace)

/-! ### Good cells -/

/-- The cell `k` (quantum times `[(k - 1 + θ)/n, (k + θ)/n]`) lies in the negative block. -/
def NegGood (φ : ℝ ≃o ℝ) (a L : ℝ) (n : ℕ) (θ : ℝ) (k : ℤ) : Prop :=
  φ.symm (-L) < ((k : ℝ) - 1 + θ) / n ∧ ((k : ℝ) + θ) / n ≤ φ.symm (-a)

/-- The cell `k` lies in the positive block. -/
def PosGood (φ : ℝ ≃o ℝ) (a L : ℝ) (n : ℕ) (θ : ℝ) (k : ℤ) : Prop :=
  φ.symm a ≤ ((k : ℝ) - 1 + θ) / n ∧ ((k : ℝ) + θ) / n < φ.symm L

section Deterministic

variable {α R a L δ M : ℝ} {e ξ : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ} {μ : Measure ℂ} {n : ℕ} {θ : ℝ}

/-- The offsets `C = (φ⁻¹(-a), φ⁻¹(a))`. -/
abbrev blockOffsets (φ : ℝ ≃o ℝ) (a : ℝ) : Fin 2 → ℝ := ![φ.symm (-a), φ.symm a]

theorem blockOffsets_zero (φ : ℝ ≃o ℝ) (a : ℝ) : blockOffsets φ a 0 = φ.symm (-a) := rfl

theorem blockOffsets_one (φ : ℝ ≃o ℝ) (a : ℝ) : blockOffsets φ a 1 = φ.symm a := rfl

theorem blockOffsets_lt (φ : ℝ ≃o ℝ) {a : ℝ} (ha : 0 < a) : blockOffsets φ a 0 < blockOffsets φ a 1 := by
  simp only [blockOffsets, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact φ.symm.lt_iff_lt.2 (by linarith)

theorem cell_left_lt_right (hn : 0 < n) (θ : ℝ) (k : ℤ) :
    ((k : ℝ) - 1 + θ) / n < ((k : ℝ) + θ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_lt_div_of_pos_right (by linarith) hn'

theorem not_negGood_and_posGood (ha : 0 < a) (hn : 0 < n) {k : ℤ} (h₁ : NegGood φ a L n θ k)
    (h₂ : PosGood φ a L n θ k) : False := by
  have h := blockOffsets_lt φ ha
  simp only [blockOffsets, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have := cell_left_lt_right hn θ k
  linarith [h₁.2, h₂.1]

/-! ### Valid synthetic labels -/

variable [IsFiniteMeasureOnCompacts μ]

theorem reconValid_reconLabel_of_negGood (hp : IsMassParam e ξ φ μ) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {k : ℤ} (hk : NegGood φ a L n θ k) :
    ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M)) (offsetResiduesOf n θ (blockOffsets φ a))
      (reconLabel n θ (blockOffsets φ a) k) := by
  have h0 : ((k : ℝ) + θ) / n ≤ blockOffsets φ a 0 := hk.2
  obtain ⟨-, hl0⟩ := reconLabel_le_zero_iff hn h0
  rw [ReconValid, ite_eq_left hl0, reconRelLeft_reconLabel_neg hn h0, reconRelRight_reconLabel_neg hn h0,
    negBlockMass_eq hp haL hδ hE]
  simp only [blockOffsets, Matrix.cons_val_zero]
  exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

theorem reconValid_reconLabel_of_posGood (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {k : ℤ} (hk : PosGood φ a L n θ k) :
    ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M)) (offsetResiduesOf n θ (blockOffsets φ a))
      (reconLabel n θ (blockOffsets φ a) k) := by
  have hC := blockOffsets_lt φ ha
  have h1 : blockOffsets φ a 1 ≤ ((k : ℝ) - 1 + θ) / n := hk.1
  have h3 := three_le_reconLabel hn hC h1
  have hl0 : ¬ (reconLabel n θ (blockOffsets φ a) k ≤ 0) := by omega
  rw [ReconValid, ite_eq_right hl0, reconRelLeft_reconLabel_pos hn hC h1, reconRelRight_reconLabel_pos hn hC h1,
    posBlockMass_eq hp haL hδ hE]
  simp only [blockOffsets, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

/-- Every valid synthetic label is the label of a good cell. -/
theorem exists_good_of_reconValid (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {ℓ : ℤ}
    (hℓ : ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M))
      (offsetResiduesOf n θ (blockOffsets φ a)) ℓ) :
    ∃ k, (NegGood φ a L n θ k ∨ PosGood φ a L n θ k) ∧ reconLabel n θ (blockOffsets φ a) k = ℓ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := blockOffsets_lt φ ha
  set C := blockOffsets φ a with hCdef
  by_cases hl0 : ℓ ≤ 0
  · rw [ReconValid, ite_eq_left hl0, negBlockMass_eq hp haL hδ hE] at hℓ
    set k := ℓ + ⌊(n : ℝ) * C 0 - θ⌋ with hk
    have hkℓ : k - ⌊(n : ℝ) * C 0 - θ⌋ = ℓ := by omega
    have hR : reconRelRight n (offsetResiduesOf n θ C) ℓ = ((k : ℝ) + θ) / n - C 0 := by
      rw [reconRelRight, ite_eq_left hl0, offsetResiduesOf_apply, ← hkℓ]
      simpa using shift_sub_fract_div hn θ (C 0) k 0
    have hL : reconRelLeft n (offsetResiduesOf n θ C) ℓ = ((k : ℝ) - 1 + θ) / n - C 0 := by
      rw [reconRelLeft, ite_eq_left hl0, offsetResiduesOf_apply, ← hkℓ]
      exact shift_sub_fract_div hn θ (C 0) k 1
    rw [hR, hL] at hℓ
    have hneg : NegGood φ a L n θ k := by
      simp only [hCdef, blockOffsets, Matrix.cons_val_zero] at hℓ
      exact ⟨by linarith [hℓ.1], by linarith [hℓ.2]⟩
    refine ⟨k, Or.inl hneg, ?_⟩
    rw [(reconLabel_le_zero_iff hn hneg.2).1, hkℓ]
  · rw [ReconValid, ite_eq_right hl0, posBlockMass_eq hp haL hδ hE] at hℓ
    set k := ℓ - 2 + ⌊(n : ℝ) * C 1 - θ⌋ with hk
    have hkℓ : k - ⌊(n : ℝ) * C 1 - θ⌋ = ℓ - 2 := by omega
    have hR : reconRelRight n (offsetResiduesOf n θ C) ℓ = ((k : ℝ) + θ) / n - C 1 := by
      have h := shift_sub_fract_div hn θ (C 1) k 0
      simp only [sub_zero] at h
      rw [reconRelRight, ite_eq_right hl0, offsetResiduesOf_apply, ← h, hkℓ]
      congr 1
      push_cast
      ring
    have hL : reconRelLeft n (offsetResiduesOf n θ C) ℓ = ((k : ℝ) - 1 + θ) / n - C 1 := by
      rw [reconRelLeft, ite_eq_right hl0, offsetResiduesOf_apply,
        ← shift_sub_fract_div hn θ (C 1) k 1, hkℓ]
      congr 1
      push_cast
      ring
    rw [hR, hL] at hℓ
    have hpos : PosGood φ a L n θ k := by
      simp only [hCdef, blockOffsets, Matrix.cons_val_one, Matrix.cons_val_zero] at hℓ
      exact ⟨by linarith [hℓ.1], by linarith [hℓ.2]⟩
    refine ⟨k, Or.inr hpos, ?_⟩
    have hlt : C 0 < ((k : ℝ) + θ) / n := by
      have h1 : C 1 ≤ ((k : ℝ) - 1 + θ) / n := hpos.1
      linarith [cell_left_lt_right hn θ k]
    rw [reconLabel_of_lt hlt, hkℓ]
    ring

/-! ### Points and multiplicities on good cells -/

/-- The Lebesgue times of the two endpoints of the synthetic cell of a good cell are `φ` of its quantum times. -/
theorem reconTime_reconLabel (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {k : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) :
    reconTime a M e (μ.restrict (offsetOuterAnnulus δ M)) (reconLabel n θ (blockOffsets φ a) k)
        (reconRelLeft n (offsetResiduesOf n θ (blockOffsets φ a)) (reconLabel n θ (blockOffsets φ a) k)) =
      φ (((k : ℝ) - 1 + θ) / n) ∧
    reconTime a M e (μ.restrict (offsetOuterAnnulus δ M)) (reconLabel n θ (blockOffsets φ a) k)
        (reconRelRight n (offsetResiduesOf n θ (blockOffsets φ a)) (reconLabel n θ (blockOffsets φ a) k)) =
      φ (((k : ℝ) + θ) / n) := by
  have hlr := cell_left_lt_right hn θ k
  have hC := blockOffsets_lt φ ha
  rcases hk with hk | hk
  · have h0 : ((k : ℝ) + θ) / n ≤ blockOffsets φ a 0 := hk.2
    obtain ⟨-, hl0⟩ := reconLabel_le_zero_iff hn h0
    rw [reconTime, ite_eq_left hl0, reconTime, ite_eq_left hl0, reconRelLeft_reconLabel_neg hn h0,
      reconRelRight_reconLabel_neg hn h0]
    simp only [blockOffsets, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · rw [negBlockTime_eq hp haL hδ hE (by linarith [hk.1]) (by linarith [hk.2])]
      congr 1; ring
    · rw [negBlockTime_eq hp haL hδ hE (by linarith [hk.1]) (by linarith [hk.2])]
      congr 1; ring
  · have h1 : blockOffsets φ a 1 ≤ ((k : ℝ) - 1 + θ) / n := hk.1
    have h3 := three_le_reconLabel hn hC h1
    have hl0 : ¬ (reconLabel n θ (blockOffsets φ a) k ≤ 0) := by omega
    rw [reconTime, ite_eq_right hl0, reconTime, ite_eq_right hl0, reconRelLeft_reconLabel_pos hn hC h1,
      reconRelRight_reconLabel_pos hn hC h1]
    simp only [blockOffsets, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · rw [posBlockTime_eq hp haL hδ hE (by linarith [hk.1]) (by linarith [hk.2])]
      congr 1; ring
    · rw [posBlockTime_eq hp haL hδ hE (by linarith [hk.1]) (by linarith [hk.2])]
      congr 1; ring

theorem reconValid_of_good (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {k : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) :
    ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M)) (offsetResiduesOf n θ (blockOffsets φ a))
      (reconLabel n θ (blockOffsets φ a) k) :=
  hk.elim (reconValid_reconLabel_of_negGood hp haL hδ hE hn)
    (reconValid_reconLabel_of_posGood hp ha haL hδ hE hn)

/-- The synthetic point of a good cell is its true point. -/
theorem reconData_fst_reconLabel (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n) {k : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) :
    (reconData a L M n e (μ.restrict (offsetOuterAnnulus δ M)) (offsetResiduesOf n θ (blockOffsets φ a))).1
      (reconLabel n θ (blockOffsets φ a) k) = (phaseData n θ ξ).1 k := by
  simp only [reconData, phaseData]
  rw [ite_eq_left (reconValid_of_good hp ha haL hδ hE hn hk), (reconTime_reconLabel hp ha haL hδ hE hn hk).2,
    hp.comp]

/-- On good cells the synthetic label is strictly increasing. -/
theorem reconLabel_lt_reconLabel (ha : 0 < a) (hn : 0 < n) {k k' : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) (hk' : NegGood φ a L n θ k' ∨ PosGood φ a L n θ k')
    (hkk : k < k') : reconLabel n θ (blockOffsets φ a) k < reconLabel n θ (blockOffsets φ a) k' := by
  have hC := blockOffsets_lt φ ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmono : ((k : ℝ) + θ) / n < ((k' : ℝ) + θ) / n :=
    div_lt_div_of_pos_right (by linarith [show (k : ℝ) < k' by exact_mod_cast hkk]) hn'
  rcases hk' with hk' | hk'
  · -- both negative
    have hk0 : ((k : ℝ) + θ) / n ≤ blockOffsets φ a 0 := le_trans hmono.le hk'.2
    rw [(reconLabel_le_zero_iff hn hk0).1, (reconLabel_le_zero_iff (C := blockOffsets φ a) hn hk'.2).1]
    omega
  · have h3 := three_le_reconLabel hn hC hk'.1
    rcases hk with hk | hk
    · have := (reconLabel_le_zero_iff (C := blockOffsets φ a) hn hk.2).2
      omega
    · have hlt : blockOffsets φ a 0 < ((k : ℝ) + θ) / n := by
        have := cell_left_lt_right hn θ k
        linarith [hk.1, blockOffsets_zero φ a, blockOffsets_one φ a]
      have hlt' : blockOffsets φ a 0 < ((k' : ℝ) + θ) / n := by
        have := cell_left_lt_right hn θ k'
        linarith [hk'.1, blockOffsets_zero φ a, blockOffsets_one φ a]
      rw [reconLabel_of_lt hlt, reconLabel_of_lt hlt']
      omega

theorem reconLabel_strictMonoOn (ha : 0 < a) (hn : 0 < n) :
    StrictMonoOn (reconLabel n θ (blockOffsets φ a)) {k | NegGood φ a L n θ k ∨ PosGood φ a L n θ k} :=
  fun _ hk _ hk' hkk => reconLabel_lt_reconLabel ha hn hk hk' hkk

/-- A good cell of the negative block and a good cell of the positive block are at least two labels apart, once
`n (C₊ - C₋) ≥ 1`. -/
theorem two_le_sub_of_neg_pos (hn : 0 < n) (hgap : 1 ≤ (n : ℝ) * (φ.symm a - φ.symm (-a))) {k k' : ℤ}
    (hk : NegGood φ a L n θ k) (hk' : PosGood φ a L n θ k') : 2 ≤ k' - k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := hk.2
  have h2 := hk'.1
  rw [div_le_iff₀ hn'] at h1
  rw [le_div_iff₀ hn'] at h2
  have : (2 : ℝ) ≤ (k' : ℝ) - k := by nlinarith
  exact_mod_cast this

/-- The synthetic labels of a good cell of the negative block and of the positive block are at least three apart. -/
theorem three_le_reconLabel_sub (ha : 0 < a) (hn : 0 < n) {k k' : ℤ} (hk : NegGood φ a L n θ k)
    (hk' : PosGood φ a L n θ k') :
    3 ≤ reconLabel n θ (blockOffsets φ a) k' - reconLabel n θ (blockOffsets φ a) k := by
  have := (reconLabel_le_zero_iff (C := blockOffsets φ a) hn hk.2).2
  have := three_le_reconLabel hn (blockOffsets_lt φ ha) hk'.1
  omega

/-- On good cells of the same block the synthetic labels differ by the true labels. -/
theorem reconLabel_sub_of_same (ha : 0 < a) (hn : 0 < n) {k k' : ℤ}
    (h : (NegGood φ a L n θ k ∧ NegGood φ a L n θ k') ∨ (PosGood φ a L n θ k ∧ PosGood φ a L n θ k')) :
    reconLabel n θ (blockOffsets φ a) k' - reconLabel n θ (blockOffsets φ a) k = k' - k := by
  rcases h with ⟨hk, hk'⟩ | ⟨hk, hk'⟩
  · rw [(reconLabel_le_zero_iff (C := blockOffsets φ a) hn hk.2).1,
      (reconLabel_le_zero_iff (C := blockOffsets φ a) hn hk'.2).1]
    ring
  · have hlt : ∀ {j : ℤ}, PosGood φ a L n θ j → blockOffsets φ a 0 < ((j : ℝ) + θ) / n := fun {j} hj => by
      have := cell_left_lt_right hn θ j
      have := blockOffsets_lt φ ha
      linarith [hj.1, blockOffsets_zero φ a, blockOffsets_one φ a]
    rw [reconLabel_of_lt (hlt hk), reconLabel_of_lt (hlt hk')]
    ring

theorem one_div_mul_add_div (n : ℕ) (θ x : ℝ) : 1 / (n : ℝ) * x + θ / n = (x + θ) / n := by
  rw [one_div_mul_eq_div, ← add_div]

omit [IsFiniteMeasureOnCompacts μ] in
/-- The true multiplicity of two separated cells is the frontier-side count of `e` at the Lebesgue times of the
cells. -/
theorem phaseData_snd_eq_cellSideCount (hp : IsMassParam e ξ φ μ) (hn : 0 < n) {k k' : ℤ}
    (hne : k ≠ k') (h1 : |k - k'| ≠ 1) :
    (phaseData n θ ξ).2 k k' =
      cellSideCount (φ ((((min k k' : ℤ) : ℝ) - 1 + θ) / n)) (φ ((((min k k' : ℤ) : ℝ) + θ) / n))
        (φ ((((max k k' : ℤ) : ℝ) - 1 + θ) / n)) (φ ((((max k k' : ℤ) : ℝ) + θ) / n)) ⇑e := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let τ : ℝ ≃o ℝ := (OrderIso.addRight (θ / n)).trans φ
  have hτ : ∀ t, τ t = φ (t + θ / n) := fun t => rfl
  have hg : (fun t => ξ (t + θ / n)) = ⇑e ∘ τ := by
    funext t
    rw [Function.comp_apply, hτ, hp.comp]
  simp only [phaseData]
  rw [cellSideMult, ite_eq_right (by
    rintro (h | h)
    · exact (not_le.2 (one_div_pos.2 hn')) h
    · exact hne h), ite_eq_right h1, hg, cellSideCount_comp_orderIso]
  simp only [hτ, one_div_mul_add_div]

/-- The synthetic multiplicity of two good cells is their true multiplicity. -/
theorem reconData_snd_reconLabel (hp : IsMassParam e ξ φ μ) (ha : 0 < a) (haL : a < L) (hδ : 0 < δ)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hn : 0 < n)
    (hgap : 1 ≤ (n : ℝ) * (φ.symm a - φ.symm (-a))) {k k' : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) (hk' : NegGood φ a L n θ k' ∨ PosGood φ a L n θ k') :
    (reconData a L M n e (μ.restrict (offsetOuterAnnulus δ M)) (offsetResiduesOf n θ (blockOffsets φ a))).2
      (reconLabel n θ (blockOffsets φ a) k) (reconLabel n θ (blockOffsets φ a) k') = (phaseData n θ ξ).2 k k' := by
  simp only [reconData]
  rw [ite_eq_left ⟨reconValid_of_good hp ha haL hδ hE hn hk, reconValid_of_good hp ha haL hδ hE hn hk'⟩]
  -- the diagonal
  rcases eq_or_ne k k' with rfl | hne
  · rw [ite_eq_left rfl]
    simp [phaseData, cellSideMult]
  have hfne : reconLabel n θ (blockOffsets φ a) k ≠ reconLabel n θ (blockOffsets φ a) k' :=
    fun h => hne ((reconLabel_strictMonoOn ha hn).injOn hk hk' h)
  rw [ite_eq_right hfne]
  -- the differences of the labels
  have hdiff : (|k - k'| = 1 ↔
      |reconLabel n θ (blockOffsets φ a) k - reconLabel n θ (blockOffsets φ a) k'| = 1) := by
    rcases hk with hk | hk <;> rcases hk' with hk' | hk'
    · rw [show reconLabel n θ (blockOffsets φ a) k - reconLabel n θ (blockOffsets φ a) k' = k - k' from
        reconLabel_sub_of_same (L := L) ha hn (Or.inl ⟨hk', hk⟩)]
    · have h2 := two_le_sub_of_neg_pos hn hgap hk hk'
      have h3 := three_le_reconLabel_sub ha hn hk hk'
      constructor <;> intro h <;> exfalso
      · rw [abs_eq (by norm_num)] at h; omega
      · rw [abs_eq (by norm_num)] at h; omega
    · have h2 := two_le_sub_of_neg_pos hn hgap hk' hk
      have h3 := three_le_reconLabel_sub ha hn hk' hk
      constructor <;> intro h <;> exfalso
      · rw [abs_eq (by norm_num)] at h; omega
      · rw [abs_eq (by norm_num)] at h; omega
    · rw [show reconLabel n θ (blockOffsets φ a) k - reconLabel n θ (blockOffsets φ a) k' = k - k' from
        reconLabel_sub_of_same (L := L) ha hn (Or.inr ⟨hk', hk⟩)]
  by_cases h1 : |reconLabel n θ (blockOffsets φ a) k - reconLabel n θ (blockOffsets φ a) k'| = 1
  · rw [ite_eq_left h1]
    have h1' := hdiff.2 h1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [phaseData]
    rw [cellSideMult, ite_eq_right (by
      rintro (h | h)
      · exact (not_le.2 (one_div_pos.2 hn')) h
      · exact hne h), ite_eq_left h1']
  · rw [ite_eq_right h1, phaseData_snd_eq_cellSideCount hp hn hne (fun h => h1 (hdiff.1 h))]
    -- the endpoints of the synthetic cells
    have hmin : min (reconLabel n θ (blockOffsets φ a) k) (reconLabel n θ (blockOffsets φ a) k') =
        reconLabel n θ (blockOffsets φ a) (min k k') := by
      rcases le_total k k' with h | h
      · rw [min_eq_left h, min_eq_left ((reconLabel_strictMonoOn ha hn).monotoneOn hk hk' h)]
      · rw [min_eq_right h, min_eq_right ((reconLabel_strictMonoOn ha hn).monotoneOn hk' hk h)]
    have hmax : max (reconLabel n θ (blockOffsets φ a) k) (reconLabel n θ (blockOffsets φ a) k') =
        reconLabel n θ (blockOffsets φ a) (max k k') := by
      rcases le_total k k' with h | h
      · rw [max_eq_right h, max_eq_right ((reconLabel_strictMonoOn ha hn).monotoneOn hk hk' h)]
      · rw [max_eq_left h, max_eq_left ((reconLabel_strictMonoOn ha hn).monotoneOn hk' hk h)]
    have hgmin : NegGood φ a L n θ (min k k') ∨ PosGood φ a L n θ (min k k') := by
      rcases le_total k k' with h | h
      · rw [min_eq_left h]; exact hk
      · rw [min_eq_right h]; exact hk'
    have hgmax : NegGood φ a L n θ (max k k') ∨ PosGood φ a L n θ (max k k') := by
      rcases le_total k k' with h | h
      · rw [max_eq_right h]; exact hk'
      · rw [max_eq_left h]; exact hk
    rw [hmin, hmax, (reconTime_reconLabel hp ha haL hδ hE hn hgmin).1,
      (reconTime_reconLabel hp ha haL hδ hE hn hgmin).2, (reconTime_reconLabel hp ha haL hδ hE hn hgmax).1,
      (reconTime_reconLabel hp ha haL hδ hE hn hgmax).2]
    -- increasing endpoints
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsep : (min k k' : ℤ) + 2 ≤ max k k' := by
      have : |k - k'| ≠ 1 := fun h => h1 (hdiff.1 h)
      rcases le_total k k' with h | h
      · rw [min_eq_left h, max_eq_right h]
        rw [abs_sub_comm, abs_of_nonneg (by omega)] at this
        omega
      · rw [min_eq_right h, max_eq_left h]
        rw [abs_of_nonneg (by omega)] at this
        omega
    have hsep' : ((min k k' : ℤ) : ℝ) + 2 ≤ ((max k k' : ℤ) : ℝ) := by exact_mod_cast hsep
    unfold cellSideCountInc
    rw [ite_eq_left ⟨φ.lt_iff_lt.2 (cell_left_lt_right hn θ _), φ.lt_iff_lt.2 (div_lt_div_of_pos_right
      (by linarith) hn'), φ.lt_iff_lt.2 (cell_left_lt_right hn θ _)⟩]

/-! ### The cells near the annulus are good, for large `n` -/

/-- The window of quantum times. -/
def quantumWindow (φ : ℝ ≃o ℝ) (L : ℝ) : Set ℝ := Icc (φ.symm (-L) - 2) (φ.symm L + 2)

/-- The conditions on the mesh `1/n`: `φ` and `ξ` move by less than `a` and `α/4` over quantum time `1/n` in the
window, and `n (C₊ - C₋) ≥ 1`. -/
structure MeshFine (φ : ℝ ≃o ℝ) (ξ : C(ℝ, ℂ)) (α a L : ℝ) (n : ℕ) : Prop where
  pos : 0 < n
  le_one : 1 / (n : ℝ) ≤ 1
  gap : 1 ≤ (n : ℝ) * (φ.symm a - φ.symm (-a))
  clock : ∀ s ∈ quantumWindow φ L, ∀ s' ∈ quantumWindow φ L, |s - s'| ≤ 1 / n → |φ s - φ s'| < a
  curve : ∀ s ∈ quantumWindow φ L, ∀ s' ∈ quantumWindow φ L, |s - s'| ≤ 1 / n → ‖ξ s - ξ s'‖ < α / 4

theorem eventually_meshFine (hα : 0 < α) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, MeshFine φ ξ α a L n := by
  have hK : IsCompact (quantumWindow φ L) := isCompact_Icc
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous φ.continuous.continuousOn) a ha
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous ξ.continuous.continuousOn) (α / 4) (by positivity)
  have hC : 0 < φ.symm a - φ.symm (-a) := sub_pos.2 (φ.symm.lt_iff_lt.2 (by linarith))
  have hsmall : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < ρ := fun ρ hρ =>
    ((tendsto_one_div_atTop_nhds_zero_nat).eventually (gt_mem_nhds hρ))
  have hbig : ∀ᶠ n : ℕ in atTop, 1 / (φ.symm a - φ.symm (-a)) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop 0, hsmall ρ₁ hρ₁, hsmall ρ₂ hρ₂, hsmall 1 one_pos, hbig] with
    n hn h1 h2 h3 h4
  refine ⟨hn, h3.le, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hC] at h4
    linarith
  · intro s hs s' hs' hss
    have := h₁ s hs s' hs' (by rw [Real.dist_eq]; linarith)
    rwa [Real.dist_eq] at this
  · intro s hs s' hs' hss
    have := h₂ s hs s' hs' (by rw [Real.dist_eq]; linarith)
    rwa [dist_eq_norm] at this

omit [IsFiniteMeasureOnCompacts μ] in
/-- **A cell containing a point of norm between `α/2` and `2R` is good**, on a fine mesh. -/
theorem good_of_mem_cell (hp : IsMassParam e ξ φ μ) (hα : 0 < α) (ha : 0 < a) (haL : 4 * a < L)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hfine : MeshFine φ ξ α a L n) {k : ℤ} {s : ℝ}
    (hs : s ∈ Icc (((k : ℝ) - 1 + θ) / n) (((k : ℝ) + θ) / n)) (h1 : α / 2 ≤ ‖ξ s‖) (h2 : ‖ξ s‖ ≤ 2 * R) :
    NegGood φ a L n θ k ∨ PosGood φ a L n θ k := by
  obtain ⟨hE1, hE2, -⟩ := hE
  have hn := hfine.pos
  set t := φ s with ht
  have het : ξ s = e t := hp.comp s
  -- `2a < |t| < L/2`
  have ht1 : 2 * a < |t| := by
    by_contra h
    rw [not_lt] at h
    have hmem := hE1 (abs_le.1 h)
    rw [mem_ball_zero_iff, ← het] at hmem
    linarith
  have ht2 : |t| < L / 2 := by
    by_contra h
    rw [not_lt] at h
    obtain ⟨m, hm⟩ := exists_nat_ge |t|
    have hmem : t ∈ Icc (L / 2) (L / 2 + m) ∪ Icc (-(L / 2) - m) (-(L / 2)) := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0] at h hm
        exact Or.inl ⟨h, by linarith⟩
      · rw [abs_of_neg h0] at h hm
        exact Or.inr ⟨by linarith, by linarith⟩
    have := hE2 m hmem
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, ← het] at this
    linarith
  -- the cell lies in the window
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcell : (((k : ℝ) + θ) / n) - (((k : ℝ) - 1 + θ) / n) = 1 / n := by field_simp; ring
  have hsW : s ∈ Ioo (φ.symm (-(L / 2))) (φ.symm (L / 2)) := by
    rw [ht] at ht2
    refine ⟨?_, ?_⟩
    · rw [← φ.lt_iff_lt, φ.apply_symm_apply]; linarith [neg_abs_le (φ s)]
    · rw [← φ.lt_iff_lt, φ.apply_symm_apply]; linarith [le_abs_self (φ s)]
  have hL2 : φ.symm (-L) < φ.symm (-(L / 2)) := φ.symm.lt_iff_lt.2 (by linarith)
  have hL3 : φ.symm (L / 2) < φ.symm L := φ.symm.lt_iff_lt.2 (by linarith)
  have hle1 := hfine.le_one
  have hW : ∀ u ∈ Icc (((k : ℝ) - 1 + θ) / n) (((k : ℝ) + θ) / n), u ∈ quantumWindow φ L := by
    intro u hu
    refine ⟨?_, ?_⟩ <;> linarith [hs.1, hs.2, hu.1, hu.2, hsW.1, hsW.2]
  have hd : ∀ u ∈ Icc (((k : ℝ) - 1 + θ) / n) (((k : ℝ) + θ) / n), |φ u - t| < a := fun u hu =>
    hfine.clock u (hW u hu) s (hW s hs) (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hs.1, hs.2])
  have hl := hd _ ⟨le_rfl, (cell_left_lt_right hn θ k).le⟩
  have hr := hd _ ⟨(cell_left_lt_right hn θ k).le, le_rfl⟩
  rw [abs_lt] at hl hr
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht1 ht2
    right
    refine ⟨?_, ?_⟩
    · rw [← φ.le_iff_le, φ.apply_symm_apply]; linarith
    · rw [← φ.lt_iff_lt, φ.apply_symm_apply]; linarith
  · rw [abs_of_neg h0] at ht1 ht2
    left
    refine ⟨?_, ?_⟩
    · rw [← φ.lt_iff_lt, φ.apply_symm_apply]; linarith
    · rw [← φ.le_iff_le, φ.apply_symm_apply]; linarith

/-- A good cell lies in the window. -/
theorem mem_quantumWindow_of_good (ha : 0 < a) (haL : a < L) {k : ℤ}
    (hk : NegGood φ a L n θ k ∨ PosGood φ a L n θ k) {u : ℝ}
    (hu : u ∈ Icc (((k : ℝ) - 1 + θ) / n) (((k : ℝ) + θ) / n)) : u ∈ quantumWindow φ L := by
  have h1 : φ.symm (-L) < φ.symm (-a) := φ.symm.lt_iff_lt.2 (by linarith)
  have h2 : φ.symm (-a) < φ.symm a := φ.symm.lt_iff_lt.2 (by linarith)
  have h3 : φ.symm a < φ.symm L := φ.symm.lt_iff_lt.2 (by linarith)
  rcases hk with hk | hk <;> exact ⟨by linarith [hk.1, hk.2, hu.1, hu.2], by linarith [hk.1, hk.2, hu.1, hu.2]⟩

omit [IsFiniteMeasureOnCompacts μ] in
/-- **The local vertices of the true data are good cells**, on a fine mesh. -/
theorem good_of_mem_localVertices (hp : IsMassParam e ξ φ μ) (hα : 0 < α) (ha : 0 < a) (haL : 4 * a < L)
    (hE : e ∈ ReconCurveEvent α R a L δ M) (hfine : MeshFine φ ξ α a L n) {k : ℤ}
    (hk : k ∈ localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (phaseData n θ ξ)) :
    NegGood φ a L n θ k ∨ PosGood φ a L n θ k := by
  have hn := hfine.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hvert : ∀ j : ℤ, (phaseData n θ ξ).1 j ∈ ball (0 : ℂ) R \ closedBall (0 : ℂ) α →
      NegGood φ a L n θ j ∨ PosGood φ a L n θ j := fun j hj => by
    simp only [phaseData, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le] at hj
    exact good_of_mem_cell hp hα ha haL hE hfine ⟨(cell_left_lt_right hn θ j).le, le_rfl⟩
      (by linarith) (by linarith)
  rcases (mem_localVertices_iff.1 hk) with hk | ⟨x, hx, hxk⟩
  · exact hvert k hk
  · have hgx := hvert x hx
    simp only [phaseData] at hxk
    obtain ⟨z, ⟨u, hu, rfl⟩, ⟨u', hu', hzu⟩⟩ := cellSideMult_ne_zero_inter_nonempty hxk
    simp only at hzu
    have hshift : ∀ (j : ℤ) {v : ℝ}, v ∈ Icc (1 / (n : ℝ) * ((j : ℝ) - 1)) (1 / (n : ℝ) * j) →
        v + θ / n ∈ Icc (((j : ℝ) - 1 + θ) / n) (((j : ℝ) + θ) / n) := fun j v hv => by
      rw [one_div_mul_eq_div, one_div_mul_eq_div] at hv
      refine ⟨?_, ?_⟩
      · rw [add_div]; linarith [hv.1]
      · rw [add_div]; linarith [hv.2]
    have hux := hshift x hu
    have huk := hshift k hu'
    -- the common point is close to the vertex of `x`
    have hxv := hx
    simp only [phaseData, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le] at hxv
    have hcx : ((x : ℝ) + θ) / n - ((x : ℝ) - 1 + θ) / n = 1 / n := by field_simp; ring
    have hcl := hfine.curve _ (mem_quantumWindow_of_good ha (by linarith) hgx hux) _
      (mem_quantumWindow_of_good ha (by linarith) hgx ⟨(cell_left_lt_right hn θ x).le, le_rfl⟩)
      (by rw [abs_le]; constructor <;> linarith [hux.1, hux.2, (cell_left_lt_right hn θ x)])
    have hnorm1 : α / 2 ≤ ‖ξ (u' + θ / n)‖ := by
      rw [hzu]
      have := norm_sub_norm_le (ξ (((x : ℝ) + θ) / n)) (ξ (u + θ / n))
      rw [norm_sub_rev] at this
      linarith [hxv.2]
    have hnorm2 : ‖ξ (u' + θ / n)‖ ≤ 2 * R := by
      rw [hzu]
      have := norm_le_norm_add_norm_sub' (ξ (u + θ / n)) (ξ (((x : ℝ) + θ) / n))
      linarith [hxv.1]
    exact good_of_mem_cell hp hα ha haL hE hfine huk hnorm1 hnorm2

/-! ### The reconstruction -/

theorem residuePair_offsetResidues (n : ℕ) (θ : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (a δ M : ℝ) :
    residuePair (offsetResidues n θ e μ a δ M) = offsetResiduesOf n θ (quantumTimeOffsets e μ a) := by
  funext i
  fin_cases i <;> rfl

theorem coneRecon_offsetResidues (α R a L M : ℝ) (n : ℕ) (θ : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (δ : ℝ) :
    coneRecon α R a L M n (offsetResidues n θ e μ a δ M) =
      localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
        (reconData a L M n e (μ.restrict (offsetOuterAnnulus δ M))
          (offsetResiduesOf n θ (quantumTimeOffsets e μ a))) := by
  rw [coneRecon, residuePair_offsetResidues]
  rfl

/-- **The reconstruction recovers the local configuration**: for a curve `e` in the curve event and a curve `ξ = e ∘ φ`
parametrized by the mass of a locally finite measure `μ`, for every phase `θ`, for all large `n` the local
configuration near `B_R(0) \ closedBall 0 α` of the true data at mesh `1/n` with phase `θ` is `coneRecon` of the outer
data and the residues. -/
theorem eventually_localConfig_eq_coneRecon (hα : 0 < α) (ha : 0 < a) (haL : 4 * a < L)
    (hδ : 0 < δ) (hp : IsMassParam e ξ φ μ) (hE : e ∈ ReconCurveEvent α R a L δ M) (θ : ℝ) :
    ∀ᶠ n : ℕ in atTop, localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (phaseData n θ ξ) =
      coneRecon α R a L M n (offsetResidues n θ e μ a δ M) := by
  have haL' : a < L := by linarith
  filter_upwards [eventually_meshFine (φ := φ) (ξ := ξ) (L := L) hα ha] with n hfine
  have hn := hfine.pos
  rw [coneRecon_offsetResidues, quantumTimeOffsets_eq hp ha]
  symm
  refine localConfig_eq_of_strictMonoOn (f := reconLabel n θ (blockOffsets φ a))
    (fun k hk k' hk' hkk => reconLabel_lt_reconLabel ha hn
      (good_of_mem_localVertices hp hα ha haL hE hfine hk)
      (good_of_mem_localVertices hp hα ha haL hE hfine hk') hkk) ?_
    (fun k hk => reconData_fst_reconLabel hp ha haL' hδ hE hn
      (good_of_mem_localVertices hp hα ha haL hE hfine hk))
    (fun k hk k' hk' => reconData_snd_reconLabel hp ha haL' hδ hE hn hfine.gap
      (good_of_mem_localVertices hp hα ha haL hE hfine hk)
      (good_of_mem_localVertices hp hα ha haL hE hfine hk'))
  -- the local vertices correspond
  set V := ball (0 : ℂ) R \ closedBall (0 : ℂ) α with hV
  set d := phaseData n θ ξ with hd
  set d' := reconData a L M n e (μ.restrict (offsetOuterAnnulus δ M))
    (offsetResiduesOf n θ (blockOffsets φ a)) with hd'
  have h0V : (0 : ℂ) ∉ V := fun h => h.2 (mem_closedBall_self hα.le)
  -- invalid synthetic labels carry the point `0` and no edges
  have hinv : ∀ ℓ, ¬ ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M))
      (offsetResiduesOf n θ (blockOffsets φ a)) ℓ → d'.1 ℓ = 0 ∧ ∀ ℓ', d'.2 ℓ' ℓ = 0 := fun ℓ hℓ => by
    refine ⟨by simp only [hd', reconData, ite_eq_right hℓ], fun ℓ' => ?_⟩
    simp only [hd', reconData]
    rw [ite_eq_right (fun h => hℓ h.2)]
  have hgood : ∀ k, NegGood φ a L n θ k ∨ PosGood φ a L n θ k →
      (k ∈ localVertices V d ↔ reconLabel n θ (blockOffsets φ a) k ∈ localVertices V d') := by
    intro k hk
    rw [mem_localVertices_iff, mem_localVertices_iff,
      reconData_fst_reconLabel hp ha haL' hδ hE hn hk]
    constructor
    · rintro (h | ⟨x, hx, hxk⟩)
      · exact Or.inl h
      · have hgx := good_of_mem_localVertices hp hα ha haL hE hfine (mem_localVertices_iff.2 (Or.inl hx))
        refine Or.inr ⟨reconLabel n θ (blockOffsets φ a) x, ?_, ?_⟩
        · rw [reconData_fst_reconLabel hp ha haL' hδ hE hn hgx]; exact hx
        · rw [reconData_snd_reconLabel hp ha haL' hδ hE hn hfine.gap hgx hk]; exact hxk
    · rintro (h | ⟨y, hy, hyk⟩)
      · exact Or.inl h
      · by_cases hyv : ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M))
          (offsetResiduesOf n θ (blockOffsets φ a)) y
        · obtain ⟨x, hgx, rfl⟩ := exists_good_of_reconValid hp ha haL' hδ hE hn hyv
          rw [reconData_fst_reconLabel hp ha haL' hδ hE hn hgx] at hy
          rw [reconData_snd_reconLabel hp ha haL' hδ hE hn hfine.gap hgx hk] at hyk
          exact Or.inr ⟨x, hy, hyk⟩
        · exact absurd ((hinv y hyv).1 ▸ hy) h0V
  ext ℓ
  constructor
  · intro hℓ
    by_cases hv : ReconValid a L M n e (μ.restrict (offsetOuterAnnulus δ M))
      (offsetResiduesOf n θ (blockOffsets φ a)) ℓ
    · obtain ⟨k, hk, rfl⟩ := exists_good_of_reconValid hp ha haL' hδ hE hn hv
      exact ⟨k, (hgood k hk).2 hℓ, rfl⟩
    · exfalso
      rcases mem_localVertices_iff.1 hℓ with h | ⟨y, -, hy⟩
      · exact h0V ((hinv ℓ hv).1 ▸ h)
      · exact hy ((hinv ℓ hv).2 y)
  · rintro ⟨k, hk, rfl⟩
    exact (hgood k (good_of_mem_localVertices hp hα ha haL hE hfine hk)).1 hk

end Deterministic

end MatedCRT
