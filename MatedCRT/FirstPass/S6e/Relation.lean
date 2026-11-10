import Mathlib
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.FirstPass.S6e.Final

/-!
# Lemma 6.8 bridge, section 5 (fp-S6e, z9): local sparsity gives the sparsity clause (15)

Write-up (14)-(15) of Lemma 6.8 (Admissible, clause (15)): for every nonempty `B ⊆ A`, `x ≤ c_B` or `t_B < x`.
The printed Lemma 6.8 hypothesis is the local sparsity `|A ∩ V^ε(B_r(z))| < s₁ r^{2β⁻} ε⁻¹` for all `z ∈ ℂ`
(lemma:constant-order-lower-bound-div). This file shows that local sparsity at scale `r` gives (15) at `x = r`:
if `c_B < r` then `B` lies in one ball `B_r(z)` (capacity radius, `capRadius_eq_iInf_complex`), so `|B|` is below the
local bound and `t_B < r`.
-/

namespace MatedCRT

namespace Lemma68Relation

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

open Lemma68Geometry Lemma68GeometryId Lemma68Admissible

/-- Each cell is nonempty (`cell ε η k = η '' Icc (ε (k-1)) (ε k)`). -/
theorem cell_nonempty' {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty :=
  ⟨η (ε * k), ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- The capacity radius of a nonempty finite set of cells is finite. -/
theorem capRadius_ne_top {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) (B : Finset ℤ) :
    capRadius ε η B ≠ ⊤ := by
  rw [capRadius_eq_iInf_complex hη hε]
  refine ne_top_of_le_ne_top ?_ (iInf_le _ 0)
  have hfin : ∀ v : B, Metric.infEDist (0 : ℂ) (cell ε η v.1) ≠ ⊤ := fun v =>
    Metric.infEDist_ne_top (cell_nonempty' hε.le η v.1)
  exact iSup_ne_top hfin

/-- **Local sparsity gives (15).** If `B ⊆ A` is nonempty and `|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` for every `z ∈ ℂ`,
then `r ≤ c_B` or `t_B < r` (the clause (15) of `Lemma68Admissible.Admissible` at `x = r`). -/
theorem sparse15_of_local {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {A B : Finset ℤ} {r s1 βm : ℝ}
    (hs1 : 0 < s1) (hr : 0 < r) (hβ : 0 < βm) (hBne : B.Nonempty) (hBA : B ⊆ A)
    (hloc : ∀ z : ℂ, (((A : Set ℤ) ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * βm) / ε) :
    r ≤ cRad ε η B ∨ tRad ε s1 βm B < r := by
  by_cases hc : r ≤ cRad ε η B
  · exact Or.inl hc
  right
  rw [not_le] at hc
  have hlt : capRadius ε η B < ENNReal.ofReal r :=
    (ENNReal.lt_ofReal_iff_toReal_lt (capRadius_ne_top hη hε B)).2 hc
  rw [capRadius_eq_iInf_complex hη hε] at hlt
  obtain ⟨z, hz⟩ := iInf_lt_iff.1 hlt
  have hsub : (B : Set ℤ) ⊆ (A : Set ℤ) ∩ cellVertices ε η (ball z r) := by
    intro v hv
    refine ⟨hBA hv, ?_⟩
    have h1 : Metric.infEDist z (cell ε η v) < ENNReal.ofReal r :=
      lt_of_le_of_lt (le_iSup (fun w : B => Metric.infEDist z (cell ε η w.1)) ⟨v, hv⟩) hz
    obtain ⟨w, hw, hzw⟩ := Metric.infEDist_lt_iff.1 h1
    rw [edist_lt_ofReal] at hzw
    exact ⟨w, hw, by rw [mem_ball, dist_comm]; exact hzw⟩
  have hnc : ((B : Set ℤ).ncard : ℝ) ≤ (((A : Set ℤ) ∩ cellVertices ε η (ball z r)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.Finite.inter_of_left (Finset.finite_toSet A) _)
  rw [Set.ncard_coe_finset] at hnc
  have hlt2 := lt_of_le_of_lt hnc (hloc z)
  rw [lt_div_iff₀ hε] at hlt2
  have hx : (B.card : ℝ) * ε / s1 < r ^ (2 * βm) := by
    rw [div_lt_iff₀ hs1]
    nlinarith [hlt2]
  unfold tRad
  calc ((B.card : ℝ) * ε / s1) ^ (1 / (2 * βm)) < (r ^ (2 * βm)) ^ (1 / (2 * βm)) :=
        Real.rpow_lt_rpow (by positivity) hx (by positivity)
    _ = r := by
        rw [← Real.rpow_mul hr.le, mul_one_div_cancel (by positivity : (2 * βm) ≠ 0), Real.rpow_one]


/-- The cell distance to a nonempty filled set is finite. -/
theorem cellDist_ne_top {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) (k : ℤ) : cellDist ε η Θ k ≠ ⊤ := by
  obtain ⟨u₀, hu₀⟩ := cell_nonempty' hε.le η k
  have h1 : cellDist ε η Θ k ≤ Metric.infEDist u₀ (fillCells ε η (↑Θ : Set ℤ)) := by
    rw [cellDist_eq_iInf_cell hη hε]
    exact iInf₂_le u₀ hu₀
  exact ne_top_of_le_ne_top (Metric.infEDist_ne_top (x := u₀) hK) h1

/-- The maximal cell distance to a nonempty filled set is finite (the cell is compact). -/
theorem cellDistMax_ne_top {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) (k : ℤ) : cellDistMax ε η Θ k ≠ ⊤ := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hc : IsCompact (cell ε η k) := isCompact_Icc.image hη
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall k₀
  refine ne_top_of_le_ne_top (show ENNReal.ofReal R ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
  rw [cellDistMax_eq_iSup_cell hη hε]
  refine iSup₂_le fun u hu => ?_
  have hd := Metric.mem_closedBall.1 (hR hu)
  exact (Metric.infEDist_le_edist_of_mem hk₀).trans ((edist_le_ofReal (dist_nonneg.trans hd)).2 hd)

/-- Frontier cells of the middle thickening: `dd_b ≤ r/2 ≤ M_b` (write-up (4)-(5), middle boundary of Lemma 6.8). -/
theorem dd_bounds_of_frontier {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) {r : ℝ} (hr : 0 < r) {b : ℤ}
    (hb : b ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η (↑Θ : Set ℤ))))) :
    dd ε η Θ b ≤ r / 2 ∧ r / 2 ≤ ddMax ε η Θ b := by
  obtain ⟨z, hzc, hzf⟩ := hb
  rw [frontier, (isOpen_thickening).interior_eq] at hzf
  have hcl : Metric.infEDist z (fillCells ε η (↑Θ : Set ℤ)) ≤ ENNReal.ofReal (r / 2) :=
    closure_minimal (fun x hx => (Metric.mem_thickening_iff_infEDist_lt.1 hx).le)
      (isClosed_le Metric.continuous_infEDist continuous_const) hzf.1
  have hout : ENNReal.ofReal (r / 2) ≤ Metric.infEDist z (fillCells ε η (↑Θ : Set ℤ)) :=
    not_lt.1 fun h => hzf.2 (Metric.mem_thickening_iff_infEDist_lt.2 h)
  have hd : cellDist ε η Θ b ≤ ENNReal.ofReal (r / 2) := by
    rw [cellDist_eq_iInf_cell hη hε]
    exact (iInf₂_le z hzc).trans hcl
  have hM : ENNReal.ofReal (r / 2) ≤ cellDistMax ε η Θ b := by
    rw [cellDistMax_eq_iSup_cell hη hε]
    exact hout.trans (le_iSup₂ (f := fun (u : ℂ) (_ : u ∈ cell ε η b) => Metric.infEDist u (fillCells ε η (↑Θ : Set ℤ))) z hzc)
  constructor
  · exact ENNReal.toReal_le_of_le_ofReal (by linarith) hd
  · exact (ENNReal.ofReal_le_iff_le_toReal (cellDistMax_ne_top hη hε hK b)).1 hM

/-- The killed set at radius `r` is the vertex set of the thickening minus `Θ`, when `F0` contains it. -/
theorem killed_eq_W {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ F0 : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) {r : ℝ}
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ)) :
    killed ε η Θ F0 r = cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ) := by
  ext v
  rw [cellVertices_thickening_eq hη hε Θ r]
  have hfin := cellDist_ne_top hη hε hK v
  simp only [killed, dd, Set.mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe]
  rw [← ENNReal.lt_ofReal_iff_toReal_lt hfin]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hF (by rw [cellVertices_thickening_eq hη hε Θ r]; exact h1), h1, h2⟩


/-- The exit time characterisation: `n < vExitTime U x` iff the path stays in `U` up to time `n`. -/
theorem lt_vExitTime_iff' {U : Set ℤ} {x : ℕ → ℤ} {n : ℕ} :
    (n : ℕ∞) < vExitTime U x ↔ ∀ k ≤ n, x k ∈ U := by
  classical
  constructor
  · intro h k hk
    unfold vExitTime at h
    split_ifs at h with hex
    · have hnf : n < Nat.find hex := by exact_mod_cast h
      exact not_not.1 (Nat.find_min hex (lt_of_le_of_lt hk hnf))
    · exact not_not.1 (not_exists.1 hex k)
  · intro h
    exact Lemma68Final.lt_vExitTime_of_forall h

/-- `P s ≤ c` for a real bound on the finite measure `P` gives the extended bound. -/
theorem measure_le_ofReal_of_real_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {s : Set Ω} {c : ℝ} (h : P.real s ≤ c) : P s ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top P s)]
  exact ENNReal.ofReal_le_ofReal h

/-- **Admissibility at a middle-boundary start (write-up (12), (14)-(15) at `x = r`).** For a frontier vertex `b` of
`∂(Θ̄ + B_{r/2})`, with the killed set frozen at `F0 ⊇ V^ε(Θ̄ + B_r)` and the local sparsity of `A`, the
configuration `(b, Θ, F0, A)` is admissible at radius `r` with `s₁ = 1/4`. -/
theorem admissible_of_frontier {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ F0 A : Finset ℤ}
    {βm r : ℝ} {b : ℤ} (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) (hr : 0 < r) (hβ : 0 < βm)
    (hb : b ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η (↑Θ : Set ℤ)))))
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ))
    (hA : (↑A : Set ℤ) ⊆ cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ))
    (hloc : ∀ z : ℂ, (((A : Set ℤ) ∩ cellVertices ε η (ball z r)).ncard : ℝ) < (1 / 4) * r ^ (2 * βm) / ε) :
    Admissible ε η Θ F0 A b (1 / 4) βm r := by
  obtain ⟨h1, h2⟩ := dd_bounds_of_frontier hη hε hK hr hb
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [killed_eq_W hη hε hK hF]
    exact hA
  · intro B hBA hBne
    exact sparse15_of_local hη hε (by norm_num) hr hβ hBne hBA hloc

/-- **Div-level bound at a middle-boundary start (Lemma 6.8, `ConstantOrderLowerBoundDivStmt` form).** If the quenched
exit probability of the killed set `W \ Θ` satisfies the real bound `≤ 1/2` (the output of `Lemma68Final` with
`Lemma68Admissible.phi_of_real_le`), then the walk from `b` exits `W \ Θ` only through `A` with probability at most
`1 - 1/2` (the set of `ConstantOrderLowerBoundDivStmt`, with `s₂ = 1/2`). -/
theorem div_bound_of_exitQ {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {Θ F0 A : Finset ℤ}
    {r : ℝ} (P : Measure (ℕ → ℤ)) [IsFiniteMeasure P]
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty)
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ))
    (hquant : P.real (Lemma68Walk.exitEvent (Lemma68Admissible.killed ε η Θ F0 r) (↑A : Set ℤ)) ≤ 1 / 2) :
    P {x : ℕ → ℤ | ∀ n : ℕ,
        (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ)) x →
          x n ∈ (↑A : Set ℤ)} ≤ ENNReal.ofReal (1 - 1 / 2) := by
  have hset : {x : ℕ → ℤ | ∀ n : ℕ,
        (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ)) x →
          x n ∈ (↑A : Set ℤ)} =
      Lemma68Walk.exitEvent (Lemma68Admissible.killed ε η Θ F0 r) (↑A : Set ℤ) := by
    rw [killed_eq_W hη hε hK hF]
    ext x
    simp only [Set.mem_ofPred_eq, Lemma68Walk.exitEvent, lt_vExitTime_iff']
  rw [hset]
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12]
  exact measure_le_ofReal_of_real_le hquant

end Lemma68Relation

end MatedCRT
