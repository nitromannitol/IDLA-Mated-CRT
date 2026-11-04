import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-! # The source vertex in the discrete Green kernel -/

namespace MatedCRT

open Set Filter Topology

/-- If the curve has not visited the origin by time `-ε`, the least-index cell
containing the origin is cell zero. This is a deterministic sufficient condition;
the area-parametrization hypotheses alone do not assert it. -/
theorem vertexOf_zero_eq_zero_of_no_visit_before_mesh {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hzero : η 0 = 0) (hno : ∀ s ≤ -ε, η s ≠ 0) :
    vertexOf ε η 0 = 0 := by
  unfold vertexOf
  apply IsLeast.csInf_eq
  constructor
  · change (0 : ℂ) ∈ cell ε η 0
    exact ⟨0, by simp [hε.le], hzero⟩
  · intro k hk
    by_contra hn
    have hkneg : k < 0 := lt_of_not_ge hn
    obtain ⟨s, hs, hszero⟩ := hk
    have hkint : k ≤ -1 := by omega
    have hkreal : (k : ℝ) ≤ -1 := by exact_mod_cast hkint
    have hsneg : s ≤ -ε := by nlinarith [hs.2]
    exact hno s hsneg hszero

/-- In particular, no earlier return to the origin identifies the sources at
every positive mesh. -/
theorem vertexOf_zero_eq_zero_of_no_earlier_visit {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hzero : η 0 = 0) (hno : ∀ s < 0, η s ≠ 0) :
    vertexOf ε η 0 = 0 :=
  vertexOf_zero_eq_zero_of_no_visit_before_mesh hε hzero
    (fun s hs => hno s (lt_of_le_of_lt hs (neg_neg_of_pos hε)))

/-- For a continuous proper curve, the no-visit condition is also necessary:
an earlier visit belongs to a negative-index cell. -/
theorem vertexOf_zero_eq_zero_iff_no_visit_before_mesh {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hzero : η 0 = 0) :
    vertexOf ε η 0 = 0 ↔ ∀ s ≤ -ε, η s ≠ 0 := by
  constructor
  · intro hv s hs hszero
    have hfinite : {k : ℤ | (0 : ℂ) ∈ cell ε η k}.Finite :=
      (Tightness.cellVertices_finite hη hp hε
        (Bornology.isBounded_singleton (x := (0 : ℂ)))).subset
        (fun k hk => ⟨0, hk, rfl⟩)
    have hmem : (⌈s / ε⌉ : ℤ) ∈ {k : ℤ | (0 : ℂ) ∈ cell ε η k} := by
      simpa [hszero] using Tightness.mem_cell_ceil (η := η) hε s
    have hle : vertexOf ε η 0 ≤ ⌈s / ε⌉ := csInf_le hfinite.bddBelow hmem
    have hceil : (⌈s / ε⌉ : ℤ) ≤ -1 := by
      apply Int.ceil_le.mpr
      have : s / ε ≤ -1 := (div_le_iff₀ hε).2 (by linarith)
      simpa using this
    rw [hv] at hle
    omega
  · exact vertexOf_zero_eq_zero_of_no_visit_before_mesh hε hzero

/-- Identification of the sources at all positive meshes is equivalent to
the curve having no negative-time visit to the origin. -/
theorem vertexOf_zero_eq_zero_all_meshes_iff_no_earlier_visit {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hzero : η 0 = 0) :
    (∀ ε : ℝ, 0 < ε → vertexOf ε η 0 = 0) ↔ ∀ s < 0, η s ≠ 0 := by
  constructor
  · intro h s hs
    have hε : 0 < -s := neg_pos.mpr hs
    have hno := (vertexOf_zero_eq_zero_iff_no_visit_before_mesh hη hp hε hzero).1 (h (-s) hε)
    exact hno s (by simp)
  · intro h ε hε
    exact vertexOf_zero_eq_zero_of_no_earlier_visit hε hzero h

end MatedCRT
