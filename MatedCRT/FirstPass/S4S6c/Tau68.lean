import MatedCRT.FirstPass.S4S6c.ConfigBound68

/-!
# The successive test times and stay sets of the printed Lemma 6.8

`ConfigBound68.trace_half` takes the successive exit times `τ` and the stay sets `S` as parameters with the recursions
`τ 0 = 0`, `τ (N+1) x = i + vExitTime (Wt (x i)) (pathShift i x)` when `τ N x = i` is finite, `τ (N+1) x = ⊤` after `⊤`,
`S 0 = univ`, `S (N+1) = S N ∩ {x | ∃ k, τ N x = k ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)}`.
This file constructs them, so that the hypotheses of `trace_half` are provable for the window family `Wt`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential SuccessiveExitStop

namespace Tau68

/-- The successive exit times of the windows `Wt` along a path. -/
noncomputable def tauSeq (Wt : ℤ → Set ℤ) : ℕ → (ℕ → ℤ) → ℕ∞
  | 0, _ => 0
  | N + 1, x => if tauSeq Wt N x = ⊤ then ⊤ else
      ((tauSeq Wt N x).toNat : ℕ∞) + vExitTime (Wt (x (tauSeq Wt N x).toNat)) (pathShift (tauSeq Wt N x).toNat x)

/-- The stay sets: paths along which every completed test stays in its region. -/
noncomputable def staySeq (Wt Aof : ℤ → Set ℤ) : ℕ → Set (ℕ → ℤ)
  | 0 => univ
  | N + 1 => staySeq Wt Aof N ∩
      {x | ∃ k : ℕ, tauSeq Wt N x = (k : ℕ∞) ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)}

theorem tauSeq_zero (Wt : ℤ → Set ℤ) (x : ℕ → ℤ) : tauSeq Wt 0 x = 0 := rfl

theorem tauSeq_succ_of_eq {Wt : ℤ → Set ℤ} {N : ℕ} {x : ℕ → ℤ} {i : ℕ} (h : tauSeq Wt N x = (i : ℕ∞)) :
    tauSeq Wt (N + 1) x = (i : ℕ∞) + vExitTime (Wt (x i)) (pathShift i x) := by
  rw [tauSeq]
  simp [h]

theorem tauSeq_succ_of_top {Wt : ℤ → Set ℤ} {N : ℕ} {x : ℕ → ℤ} (h : tauSeq Wt N x = ⊤) :
    tauSeq Wt (N + 1) x = ⊤ := by
  rw [tauSeq]
  simp [h]

theorem staySeq_zero (Wt Aof : ℤ → Set ℤ) : staySeq Wt Aof 0 = univ := rfl

theorem staySeq_succ (Wt Aof : ℤ → Set ℤ) (N : ℕ) :
    staySeq Wt Aof (N + 1) = staySeq Wt Aof N ∩
      {x | ∃ k : ℕ, tauSeq Wt N x = (k : ℕ∞) ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)} := rfl

end Tau68

end MatedCRT

#print axioms MatedCRT.Tau68.tauSeq_succ_of_eq
#print axioms MatedCRT.Tau68.tauSeq_succ_of_top
#print axioms MatedCRT.Tau68.staySeq_succ
