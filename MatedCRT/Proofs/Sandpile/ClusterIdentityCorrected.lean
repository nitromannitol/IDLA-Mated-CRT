import MatedCRT.Proofs.Sandpile.Connectivity

/-! The cluster identity, corrected paper equation `eq:cluster-definition`, line 1721. -/

namespace MatedCRT.Sandpile

open Set

/-- If the initial mass exceeds one, the source topples and the cluster is the
vertex closure of the support of the normalized odometer. -/
theorem cluster_eq_closure_of_one_lt {m : ℤ → ℤ → ℕ} {M : ℝ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) (hM : 1 < M) :
    sandpileCluster m M = vClosure m (Function.support (sandpileNormOdometer m M)) := by
  rw [cluster_eq_insert_closure hlf hsymm hloop hdeg hne (by linarith : 0 < M)]
  exact Set.insert_eq_of_mem (Or.inl (origin_mem_odometer_support hlf hne (hdeg 0) hM))

/-- Equation `eq:cluster-and-lambdat` (paper line 1874), conditional on
agreement of the stopped and global positive odometer sets. -/
theorem cluster_eq_closure_of_consistency {m : ℤ → ℤ → ℕ} {M : ℝ} {Λ : Set ℤ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m M).Nonempty) (hM : 1 < M)
    (hconsistency : Function.support (sandpileNormOdometer m M) = Λ) :
    sandpileCluster m M = vClosure m Λ := by
  rw [← hconsistency]
  exact cluster_eq_closure_of_one_lt hlf hsymm hloop hdeg hne hM

/-- Equation `eq:cluster-definition` at the paper's mass `t / ε`, for `ε < t`
(corrected paper lines 1719–1724). -/
theorem cluster_eq_closure_of_mesh_lt_time {m : ℤ → ℤ → ℕ} {ε t : ℝ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (admissible m (t / ε)).Nonempty) (hε : 0 < ε) (hεt : ε < t) :
    sandpileCluster m (t / ε) = vClosure m (Function.support (sandpileNormOdometer m (t / ε))) := by
  apply cluster_eq_closure_of_one_lt hlf hsymm hloop hdeg hne
  exact (one_lt_div hε).2 hεt

end MatedCRT.Sandpile
