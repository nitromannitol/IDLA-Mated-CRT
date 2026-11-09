import MatedCRT.FirstPass.S4S6c.NextExitStop

/-!
# LEMMA68 N3c: the next exit time is a stopping time (q2, task fp-S4S6c; write-up C1-C3)

For a stopping time `T` (the start of the current test) and a state-dependent region `W (x T)` (the disk of the test, a function of
the state at `T`), the next exit time is `T_next = T + vExitTime (W (x T)) (pathShift T x)` (write-up C1, eq (27)).
* `determinacy_of_pathHist_set`: a stopping set `{T = j} = {pathHist j ∈ G}` is determined by `pathHist k` for `k ≥ j`;
* `nextExitTime_determinacy`: `{T_next = k}` is determined by `pathHist k`;
* `nextExitTime_stop`: `{T_next = k} = {pathHist k ∈ F}` with `F` measurable, the stopping property required by
  `srwLaw_successive_tests_le_pow` (hstop).
-/

open MeasureTheory Set

namespace MatedCRT

open WalkPotential

namespace NextExitTime

/-- The next exit time after `T`, from the region `W (x T)` of the state at `T`. -/
noncomputable def nextExitTime (T : (ℕ → ℤ) → ℕ) (W : ℤ → Set ℤ) (x : ℕ → ℤ) : ℕ∞ :=
  (T x : ℕ∞) + vExitTime (W (x (T x))) (pathShift (T x) x)

/-- A stopping set `{T = j} = {pathHist j ∈ G}` is determined by the history up to any `k ≥ j`. -/
theorem determinacy_of_pathHist_set (T : (ℕ → ℤ) → ℕ) {j k : ℕ} {G : Set (Fin (j + 1) → ℤ)}
    (hG : {x | T x = j} = {x | pathHist j x ∈ G}) (hjk : j ≤ k) (x y : ℕ → ℤ)
    (hxy : pathHist k x = pathHist k y) : T x = j ↔ T y = j := by
  have hres : pathHist j x = pathHist j y := by
    funext i
    have := congrFun hxy ⟨i.1, by omega⟩
    simpa [pathHist] using this
  have h1 : T x = j ↔ pathHist j x ∈ G := by
    have := Set.ext_iff.1 hG x
    simpa using this
  have h2 : T y = j ↔ pathHist j y ∈ G := by
    have := Set.ext_iff.1 hG y
    simpa using this
  rw [h1, h2, hres]

/-- The next exit time is determined by the history up to time `k`. -/
theorem nextExitTime_determinacy (T : (ℕ → ℤ) → ℕ) (W : ℤ → Set ℤ)
    (hT : ∀ j k : ℕ, j ≤ k → ∀ x y : ℕ → ℤ, pathHist k x = pathHist k y → (T x = j ↔ T y = j))
    (k : ℕ) (x y : ℕ → ℤ) (hxy : pathHist k x = pathHist k y)
    (hx : nextExitTime T W x = (k : ℕ∞)) : nextExitTime T W y = (k : ℕ∞) := by
  unfold nextExitTime at hx ⊢
  have hfin : vExitTime (W (x (T x))) (pathShift (T x) x) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hx
    exact ENat.natCast_ne_top k hx.symm
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hm] at hx
  have hsum : T x + m = k := by exact_mod_cast hx
  have hjk : T x ≤ k := by omega
  have hTy : T y = T x := (hT (T x) k hjk x y hxy).1 rfl
  have hxj : x (T x) = y (T x) := by
    have := congrFun hxy ⟨T x, by omega⟩
    simpa [pathHist] using this
  have hV : vExitTime (W (x (T x))) (pathShift (T x) x) = (m : ℕ∞) := hm.symm
  have hwin : vExitTime (W (x (T x))) (pathShift (T x) y) = (m : ℕ∞) :=
    (NextExitStop.vExitTime_pathShift_congr (W (x (T x))) (by omega : T x + m ≤ k) hxy).1 hV
  rw [hTy, ← hxj, hwin]
  exact_mod_cast hsum

/-- **The stopping property of the next exit time** (write-up C1; the hypothesis `hstop` of `srwLaw_successive_tests_le_pow`):
if the current test time has the `pathHist` form, so does the next exit time. -/
theorem nextExitTime_stop (T : (ℕ → ℤ) → ℕ) (W : ℤ → Set ℤ)
    (hTF : ∀ j : ℕ, ∃ G : Set (Fin (j + 1) → ℤ), MeasurableSet G ∧ {x | T x = j} = {x | pathHist j x ∈ G})
    (k : ℕ) : ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      {x | nextExitTime T W x = (k : ℕ∞)} = {x | pathHist k x ∈ F} := by
  have hT : ∀ j k : ℕ, j ≤ k → ∀ x y : ℕ → ℤ, pathHist k x = pathHist k y → (T x = j ↔ T y = j) := by
    intro j k hjk x y hxy
    obtain ⟨G, _, hG⟩ := hTF j
    exact determinacy_of_pathHist_set T hG hjk x y hxy
  refine NextExitStop.exists_pathHist_of_determinacy k (fun x => nextExitTime T W x = (k : ℕ∞)) ?_
  intro x y hxy
  exact ⟨nextExitTime_determinacy T W hT k x y hxy, nextExitTime_determinacy T W hT k y x hxy.symm⟩

#print axioms MatedCRT.NextExitTime.nextExitTime_stop

end NextExitTime

end MatedCRT
