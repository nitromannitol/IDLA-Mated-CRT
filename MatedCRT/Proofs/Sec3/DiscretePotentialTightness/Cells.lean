import MatedCRT.Defs.Map

/-!
# Cells of a continuous proper space-filling curve, and measurable proxies

Deterministic facts about the cells `H^ε_k = η([ε(k-1), εk])` of a continuous curve `η` with `η(t) → ∞` as `|t| → ∞`:

* `cellVertices_finite`: finitely many cells meet a bounded set.
* `mem_cell_vertexOf`: for a surjective curve, `x ∈ H^ε_{a^ε_x}`, so `a^ε_x` (`vertexOf`) is a genuine vertex.
* `exists_cell_near_vertexPoint`: the cells meeting a bounded set lie within `s` of their vertex point `η(εk)` for all
  small `ε`, by uniform continuity of `η` on a compact time interval.

The *proxy* of `ū^ε` near `q` at radius `r` (`proxyValue`) is the value at the first vertex `k`, in a fixed enumeration
of `ℤ`, with `η(εk) ∈ D` and `|η(εk) - q| < r` (`0` if there is none). Unlike `ū^ε(q)`, it depends on `η` only through
the points `η(εk)`, so it is `σ(h, η)`-measurable. The subsequence of Lemma 3.1 is chosen to make the proxies converge.
-/

namespace MatedCRT.Tightness

open Filter Topology Set Metric

variable {ε : ℝ} {η : ℝ → ℂ}

/-- The times at which a continuous proper curve visits a bounded set are bounded. -/
theorem exists_time_bound (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {K : Set ℂ}
    (hK : Bornology.IsBounded K) : ∃ T : ℝ, ∀ t, η t ∈ K → |t| ≤ T := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  have hc : IsCompact (η ⁻¹' closedBall 0 R) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη, hp⟩).isCompact_preimage (isCompact_closedBall 0 R)
  obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
  exact ⟨T, fun t ht => by simpa [Real.dist_eq] using hT (hR ht)⟩

/-- Finitely many cells meet a bounded set. -/
theorem cellVertices_finite (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : (cellVertices ε η K).Finite := by
  obtain ⟨T, hT⟩ := exists_time_bound hη hp hK
  refine (Set.finite_Icc (-⌈T / ε + 1⌉) ⌈T / ε + 1⌉).subset ?_
  intro k hk
  obtain ⟨z, ⟨s, hs, rfl⟩, hzK⟩ : ∃ z, z ∈ η '' Icc (ε * (k - 1)) (ε * k) ∧ z ∈ K := hk
  have hsT : |s| ≤ T := hT s hzK
  have h1 : ε * (k - 1) ≤ T := hs.1.trans ((le_abs_self s).trans hsT)
  have h2 : -T ≤ ε * k := ((neg_le_neg hsT).trans (neg_abs_le s)).trans hs.2
  have hk1 : (k : ℝ) ≤ T / ε + 1 := by
    have : (k : ℝ) - 1 ≤ T / ε := (le_div_iff₀ hε).2 (by rw [mul_comm]; exact h1)
    linarith
  have hk2 : -(T / ε + 1) ≤ (k : ℝ) := by
    have h3 : -T / ε ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by rw [mul_comm]; exact h2)
    rw [neg_div] at h3
    linarith
  have hc1 := Int.le_ceil (T / ε + 1)
  constructor
  · have : ((-⌈T / ε + 1⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast hk1.trans hc1

/-- `η(t)` lies in the cell of the vertex `⌈t/ε⌉`. -/
theorem mem_cell_ceil (hε : 0 < ε) (t : ℝ) : η t ∈ cell ε η ⌈t / ε⌉ := by
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · have h := Int.ceil_lt_add_one (t / ε)
    have h' : ((⌈t / ε⌉ : ℤ) : ℝ) - 1 < t / ε := by linarith
    rw [mul_comm]
    exact ((lt_div_iff₀ hε).1 h').le
  · rw [mul_comm]
    exact (div_le_iff₀ hε).1 (Int.le_ceil (t / ε))

/-- For a continuous, proper, surjective curve, `x` lies in the cell of `a^ε_x`. -/
theorem mem_cell_vertexOf (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : 0 < ε) (x : ℂ) : x ∈ cell ε η (vertexOf ε η x) := by
  obtain ⟨t, rfl⟩ := hsurj x
  have hne : {k : ℤ | η t ∈ cell ε η k}.Nonempty := ⟨_, mem_cell_ceil hε t⟩
  have hfin : {k : ℤ | η t ∈ cell ε η k}.Finite :=
    (cellVertices_finite hη hp hε (Bornology.isBounded_singleton (x := η t))).subset
      fun k hk => ⟨η t, hk, rfl⟩
  exact Int.csInf_mem hne hfin.bddBelow

/-- The vertex point `η(εk)` lies in the cell of `k`. -/
theorem vertexPoint_mem_cell (hε : 0 < ε) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- A vertex whose vertex point lies in `K` belongs to `V^ε(K)`. -/
theorem mem_cellVertices_of_vertexPoint_mem (hε : 0 < ε) {K : Set ℂ} {k : ℤ} (hk : vertexPoint ε η k ∈ K) :
    k ∈ cellVertices ε η K :=
  ⟨_, vertexPoint_mem_cell hε k, hk⟩

/-- **Cells are small.** For all small `ε`, every cell meeting the bounded set `K` lies within `s` of its vertex
point. -/
theorem exists_cell_near_vertexPoint (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {K : Set ℂ} (hK : Bornology.IsBounded K) {s : ℝ} (hs : 0 < s) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k ∈ cellVertices ε η K, ∀ z ∈ cell ε η k, ‖z - vertexPoint ε η k‖ < s := by
  obtain ⟨T, hT⟩ := exists_time_bound hη hp hK
  have huc : UniformContinuousOn η (Icc (-T - 1) (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hη.continuousOn
  obtain ⟨δ, hδ, hδη⟩ := Metric.uniformContinuousOn_iff.1 huc s hs
  refine ⟨min δ 1, lt_min hδ one_pos, fun ε hε hεδ k hk z hz => ?_⟩
  obtain ⟨w, ⟨t0, ht0, rfl⟩, hwK⟩ : ∃ w, w ∈ η '' Icc (ε * (k - 1)) (ε * k) ∧ w ∈ K := hk
  obtain ⟨t, ht, rfl⟩ := hz
  have hT0 := abs_le.1 (hT t0 hwK)
  have hε1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hεδ' : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hlen : ε * (k : ℝ) - ε * ((k : ℝ) - 1) = ε := by ring
  have htI : t ∈ Icc (-T - 1) (T + 1) :=
    ⟨by linarith [ht.1, ht0.2, hT0.1], by linarith [ht.2, ht0.1, hT0.2]⟩
  have hkI : ε * (k : ℝ) ∈ Icc (-T - 1) (T + 1) :=
    ⟨by linarith [ht0.2, hT0.1], by linarith [ht0.1, hT0.2]⟩
  have hd : dist t (ε * (k : ℝ)) < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have h := hδη t htI (ε * (k : ℝ)) hkI hd
  rw [dist_eq_norm] at h
  exact h

/-! ## Proxies -/

/-- A fixed enumeration of `ℤ`. -/
def intEnum (n : ℕ) : ℤ :=
  Equiv.intEquivNat.symm n

theorem intEnum_surjective : Function.Surjective intEnum :=
  Equiv.intEquivNat.symm.surjective

/-- `k` is a *proxy vertex* for `(q, r)`: `η(εk) ∈ D` and `|η(εk) - q| < r`. -/
def IsProxyVertex (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) (k : ℤ) : Prop :=
  vertexPoint ε η k ∈ D ∧ ‖vertexPoint ε η k - q‖ < r

theorem exists_proxyIndex (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) :
    ∃ n, IsProxyVertex ε η D q r (intEnum n) ∨ ∀ m, ¬ IsProxyVertex ε η D q r (intEnum m) := by
  by_cases h : ∃ n, IsProxyVertex ε η D q r (intEnum n)
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr fun m hm => h ⟨m, hm⟩⟩

/-- The index (in `intEnum`) of the first proxy vertex for `(q, r)`, or `0` if there is none. -/
noncomputable def proxyIndex (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_proxyIndex ε η D q r)

theorem proxyIndex_spec (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) :
    IsProxyVertex ε η D q r (intEnum (proxyIndex ε η D q r)) ∨ ∀ m, ¬ IsProxyVertex ε η D q r (intEnum m) :=
  @Nat.find_spec _ (Classical.decPred _) (exists_proxyIndex ε η D q r)

open Classical in
/-- The proxy of `U` near `q` at radius `r`: its value at the first proxy vertex, `0` if there is none. -/
noncomputable def proxyValue (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) (U : ℤ → ℝ) : ℝ :=
  if ∃ k, IsProxyVertex ε η D q r k then U (intEnum (proxyIndex ε η D q r)) else 0

theorem proxyValue_spec (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (q : ℂ) (r : ℝ) (U : ℤ → ℝ) :
    (∃ k, IsProxyVertex ε η D q r k ∧ proxyValue ε η D q r U = U k) ∨
      ((∀ k, ¬ IsProxyVertex ε η D q r k) ∧ proxyValue ε η D q r U = 0) := by
  by_cases h : ∃ k, IsProxyVertex ε η D q r k
  · left
    refine ⟨intEnum (proxyIndex ε η D q r), ?_, by simp only [proxyValue, h, ↓reduceIte]⟩
    rcases proxyIndex_spec ε η D q r with hs | hs
    · exact hs
    · obtain ⟨k, hk⟩ := h
      obtain ⟨n, rfl⟩ := intEnum_surjective k
      exact absurd hk (hs n)
  · right
    exact ⟨fun k hk => h ⟨k, hk⟩, by simp only [proxyValue, h, ↓reduceIte]⟩

end MatedCRT.Tightness
