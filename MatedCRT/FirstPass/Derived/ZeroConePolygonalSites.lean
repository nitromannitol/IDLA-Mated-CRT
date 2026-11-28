import MatedCRT.FirstPass.Derived.ZeroConePolygonalVoronoi

/-!
# The dyadic sites of a curve

In the construction of the polygonal configuration (written argument, line 17): "In each time cell
take the endpoints of the first dyadic subdivision for which all subinterval images have diameter
at most `min_{K_j} r / 100`. ... It satisfies `dist(z,V) ≤ r(z)/100` everywhere."

For a curve `q : ℝ → Plane`, the time cell `K_j = q([j-1, j])` and a positive `1`-Lipschitz scale
`s`, the level `dyadicLevel q s j` is the least `n` such that all `2^n` dyadic subintervals of
`[j-1, j]` have images of diameter at most `(inf_{K_j} s) / 100`, and `dyadicSites q s` is the set
of the endpoints of these subintervals, over all `j`.

Main declarations:

* `timeCell`, `scaleMin`, `dyadicLevel`, `dyadicSites`.
* `exists_dyadicFine`: the level exists.
* `isSiteSystem_dyadicSites`: under coverage by the time cells and local finiteness of the time
  cells, `dyadicSites q s` is a site system for `s`.
* `mem_dyadicSites`: every `q j` is a site.
-/

set_option autoImplicit false

open Set Metric Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-- The time cell `K_j = q([j-1, j])`. -/
def timeCell (q : ℝ → Plane) (j : ℤ) : Set Plane := q '' Icc ((j : ℝ) - 1) j

/-- The infimum of the scale over the time cell `K_j`. -/
def scaleMin (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) : ℝ := sInf (s '' timeCell q j)

/-- The left endpoint `j - 1 + k 2^{-n}` of the `k`-th dyadic subinterval of `[j-1, j]` at level
`n`. -/
def dyadicPoint (j : ℤ) (n k : ℕ) : ℝ := (j : ℝ) - 1 + k * (1 / 2) ^ n

/-- At level `n` every dyadic subinterval of `[j-1, j]` has an image of diameter at most
`(inf_{K_j} s) / 100`. -/
def DyadicFine (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) (n : ℕ) : Prop :=
  ∀ k < 2 ^ n, diam (q '' Icc (dyadicPoint j n k) (dyadicPoint j n (k + 1))) ≤
    scaleMin q s j / 100

/-- The first dyadic level at which the subdivision of `[j-1, j]` is fine. -/
def dyadicLevel (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) : ℕ := sInf {n | DyadicFine q s j n}

/-- The endpoints of the dyadic subdivision of `[j-1, j]` at its level, mapped by `q`. -/
def cellSites (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) : Set Plane :=
  (fun k : ℕ => q (dyadicPoint j (dyadicLevel q s j) k)) '' {k | k ≤ 2 ^ dyadicLevel q s j}

/-- **The dyadic sites** of the curve `q` for the scale `s`. -/
def dyadicSites (q : ℝ → Plane) (s : Plane → ℝ) : Set Plane := ⋃ j : ℤ, cellSites q s j

variable {q : ℝ → Plane} {s : Plane → ℝ}

theorem continuous_of_lip (hlip : ∀ y z, s y ≤ s z + dist y z) : Continuous s :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun y z => by
    have h1 := hlip y z
    have h2 := hlip z y
    rw [Real.dist_eq, abs_le, NNReal.coe_one, one_mul, dist_comm z y] at *
    constructor <;> linarith).continuous

theorem scaleMin_le (j : ℤ) {z : Plane} (hz : z ∈ timeCell q j) (hpos : ∀ z, 0 < s z) :
    scaleMin q s j ≤ s z :=
  csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact (hpos y).le⟩ (mem_image_of_mem s hz)

theorem scaleMin_pos (hq : Continuous q) (hs : Continuous s) (hpos : ∀ z, 0 < s z) (j : ℤ) :
    0 < scaleMin q s j := by
  have hK : IsCompact (s '' timeCell q j) := (isCompact_Icc.image hq).image hs
  have hne : (s '' timeCell q j).Nonempty :=
    ((nonempty_Icc.2 (by linarith)).image q).image s
  obtain ⟨z, -, hz⟩ := hK.sInf_mem hne
  rw [scaleMin, ← hz]
  exact hpos z

theorem pow_half_mul_two_pow (n : ℕ) : ((2 : ℝ) ^ n) * (1 / 2) ^ n = 1 := by
  rw [← mul_pow]; norm_num

/-- The dyadic level exists: `q` is uniformly continuous on `[j-1, j]` and `inf_{K_j} s > 0`. -/
theorem exists_dyadicFine (hq : Continuous q) (hlip : ∀ y z, s y ≤ s z + dist y z)
    (hpos : ∀ z, 0 < s z) (j : ℤ) : ∃ n, DyadicFine q s j n := by
  have hm := scaleMin_pos hq (continuous_of_lip hlip) hpos j
  have hε : 0 < scaleMin q s j / 100 := by positivity
  obtain ⟨δ, hδ, hδq⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hq.continuousOn) _ hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, fun k hk => ?_⟩
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  have h2 := pow_half_mul_two_pow n
  have hh : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hk1 : ((k + 1 : ℕ) : ℝ) * (1 / 2) ^ n ≤ 1 := by nlinarith
  have hmem : ∀ a ∈ Icc (dyadicPoint j n k) (dyadicPoint j n (k + 1)),
      a ∈ Icc ((j : ℝ) - 1) j := fun a ha => by
    unfold dyadicPoint at ha
    constructor <;> nlinarith [ha.1, ha.2]
  refine diam_le_of_forall_dist_le hε.le ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine (hδq a (hmem a ha) b (hmem b hb) ?_).le
  have hab : dist a b ≤ (1 / 2) ^ n := by
    rw [Real.dist_eq, abs_le]
    have := ha.1; have := ha.2; have := hb.1; have := hb.2
    unfold dyadicPoint at *
    push_cast at *
    constructor <;> nlinarith
  exact lt_of_le_of_lt hab hn

theorem dyadicFine_level (hq : Continuous q) (hlip : ∀ y z, s y ≤ s z + dist y z)
    (hpos : ∀ z, 0 < s z) (j : ℤ) : DyadicFine q s j (dyadicLevel q s j) :=
  Nat.sInf_mem (exists_dyadicFine hq hlip hpos j)

/-- Every point of `[0,1]` lies in a closed dyadic subinterval of level `n`. -/
theorem exists_dyadic_index (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * (1 / 2) ^ n ≤ u ∧ u ≤ ((k : ℝ) + 1) * (1 / 2) ^ n := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have h2 := pow_half_mul_two_pow n
  have hh : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div_pow]
  rcases hu1.lt_or_eq with hlt | rfl
  · refine ⟨⌊u * 2 ^ n⌋₊, ?_, ?_, ?_⟩
    · have h : u * 2 ^ n < ((2 ^ n : ℕ) : ℝ) := by push_cast; nlinarith
      exact (Nat.floor_lt (by positivity)).2 h
    · rw [hh, mul_one_div, div_le_iff₀ hN]
      exact Nat.floor_le (by positivity)
    · rw [hh, mul_one_div, le_div_iff₀ hN]
      exact (Nat.lt_floor_add_one _).le
  · refine ⟨2 ^ n - 1, Nat.sub_lt (by positivity) one_pos, ?_, ?_⟩
    · rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      nlinarith
    · rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      nlinarith

theorem dyadicPoint_mem_Icc (j : ℤ) (n : ℕ) {k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicPoint j n k ∈ Icc ((j : ℝ) - 1) j := by
  have h2 := pow_half_mul_two_pow n
  have hh : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  unfold dyadicPoint
  constructor <;> nlinarith

theorem cellSites_subset (j : ℤ) : cellSites q s j ⊆ timeCell q j := by
  rintro _ ⟨k, hk, rfl⟩
  exact mem_image_of_mem q (dyadicPoint_mem_Icc j _ hk)

theorem finite_cellSites (j : ℤ) : (cellSites q s j).Finite :=
  (finite_Iic (2 ^ dyadicLevel q s j)).image _

/-- Every `q j` is a dyadic site. -/
theorem mem_dyadicSites (j : ℤ) : q j ∈ dyadicSites q s := by
  refine mem_iUnion.2 ⟨j, 2 ^ dyadicLevel q s j, Nat.le_refl _, ?_⟩
  have h2 := pow_half_mul_two_pow (dyadicLevel q s j)
  simp only [dyadicPoint, Nat.cast_pow, Nat.cast_ofNat, h2]
  congr 1
  ring

/-- **The dyadic sites form a site system**: if the time cells cover the plane and are locally
finite, the dyadic sites are locally finite and every `z` has a site within `s z / 100`. -/
theorem isSiteSystem_dyadicSites (hq : Continuous q) (hlip : ∀ y z, s y ≤ s z + dist y z)
    (hpos : ∀ z, 0 < s z) (hcover : ∀ z, ∃ j : ℤ, z ∈ timeCell q j)
    (hloc : ∀ A : Set Plane, IsCompact A → {j : ℤ | (timeCell q j ∩ A).Nonempty}.Finite) :
    IsSiteSystem (dyadicSites q s) s where
  lip := hlip
  pos := hpos
  finite := by
    intro z R
    have hJ := hloc _ (isCompact_closedBall z R)
    refine (hJ.biUnion fun j _ => finite_cellSites (q := q) (s := s) j).subset ?_
    rintro p ⟨hpV, hpB⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hpV
    exact mem_iUnion₂.2 ⟨j, ⟨p, cellSites_subset j hj, hpB⟩, hj⟩
  dense := by
    intro z
    obtain ⟨j, t, ht, rfl⟩ := hcover z
    set n := dyadicLevel q s j with hn
    obtain ⟨k, hk, hk1, hk2⟩ := exists_dyadic_index n (u := t - ((j : ℝ) - 1))
      (by linarith [ht.1]) (by linarith [ht.2])
    have hpt : ∀ m : ℕ, dyadicPoint j n m = (j : ℝ) - 1 + m * (1 / 2) ^ n := fun m => rfl
    have hta : dyadicPoint j n k ≤ t := by rw [hpt]; linarith
    have htb : t ≤ dyadicPoint j n (k + 1) := by rw [hpt]; push_cast; linarith
    refine ⟨q (dyadicPoint j n k), mem_iUnion.2 ⟨j, k, hk.le, rfl⟩, ?_⟩
    have hfine := dyadicFine_level hq hlip hpos j k hk
    have hbdd : Bornology.IsBounded
        (q '' Icc (dyadicPoint j n k) (dyadicPoint j n (k + 1))) :=
      (isCompact_Icc.image hq).isBounded
    have hd := dist_le_diam_of_mem hbdd
      (mem_image_of_mem q ⟨hta, htb⟩)
      (mem_image_of_mem q (⟨le_rfl, hta.trans htb⟩ : dyadicPoint j n k ∈
        Icc (dyadicPoint j n k) (dyadicPoint j n (k + 1))))
    have hmin := scaleMin_le (q := q) (s := s) j (mem_image_of_mem q ht) hpos
    linarith

end MatedCRT.ZeroConePolygonal
