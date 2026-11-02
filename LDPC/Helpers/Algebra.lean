module

public import LDPC.Statements.Core
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Review layout: Helpers.Algebra. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section Algebra
variable {L R F : Type*} [Fintype L] [DecidableEq L]
    [Field F] [DecidableEq F]

omit [DecidableEq L] in
@[simp] theorem mem_support (x : L → F) (i : L) :
    i ∈ support x ↔ x i ≠ 0 := by simp [support]

omit [DecidableEq L] in
theorem support_eq_empty_iff (x : L → F) : support x = ∅ ↔ x = 0 := by
  simp [Finset.ext_iff, funext_iff]

omit [Fintype L] [DecidableEq L] [DecidableEq F] in
@[simp] theorem restrict_apply (I : Finset L) (x : L → F) (i : I) :
    restrict I x i = x i := rfl

theorem support_restrict_card (I : Finset L) (x : L → F) :
    (support (restrict I x)).card = (support x ∩ I).card := by
  have heq : support (restrict I x) = (support x).subtype (· ∈ I) := by
    ext i
    simp
  rw [heq, Finset.card_subtype]
  congr 1

theorem distance_restrict_le (I : Finset L) (x y : L → F) :
    distance (restrict I x) (restrict I y) ≤ distance x y := by
  unfold distance
  rw [← map_sub, support_restrict_card]
  exact Finset.card_le_card Finset.inter_subset_left

omit [DecidableEq L] in
theorem HasDistance.eq_of_distance_lt {C : Submodule F (L → F)} {D : ℚ}
    (hD : HasDistance C D) {x y : L → F} (hx : x ∈ C) (hy : y ∈ C)
    (hclose : (distance x y : ℚ) < D) : x = y := by
  by_contra hne
  exact (not_lt_of_ge (hD (x - y) (C.sub_mem hx hy) (sub_ne_zero.mpr hne))) hclose

/-- The projected distance turns a nearby full word into exact agreement. -/
theorem agreement_of_close {C C' : Submodule F (L → F)} (hCC' : C ≤ C')
    (I : Finset L) {D : ℚ} (hD : HasDistance (puncture C' I) D)
    {w cw : L → F} (hw : w ∈ C') (hcw : cw ∈ C)
    (hclose : (distance w cw : ℚ) < D) : restrict I w = restrict I cw := by
  apply hD.eq_of_distance_lt (Submodule.mem_map_of_mem hw)
    (Submodule.mem_map_of_mem (hCC' hcw))
  exact lt_of_le_of_lt (by exact_mod_cast distance_restrict_le I w cw) hclose

omit [Fintype L] [DecidableEq L] [DecidableEq F] in
/-- Interpolate full codewords from agreement at two distinct seeds. -/
theorem interpolate_agreement (C : Submodule F (L → F)) (I : Finset L)
    (u v c₁ c₂ : L → F) {r₁ r₂ : F} (hne : r₁ ≠ r₂)
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (h₁ : restrict I (u + r₁ • v) = restrict I c₁)
    (h₂ : restrict I (u + r₂ • v) = restrict I c₂) :
    ∃ cu ∈ C, ∃ cv ∈ C, ∀ i ∈ I, u i = cu i ∧ v i = cv i := by
  let cv : L → F := (r₁ - r₂)⁻¹ • (c₁ - c₂)
  let cu : L → F := c₁ - r₁ • cv
  have hcv : cv ∈ C := C.smul_mem _ (C.sub_mem hc₁ hc₂)
  refine ⟨cu, C.sub_mem hc₁ (C.smul_mem r₁ hcv), cv, hcv, ?_⟩
  intro i hi
  have h₁i : u i + r₁ * v i = c₁ i := congrFun h₁ ⟨i, hi⟩
  have h₂i : u i + r₂ * v i = c₂ i := congrFun h₂ ⟨i, hi⟩
  have hv : v i = cv i := by
    change v i = (r₁ - r₂)⁻¹ * (c₁ i - c₂ i)
    rw [← h₁i, ← h₂i]
    field_simp [sub_ne_zero.mpr hne]
    ring
  refine ⟨?_, hv⟩
  change u i = c₁ i - r₁ * cv i
  rw [← hv, ← h₁i]
  ring

theorem pairDistance_le_deleted (L₀ : Finset L) (u v cu cv : L → F)
    (hag : ∀ i ∈ Finset.univ \ L₀, u i = cu i ∧ v i = cv i) :
    pairDistance u v cu cv ≤ L₀.card := by
  apply Finset.card_le_card
  intro i hi
  by_contra hnot
  have heq := hag i (by simp [hnot])
  simp [mem_support, heq.1, heq.2] at hi


/-- A jointly far pair forces the claimed radius below the whole block length. -/
theorem PairFar.radius_lt_card {C : Submodule F (L → F)} {P : ℚ} {u v : L → F}
    (hfar : PairFar C P u v) : P < Fintype.card L := by
  have hcard : (pairDistance u v 0 0 : ℚ) ≤ Fintype.card L := by
    exact_mod_cast Finset.card_le_univ (support (u - 0) ∪ support (v - 0))
  exact (hfar 0 C.zero_mem 0 C.zero_mem).trans_le hcard

end Algebra

section Checks
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F]
    {G : TannerGraph L R}

@[simp] theorem mem_code (H : G.WeightedSystem F) (x : L → F) :
    x ∈ H.code ↔ ∀ j, H.check x j = 0 := by
  change H.checkMap x = 0 ↔ _
  exact funext_iff

theorem code_le_relaxed (H : G.WeightedSystem F) (R₀ : Finset R) :
    H.code ≤ H.relaxedCode R₀ := by
  intro x hx j hj
  exact (mem_code H x).mp hx j

theorem inputs_mem_relaxed_badChecks (H : G.WeightedSystem F) (u v : L → F) :
    u ∈ H.relaxedCode (H.badChecks u v) ∧ v ∈ H.relaxedCode (H.badChecks u v) := by
  classical
  constructor <;> intro j hj <;>
    simp_all [TannerGraph.WeightedSystem.badChecks]

end Checks

/-! ## Unique-neighbor property: graph counting and nonzero checks -/

namespace TannerGraph
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

@[simp] theorem mem_neighborhood (G : TannerGraph L R) (S : Finset L) (j : R) :
    j ∈ G.neighborhood S ↔ ∃ i ∈ S, i ∈ G.left j := by
  simp [neighborhood, G.mem_left_iff]

@[simp] theorem mem_uniqueNeighbors (G : TannerGraph L R) (S : Finset L) (j : R) :
    j ∈ G.uniqueNeighbors S ↔ (G.left j ∩ S).card = 1 := by
  simp [uniqueNeighbors]

/-- Count edges by either endpoint. -/
theorem incidence_sum (G : TannerGraph L R) (S : Finset L) :
    ∑ j : R, (G.left j ∩ S).card = ∑ i ∈ S, (G.right i).card := by
  have hleft (j : R) :
      S.bipartiteBelow (fun i j => j ∈ G.right i) j = G.left j ∩ S := by
    ext i
    simp [Finset.bipartiteBelow, ← G.mem_left_iff, and_comm]
  have hright (i : L) :
      Finset.univ.bipartiteAbove (fun i j => j ∈ G.right i) i = G.right i := by
    ext j
    simp [Finset.bipartiteAbove]
  simpa [hleft, hright] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := S) (t := Finset.univ) (fun i j => j ∈ G.right i)).symm

/-- Bi-regularity gives `c|L| = k|R|`. -/
theorem regular_handshake (G : TannerGraph L R) {c k : ℕ}
    (hreg : G.IsRegular c k) : c * Fintype.card L = k * Fintype.card R := by
  simpa [hreg.left_degree, hreg.right_degree, Nat.mul_comm] using
    (G.incidence_sum Finset.univ).symm

/-- Convert a coordinate radius into the corresponding check budget. -/
theorem regular_scale (G : TannerGraph L R) [Nonempty L] {c k : ℕ}
    (hreg : G.IsRegular c k) (ρ : ℚ) :
    ((k : ℚ) * ρ / Fintype.card L) * Fintype.card R = c * ρ := by
  have hh : (c : ℚ) * Fintype.card L = k * Fintype.card R := by
    exact_mod_cast G.regular_handshake hreg
  have hn : (Fintype.card L : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  nlinarith [congrArg (fun t : ℚ => ρ * t) hh]

end TannerGraph

end SmoothLDPC
