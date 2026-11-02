module

public import LDPC.PaperLemmas.DeletedChecks
public import Mathlib.Data.Rat.Floor

/-! Review layout: Helpers.Peeling. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section Peeling
variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ τ P : ℚ}

/-- Finite maximality implements the peeling proof. An admissible state records
the check-growth invariant and the integer expansion bound. If a coordinate
still meets the peeling rule, inserting it gives a larger admissible state.
Counting all neighbors, rather than only unique neighbors, gives the improved
factor τ−γ. The strict size bound keeps insertion within the integer cutoff `K`. -/
theorem peeling_exists (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hτ : γ < τ) (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hPK : P ≤ K) (R₀ : Finset R)
    (hbad : (R₀.card : ℚ) < (τ - γ) * c * P) :
    ∃ L₀ : Finset L, (L₀.card : ℚ) < P ∧
      ∀ i ∉ L₀, ((G.right i ∩ (R₀ ∪ G.neighborhood L₀)).card : ℚ) ≤ τ * c := by
  classical
  let good (S : Finset L) : Prop := S.card ≤ K ∧
    ((R₀ ∪ G.neighborhood S).card : ℚ) ≤ R₀.card + (1 - τ) * c * S.card
  have hsmall (S : Finset L) (hS : good S) : (S.card : ℚ) < P := by
    have he := hG.expansion S
      ((by exact_mod_cast hS.1 : (S.card : ℚ) ≤ K).trans hK)
    have hsub : ((G.neighborhood S).card : ℚ) ≤ (R₀ ∪ G.neighborhood S).card := by
      exact_mod_cast Finset.card_le_card Finset.subset_union_right
    have hcost := hS.2
    have hfactor : (0 : ℚ) < (τ - γ) * c :=
      mul_pos (sub_pos.mpr hτ) (by exact_mod_cast hc)
    nlinarith
  let states := Finset.univ.filter good
  have hempty : (∅ : Finset L) ∈ states := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simp [good, TannerGraph.neighborhood]⟩
  obtain ⟨S, hSmem, hmax⟩ := states.exists_max_image Finset.card ⟨∅, hempty⟩
  have hS : good S := (Finset.mem_filter.mp hSmem).2
  refine ⟨S, hsmall S hS, ?_⟩
  intro i hi
  by_contra hhit
  have hhit' := lt_of_not_ge hhit
  have hltK : S.card < K := by
    exact_mod_cast lt_of_lt_of_le (hsmall S hS) hPK
  have hinsert : good (insert i S) := by
    refine ⟨by rw [Finset.card_insert_of_notMem hi]; omega, ?_⟩
    have hnew : R₀ ∪ G.neighborhood (insert i S) =
        (R₀ ∪ G.neighborhood S) ∪ G.right i := by
      simp only [TannerGraph.neighborhood, Finset.biUnion_insert]
      ac_rfl
    have hcard : (((R₀ ∪ G.neighborhood S) ∪ G.right i).card : ℚ) +
        (G.right i ∩ (R₀ ∪ G.neighborhood S)).card =
        (R₀ ∪ G.neighborhood S).card + c := by
      have h := Finset.card_union_add_card_inter (R₀ ∪ G.neighborhood S) (G.right i)
      rw [hG.left_degree i, Finset.inter_comm] at h
      exact_mod_cast h
    rw [hnew, Finset.card_insert_of_notMem hi]
    push_cast
    have hcost := hS.2
    nlinarith
  have hmem : insert i S ∈ states := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinsert⟩
  have := hmax (insert i S) hmem
  rw [Finset.card_insert_of_notMem hi] at this
  omega


/-- The closed check budget is sufficient when the puncturing budget lies strictly
inside the integer expansion cutoff. Apply strict peeling at floor(P)+1. -/
theorem peeling_exists_le (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hτ : γ < τ) (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hPK : P < K) (R₀ : Finset R)
    (hbad : (R₀.card : ℚ) ≤ (τ - γ) * c * P) :
    ∃ L₀ : Finset L, (L₀.card : ℚ) ≤ P ∧
      ∀ i ∉ L₀, ((G.right i ∩ (R₀ ∪ G.neighborhood L₀)).card : ℚ) ≤ τ * c := by
  have hfactor : (0 : ℚ) < (τ - γ) * c :=
    mul_pos (sub_pos.mpr hτ) (by exact_mod_cast hc)
  have hP : 0 ≤ P := by
    nlinarith [show (0 : ℚ) ≤ R₀.card by positivity]
  have hfloor : Nat.floor P < K := (Nat.floor_lt hP).mpr hPK
  have hcut : ((Nat.floor P + 1 : ℕ) : ℚ) ≤ K := by
    exact_mod_cast Nat.succ_le_of_lt hfloor
  have hstrict : (R₀.card : ℚ) <
      (τ - γ) * c * ((Nat.floor P + 1 : ℕ) : ℚ) := by
    have hnext := Nat.lt_floor_add_one P
    push_cast
    nlinarith
  obtain ⟨L₀, hL₀, hterminal⟩ := peeling_exists hG hc hτ hK hcut R₀ hstrict
  have hcard : L₀.card ≤ Nat.floor P := by
    have : L₀.card < Nat.floor P + 1 := by exact_mod_cast hL₀
    omega
  exact ⟨L₀, (by exact_mod_cast hcard : (L₀.card : ℚ) ≤ Nat.floor P).trans
    (Nat.floor_le hP), hterminal⟩

end Peeling

/-! ## The surviving checks certify distance of the actual punctured supercode -/

section ResidualDistance
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ τ : ℚ}

omit [Field F] [DecidableEq F] in
theorem neighborhood_inter_card_le (S : Finset L) (B : Finset R) :
    (G.neighborhood S ∩ B).card ≤ ∑ i ∈ S, (G.right i ∩ B).card := by
  have heq : G.neighborhood S ∩ B = S.biUnion (fun i => G.right i ∩ B) := by
    ext j
    simp only [TannerGraph.neighborhood, Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [heq]
  exact Finset.card_biUnion_le

/-- The terminal peeling condition preserves a unique surviving check on every
nonempty support of size at most `K`. The projected code is the actual image
of the original relaxed code; equality with the surviving-check code is not
assumed. -/
theorem punctured_relaxed_distance (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hτ : τ < 1 - 2 * γ) (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (H : G.WeightedSystem F) (R₀ : Finset R) (L₀ : Finset L)
    (hterminal : ∀ i ∉ L₀,
      ((G.right i ∩ (R₀ ∪ G.neighborhood L₀)).card : ℚ) ≤ τ * c) :
    HasDistance (puncture (H.relaxedCode R₀) (Finset.univ \ L₀)) (K + 1) := by
  intro w hw hw0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
  let T := support x \ L₀
  have hcard : (support (restrict (Finset.univ \ L₀) x)).card = T.card := by
    rw [support_restrict_card]
    congr 1
    ext i
    simp [T]
  have hpos : 0 < T.card := by
    by_contra h
    have hz : support (restrict (Finset.univ \ L₀) x) = ∅ :=
      Finset.card_eq_zero.mp (by rw [hcard]; omega)
    exact hw0 ((support_eq_empty_iff _).mp hz)
  have hlarge : K < T.card := by
    by_contra h
    have hsmall : T.card ≤ K := le_of_not_gt h
    have huniq := proposition_4 hG T
      ((by exact_mod_cast hsmall : (T.card : ℚ) ≤ K).trans hK)
    have hsub : G.uniqueNeighbors T ⊆ R₀ ∪ G.neighborhood L₀ := by
      apply (unique_subset_removed H hx T Finset.sdiff_subset).trans
      apply Finset.union_subset_union (Finset.Subset.refl R₀)
      apply Finset.biUnion_subset_biUnion_of_subset_left
      simp [T]
    have hupperNat : (G.uniqueNeighbors T).card ≤
        ∑ i ∈ T, (G.right i ∩ (R₀ ∪ G.neighborhood L₀)).card := by
      apply (Finset.card_le_card
        (Finset.subset_inter (unique_subset_neighborhood T) hsub)).trans
      exact neighborhood_inter_card_le T (R₀ ∪ G.neighborhood L₀)
    have hupper : ((G.uniqueNeighbors T).card : ℚ) ≤ τ * c * T.card := calc
      _ ≤ ∑ i ∈ T, ((G.right i ∩ (R₀ ∪ G.neighborhood L₀)).card : ℚ) := by
        exact_mod_cast hupperNat
      _ ≤ ∑ _i ∈ T, τ * c := Finset.sum_le_sum fun i hi =>
        hterminal i (Finset.mem_sdiff.mp hi).2
      _ = _ := by simp [mul_comm]
    have hfactor : (0 : ℚ) < (1 - 2 * γ - τ) * c :=
      mul_pos (by linarith) (by exact_mod_cast hc)
    have hpositive := mul_pos hfactor (show (0 : ℚ) < T.card by exact_mod_cast hpos)
    nlinarith
  rw [hcard]
  exact_mod_cast Nat.succ_le_of_lt hlarge

end ResidualDistance

end SmoothLDPC
