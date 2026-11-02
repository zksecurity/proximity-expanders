module

public import LDPC.Helpers.Peeling

/-! Review layout: PaperLemmas.Smoothness. Declaration names are unchanged. -/

@[expose] public section

open scoped BigOperators

namespace SmoothLDPC

section Monotonicity
variable {L R F : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R}

/-- Fewer removed checks, a larger puncturing budget, or a weaker surviving
 distance preserve smoothness. In particular the check fraction is monotone. -/
theorem IsSmooth.mono {H : G.WeightedSystem F} {α α' P P' D D' : ℚ}
    (hs : IsSmooth H α P D) (hα : α' ≤ α) (hP : P ≤ P') (hD : D' ≤ D) :
    IsSmooth H α' P' D' := by
  intro R₀ hR₀
  obtain ⟨L₀, hL₀, hdist⟩ := hs R₀
    (hR₀.trans (mul_le_mul_of_nonneg_right hα (by positivity)))
  exact ⟨L₀, hL₀.trans hP, fun x hx hx0 => hD.trans (hdist x hx hx0)⟩

end Monotonicity

section Smoothness
variable {L R F : Type*} [Fintype L] [Fintype R]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ τ α : ℚ}

/-- The stronger form actually established by peeling: after puncturing fewer
than `(1−γ)K` coordinates the projected distance is at least `K+1`. -/
theorem smoothness_from_expansion (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hγ0 : 0 ≤ γ) (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hα : α < (τ - γ) * k * ((1 - γ) * K) / Fintype.card L)
    (H : G.WeightedSystem F) : IsSmooth H α ((1 - γ) * K) (K + 1) := by
  intro R₀ hR₀
  have hm : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hscale : ((τ - γ) * k * ((1 - γ) * K) / Fintype.card L) *
      Fintype.card R = (τ - γ) * c * ((1 - γ) * K) := by
    calc
      _ = ((k : ℚ) * ((τ - γ) * ((1 - γ) * K)) / Fintype.card L) *
          Fintype.card R := by ring
      _ = _ := by rw [G.regular_scale hG.toIsRegular]; ring
  have hbad : (R₀.card : ℚ) < (τ - γ) * c * ((1 - γ) * K) := by
    rw [← hscale]
    exact hR₀.trans_lt (mul_lt_mul_of_pos_right hα hm)
  have hPK : (1 - γ) * (K : ℚ) ≤ K := by
    nlinarith [show (0 : ℚ) ≤ K by positivity]
  obtain ⟨L₀, hL₀, hterminal⟩ := peeling_exists hG hc hτlo hK hPK R₀ hbad
  exact ⟨L₀, hL₀.le, punctured_relaxed_distance hG hc hτhi hK H R₀ L₀ hterminal⟩

/-- The integer-cutoff variant with `K ≤ δn`: `d/2 = (1−γ)K`. The threshold
interval implies `γ < 1/3`; both threshold inequalities remain explicit. -/
theorem proposition_7 (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hγ0 : 0 ≤ γ) (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hα : α < (τ - γ) * k * ((1 - γ) * K) / Fintype.card L)
    (H : G.WeightedSystem F) : IsSmooth H α ((1 - γ) * K) ((1 - γ) * K) := by
  intro R₀ hR₀
  obtain ⟨L₀, hL₀, hD⟩ := smoothness_from_expansion hG hc hγ0 hτlo hτhi hK hα H R₀ hR₀
  refine ⟨L₀, hL₀, ?_⟩
  intro x hx hx0
  have hd := hD x hx hx0
  nlinarith [show (0 : ℚ) ≤ K by positivity]


/-- Closed-budget smoothness separates the puncturing budget from the integer
cutoff used to certify surviving distance. -/
theorem smoothness_from_expansion_le (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L) {P : ℚ} (hPK : P < K)
    (hα : α ≤ (τ - γ) * k * P / Fintype.card L)
    (H : G.WeightedSystem F) : IsSmooth H α P (K + 1) := by
  intro R₀ hR₀
  have hscale : ((τ - γ) * k * P / Fintype.card L) * Fintype.card R =
      (τ - γ) * c * P := by
    calc
      _ = ((k : ℚ) * ((τ - γ) * P) / Fintype.card L) * Fintype.card R := by ring
      _ = _ := by rw [G.regular_scale hG.toIsRegular]; ring
  have hbad : (R₀.card : ℚ) ≤ (τ - γ) * c * P := by
    rw [← hscale]
    exact hR₀.trans (mul_le_mul_of_nonneg_right hα (by positivity))
  obtain ⟨L₀, hL₀, hterminal⟩ := peeling_exists_le hG hc hτlo hK hPK R₀ hbad
  exact ⟨L₀, hL₀, punctured_relaxed_distance hG hc hτhi hK H R₀ L₀ hterminal⟩

/-- The paper's half-distance smoothness proposition, including equality at the
check threshold. The margin γδn ≥ 1 handles nonintegral δn by floor(δn). -/
theorem half_distance_smoothness (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hγ0 : 0 ≤ γ) (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L)) (H : G.WeightedSystem F) :
    IsSmooth H ((τ - γ) * k * ((1 - γ) * δ * Fintype.card L) / Fintype.card L)
      ((1 - γ) * δ * Fintype.card L) ((1 - γ) * δ * Fintype.card L) := by
  have hx : 0 ≤ δ * Fintype.card L := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hγ0 (le_of_not_ge hn)
    linarith
  have hK : (Nat.floor (δ * Fintype.card L) : ℚ) ≤ δ * Fintype.card L := Nat.floor_le hx
  have hPK : (1 - γ) * δ * Fintype.card L < Nat.floor (δ * Fintype.card L) := by
    have hnext := Nat.lt_floor_add_one (δ * Fintype.card L)
    nlinarith
  have hs := smoothness_from_expansion_le hG hc hτlo hτhi hK hPK le_rfl H
  intro R₀ hR₀
  obtain ⟨L₀, hL₀, hD⟩ := hs R₀ hR₀
  refine ⟨L₀, hL₀, ?_⟩
  intro x hx hx0
  have hd := hD x hx hx0
  nlinarith

end Smoothness

end SmoothLDPC
