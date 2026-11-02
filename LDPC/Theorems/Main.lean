module

public import LDPC.Theorems.Paper

/-!
# Five starting theorems

1. Original distance, with an integer expansion cutoff.
2. Half-distance smoothness at the exact check threshold.
3. The main technical lemma for few violated checks: radius d/2, error 1/|F|.
4. The main folding theorem for all far pairs: radius t, error |R|/|F|.
5. Sampling constraints: radius d/2, error 1/|F|+(1−α)^Q.

Here d=2(1−γ)δn, t=(1−3γ−ε)d/2 and α=(1−3γ−ε)kd/(2n).
The margin γδn≥1 supplies the rounding conditions for the last four results.
-/

@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Main

/-- Original distance at an integer cutoff K≤δn. The paper's unrounded bound
requires K=δn; without integrality the cutoff remains explicit. -/
theorem expansion_distance
    -- L and R index finite coordinate/check sets; F is the field alphabet.
    {L R F : Type} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R} {c k K : ℕ} {γ δ : ℚ}
    -- Regular expansion, positive variable degree, and an integer expansion cutoff.
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ : γ < 1 / 2)
    (hK : (K : ℚ) ≤ δ * Fintype.card L) (H : G.WeightedSystem F) :
    -- Every nonzero original codeword has weight at least this absolute count.
    HasDistance H.code (2 * (1 - γ) * K) :=
  proposition_5 hG hc hγ hK H

/-- Half-distance smoothness, including equality at α=(τ−γ)kd/(2n). -/
theorem expansion_smoothness
    {L R F : Type} [Fintype L] [Fintype R]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    {c k : ℕ} {γ δ τ : ℚ}
    -- The graph expands; the peeling threshold lies between the two losses.
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    -- This margin permits a nonintegral expansion range δn.
    (hmargin : 1 ≤ γ * (δ * Fintype.card L)) (H : G.WeightedSystem F) :
    -- Both the puncturing budget and surviving distance are d/2=(1−γ)δn.
    IsSmooth H ((τ - γ) * k * ((1 - γ) * δ * Fintype.card L) / Fintype.card L)
      ((1 - γ) * δ * Fintype.card L) ((1 - γ) * δ * Fintype.card L) :=
  half_distance_smoothness hG hc hγ0 hτlo hτhi hmargin H

/-- The main technical lemma retains the few-violated-checks hypothesis and
its stronger radius d/2 and folding error 1/|F|. -/
theorem smoothness_proximity_gap
    {L R F : Type} [Fintype L] [Fintype R] [Fintype F]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    {c k : ℕ} {γ δ ε : ℚ}
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (H : G.WeightedSystem F) (u v : L → F)
    -- The fixed pair is jointly farther than d/2 from every original codeword pair.
    (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v)
    -- At most α|R| checks fail on either input column; α=(1−3γ−ε)kd/(2n).
    (hbad : ((H.badChecks u v).card : ℚ) ≤
      ((1 - 3 * γ - ε) * k * ((1 - γ) * δ * Fintype.card L) /
        Fintype.card L) * Fintype.card R) :
    -- Only the folding scalar is sampled; proximity is strict.
    Pr_{let r ← $ᵖ F}[GoodFold H.code ((1 - γ) * δ * Fintype.card L) u v r] ≤
      (Fintype.card F : ENNReal)⁻¹ :=
  Paper.main_technical_lemma H hG hc hγ0 hε0 hε hmargin u v hfar hbad

/-- The main folding theorem removes the failed-check premise by splitting
into the few-check and many-check cases. Their bounds are not added. -/
theorem folding
    {L R F : Type} [Fintype L] [Fintype R] [Fintype F]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    {c k : ℕ} {γ δ ε : ℚ}
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (H : G.WeightedSystem F) (u v : L → F)
    (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v) :
    -- The fold radius is t=(1−3γ−ε)d/2, with a check-count loss in the error.
    Pr_{let r ← $ᵖ F}[
      GoodFold H.code ((1 - 3 * γ - ε) * ((1 - γ) * δ * Fintype.card L)) u v r] ≤
      (Fintype.card R : ENNReal) / Fintype.card F :=
  Paper.folding H hG hc hγ0 hε0 hε hmargin u v hfar

/-- Sampling constraints uses the same neighborhood openings for parity and
folding consistency; the rounding condition follows from γδn≥1. -/
theorem shared_query_soundness
    {L R F : Type} [Fintype L] [Fintype R] [Fintype F]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    {c k : ℕ} {γ δ ε : ℚ}
    (H : G.WeightedSystem F) (hG : G.IsExpander c k γ δ)
    (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L)) :
    -- For every far pair, every response preceding queries, and every Q:
    -- acceptance probability is at most 1/|F|+(1−α)^Q, with α=(1−3γ−ε)kd/(2n).
    Protocol.SharedSoundness H ((1 - γ) * δ * Fintype.card L)
      ((1 - 3 * γ - ε) * k * ((1 - γ) * δ * Fintype.card L) / Fintype.card L) :=
  Paper.check_sampling H hG hc hγ0 hε0 hε hmargin

end SmoothLDPC.Main
