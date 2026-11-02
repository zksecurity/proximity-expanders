module

public import LDPC.Statements.Protocol

/-! The check-sampling verifier:
parity and folding consistency are checked on the same sampled neighborhoods. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R}

/-- One neighborhood opening serves both input parity and folding consistency. -/
def SharedAccept (H : G.WeightedSystem F) (u v : L → F) (response : F → L → F)
    {Q : ℕ} (r : F) (sample : Fin Q → R) : Prop :=
  MCA.parityAccept H u v sample ∧ response r ∈ H.code ∧
    ∀ q, ∀ i ∈ G.left (sample q), u i + r * v i = response r i

/-- The paper's one-challenge error plus shared-neighborhood sampling error.
Inputs are fixed before the challenge; the response precedes the query sample. -/
def SharedSoundness [Fintype F] [Nonempty R]
    (H : G.WeightedSystem F) (P α : ℚ) : Prop :=
  ∀ (u v : L → F), PairFar H.code P u v →
    ∀ (response : F → L → F) (Q : ℕ),
    Pr_{let r ← $ᵖ F; let sample ← $ᵖ (Fin Q → R)}[
      SharedAccept H u v response r sample] ≤
      (Fintype.card F : ENNReal)⁻¹ + ENNReal.ofReal (1 - (α : ℝ))^Q

/-- The paper's original Ligero-style test, without input parity queries. -/
def FoldOnlyAccept (H : G.WeightedSystem F) (u v : L → F) (response : F → L → F)
    {Q : ℕ} (r : F) (sample : Fin Q → L) : Prop :=
  response r ∈ H.code ∧ spotAccept u v r (response r) sample

/-- Every coordinate opened by the shared check samples; duplicates count once. -/
def openedCoordinates (G : TannerGraph L R) {Q : ℕ} (sample : Fin Q → R) : Finset L :=
  Finset.univ.biUnion fun q => G.left (sample q)

end SmoothLDPC.Protocol
