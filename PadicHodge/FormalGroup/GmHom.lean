/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.FGLHom
import PadicHodge.FormalGroup.GmMu

/-!
# Characters of `F[p^∞]` from formal homomorphisms `F → Ĝ_m`

Over a complete local ring `R` with `p ∈ 𝔪_R`, a homomorphism of formal group laws
`u : F → Ĝ_m` gives a homomorphism of `p`-divisible groups `F[p^∞] → Ĝ_m[p^∞] ≅ μ_{p^∞}`
(`PDivFGL.toMuOfFGLHom`, composing `FGL.Hom.toPDiv` with `GmMu.gmToMu`), hence a map of Tate
modules `T_p F[p^∞](S) → T_p μ_{p^∞}(S)`. These are the maps `u_{O_C} : G(O_C) → μ_{p^∞}(O_C)` used
to define `α` in [Hong, Prop. 3.4.9] (there for `u ∈ T_p(G^∨) = Hom(G_{O_C}, μ_{p^∞})`, (3.7)),
here for `u` defined over `R`.
-/

noncomputable section

open IsLocalRing

namespace PadicHodge

namespace PDivFGL

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [Fact p.Prime] (hpR : (p : R) ∈ maximalIdeal R) {P : PDivFGL R d p}

/-- **`F[p^∞] → μ_{p^∞}` from a formal homomorphism `F → Ĝ_m`.** -/
def toMuOfFGLHom (φ : FGL.Hom P.F (FGL.multiplicative R)) :
    PDivGroup.Hom P.pdivGroup (muPDiv R p) :=
  (GmMu.gmToMu p hpR).comp (FGL.Hom.toPDiv (P' := gmPDiv R p hpR) φ)

/-- The induced map of Tate modules `T_p F[p^∞](S) → T_p μ_{p^∞}(S)`. -/
def tateToMu (φ : FGL.Hom P.F (FGL.multiplicative R)) (S : Type u) [CommRing S] [Algebra R S] :
    P.pdivGroup.TateModule S →* (muPDiv R p).TateModule S :=
  (toMuOfFGLHom hpR φ).mapTate S

end PDivFGL

end PadicHodge
