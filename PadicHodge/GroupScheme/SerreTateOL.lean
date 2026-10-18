/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.ConnectedPDiv
import PadicHodge.FormalGroup.HeightIneq
import PadicHodge.FormalGroup.OLCompact

/-!
# Serre–Tate over `O_L`, `L/ℚ_p` finite

For a finite extension `L = K'` of `ℚ_p` inside `ℚ̄_p`, `O_L` (`OL L`) is a coefficient ring
(`OL.instCoeffRing`), so the essential surjectivity half of Serre–Tate ([Hong, Thm. 2.2.16])
holds over `O_L`:

* **`PDivGroup.exists_pdivFGL_iso_OL`**: a connected `p`-divisible group over `O_L` is isomorphic
  to `F[p^∞]` for a `p`-divisible formal group law `F` over `O_L`;
* **`PDivGroup.exists_connPart_iso_OL`**: for every `p`-divisible group `G` over `O_L`,
  `G⁰ ≅ F[p^∞]` ([Hong, Prop. 2.1.10, Thm. 2.2.16, Def. 2.2.17]);
* **`PDivFGL.exists_connPart_dual_iso_height_le_OL`**: `h ≤ d + d'` for `F[p^∞]` over `O_L`
  ([Hong, Thm. 2.2.19]), with `(F[p^∞]^∨)⁰ ≅ F'[p^∞]`, `d' = dim F'`.
-/

namespace PadicHodge

variable {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L]

/-- **Serre–Tate, essential surjectivity over `O_L`** ([Hong, Thm. 2.2.16]). -/
theorem PDivGroup.exists_pdivFGL_iso_OL (H : PDivGroup (OL L) p)
    (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ (d : ℕ) (P : PDivFGL (OL L) d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  PDivGroup.exists_pdivFGL_iso_of_coeffRing OL.p_mem H hconn

/-- **`G⁰ ≅ F[p^∞]` over `O_L`** ([Hong, Prop. 2.1.10, Thm. 2.2.16, Def. 2.2.17]). -/
theorem PDivGroup.exists_connPart_iso_OL (G : PDivGroup (OL L) p) :
    ∃ (d : ℕ) (P : PDivFGL (OL L) d p) (φ : PDivGroup.Hom G.connPart P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup G.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  PDivGroup.exists_connPart_iso_of_coeffRing OL.p_mem G

/-- **`h ≤ d + d'` over `O_L`** ([Hong, Thm. 2.2.19]). -/
theorem PDivFGL.exists_connPart_dual_iso_height_le_OL {d : ℕ} (P : PDivFGL (OL L) d p) :
    ∃ (d' : ℕ) (P' : PDivFGL (OL L) d' p)
      (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ ∧ P.height ≤ d + d' :=
  P.exists_connPart_dual_iso_height_le_of_coeffRing OL.p_mem

end PadicHodge
