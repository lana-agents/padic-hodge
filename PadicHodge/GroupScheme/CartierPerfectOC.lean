/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.IntegralPoints
import PadicHodge.GroupScheme.CartierPerfect
import PadicHodge.GroupScheme.EtaleInvertible
import PadicHodge.GroupScheme.BaseChange
import Mathlib.NumberTheory.Padics.Complex

/-!
# The Cartier pairing over `O_{ℂ_p}` separates points

Let `G` be finite flat over `R → O_{ℂ_p}` (`R` nontrivial), killed by some `n ≠ 0` (e.g. a layer
`G_v` of a `p`-divisible group, `n = p^v`). Then:

* `card_dual_points_Cp`: `#G^∨(ℂ_p) = |G|` (`G^∨ ⊗ ℂ_p` is killed by `n`, hence étale over the
  algebraically closed field `ℂ_p`);
* **`eq_one_of_pairing_OC`**: a point `φ ∈ G(O_{ℂ_p})` with `⟨φ, ψ⟩ = 1` for all
  `ψ ∈ G^∨(O_{ℂ_p})` is trivial (perfectness over `ℂ_p`, `pairingHom'_injective`, transported
  along `G(O_{ℂ_p}) ≃ G(ℂ_p)`, `pointsOCEquiv`).

This is the injectivity of the left vertical map of [Hong, Prop. 3.4.9] at a finite level
(`G_v(O_{C_K}) → Hom(G_v^∨(O_{C_K}), μ_{p^v})`, from [Hong, Prop. 3.4.6], (3.6)).
-/

noncomputable section

open WithConv

namespace PadicHodge

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Nontrivial R] [Algebra R (OC p)]

/-- **`#G^∨(ℂ_p) = |G|`** for `G` killed by `n ≠ 0`. -/
theorem card_dual_points_Cp (G : FFGroupScheme R) {n : ℕ} (hn : n ≠ 0)
    (hG : G.univPt ^ n = 1) :
    letI := algebraCpOfOC (p := p) R
    Nat.card (G.dual.points ℂ_[p]) = G.order := by
  letI := algebraCpOfOC (p := p) R
  have hD : G.dual.univPt ^ n = 1 := G.dual_univPt_pow_eq_one hG
  set H := G.dual.baseChange ℂ_[p]
  have hH : H.univPt ^ n = 1 := by
    apply (G.dual.baseChangePointsEquiv H.A).injective
    rw [map_pow, map_one]
    exact G.dual.pow_eq_one_of_univPt hD _
  have hu : IsUnit (n : ℂ_[p]) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  have hE : H.IsEtale := H.isEtale_of_univPt_pow_eq_one hu hH
  rw [← Nat.card_congr (G.dual.baseChangePointsEquiv (S := ℂ_[p]) ℂ_[p]).toEquiv,
    card_points_of_isEtale H hE, order_baseChange, order_dual]

/-- **A point of `G(O_{ℂ_p})` pairing trivially with `G^∨(O_{ℂ_p})` is trivial.** -/
theorem eq_one_of_pairing_OC (G : FFGroupScheme R) {n : ℕ} (hn : n ≠ 0)
    (hG : G.univPt ^ n = 1) (φ : G.points (OC p))
    (h : ∀ ψ : G.dual.points (OC p), G.pairing (OC p) φ ψ = 1) : φ = 1 := by
  letI := algebraCpOfOC (p := p) R
  let ι : OC p →ₐ[R] ℂ_[p] := { (OC p).subtype with commutes' := fun _ => rfl }
  have key : G.pairingHom' (S := ℂ_[p]) (G.postComp ι φ) = G.pairingHom' (S := ℂ_[p]) 1 := by
    refine MonoidHom.ext fun ψ' => ?_
    obtain ⟨ψ, rfl⟩ := (G.dual.pointsOCEquiv (p := p)).surjective ψ'
    rw [map_one, MonoidHom.one_apply]
    change G.pairing ℂ_[p] (G.postComp ι φ) (G.dual.postComp ι ψ) = 1
    rw [pairing_postComp, h ψ, map_one]
  have h1 := G.pairingHom'_injective (S := ℂ_[p]) (G.card_dual_points_Cp hn hG) key
  have h2 : G.pointsOCEquiv (p := p) φ = G.pointsOCEquiv (p := p) 1 := by
    rw [map_one]; exact h1
  exact (G.pointsOCEquiv (p := p)).injective h2

end FFGroupScheme

end PadicHodge
