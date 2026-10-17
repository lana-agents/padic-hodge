/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.FiniteFlat

/-!
# `p`-divisible groups and their Tate modules

[BC, Def. 7.2.1]: a `p`-divisible group of height `h` over `R` is a directed system `(G_v)` of
finite flat group schemes with `G_v` of order `p^{hv}` and `i_v : G_v → G_{v+1}` an isomorphism
onto `G_{v+1}[p^v]`. We encode "isomorphism onto the kernel of `p^v`" through points: `i_v` is a
closed immersion (its ring map `O(G_{v+1}) → O(G_v)` is surjective) and, for every `R`-algebra
`S`, `i_v(G_v(S)) = G_{v+1}(S)[p^v]`.

* `PDivGroup R p`, `PDivGroup.TateModule G S`: the Tate module
  `lim_v G_v(S)` (transition maps `p`), as a subgroup of `∏_v G_v(S)`;
* `PDivGroup.mapPoints_injective`: the transition maps are injective on points.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

open FFGroupScheme

/-- A `p`-divisible group of height `h` over `R` ([BC, Def. 7.2.1]). -/
structure PDivGroup (R : Type u) [CommRing R] (p : ℕ) where
  /-- the height -/
  height : ℕ
  /-- the layers `G_v = G[p^v]` -/
  G : ℕ → FFGroupScheme R
  order_eq : ∀ v, (G v).order = p ^ (height * v)
  /-- the transition maps `i_v : G_v → G_{v+1}` -/
  incl : ∀ v, FFGroupScheme.Hom (G v) (G (v + 1))
  /-- `i_v` is a closed immersion -/
  incl_surjective : ∀ v, Function.Surjective (incl v)
  /-- `i_v` identifies `G_v` with `G_{v+1}[p^v]` on points -/
  range_eq : ∀ v (S : Type u) [CommRing S] [Algebra R S] (y : (G (v + 1)).points S),
    (∃ x, (incl v).mapPoints S x = y) ↔ y ^ (p ^ v) = 1

namespace PDivGroup

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p)

theorem mapPoints_injective (v : ℕ) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Injective ((G.incl v).mapPoints S) := by
  intro x y h
  apply WithConv.ofConv_injective
  ext a
  obtain ⟨b, rfl⟩ := G.incl_surjective v a
  exact congrArg (fun φ => (ofConv φ) b) h

/-- The Tate module `T_p G (S) = lim_v G_v(S)` with transition maps `[p]`: sequences
`(x_v)` with `i_v(x_v) = p · x_{v+1}` (written multiplicatively). -/
def TateModule (S : Type u) [CommRing S] [Algebra R S] :
    Subgroup ((v : ℕ) → (G.G v).points S) where
  carrier := {x | ∀ v, (G.incl v).mapPoints S (x v) = (x (v + 1)) ^ p}
  mul_mem' := fun {x y} hx hy v => by
    simp only [Pi.mul_apply, map_mul, hx v, hy v, mul_pow]
  one_mem' := fun v => by simp
  inv_mem' := fun {x} hx v => by
    simp only [Pi.inv_apply, map_inv, hx v, inv_pow]

end PDivGroup

end PadicHodge
