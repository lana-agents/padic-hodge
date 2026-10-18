/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtalePoints

/-!
# The quotient maps are surjective on `ℚ̄_p`-points

For a `p`-divisible group `G` over `R` and an `R`-algebra `S`:

* `card_ker_pow`: `G_{v+1}(S)[p] ≅ G_1(S)` (iterate `i_w(G_w) = G_{w+1}[p^w]`), so the
  `p`-torsion of every layer has the cardinality of `G_1(S)`;
* `card_ker_mul_card_range_quot`: `#ker(quot_v) · #im(quot_v) = #G_{v+1}(S)`, with
  `ker(quot_v) = G_{v+1}(S)[p]` (as `i_v ∘ quot_v = [p]` and `i_v` is injective);
* `quot_surjective_of_card`: if `#G_w(S) = p^{hw}` for all `w`, then
  `quot_v : G_{v+1}(S) → G_v(S)` is surjective; in particular over `S = ℚ̄_p` for `G` over `ℚ_p`
  (`quot_surjective_padicAlgCl`, from `card_points_padicAlgCl`).
-/

noncomputable section

open WithConv

namespace PadicHodge

universe u

namespace PDivGroup

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p) (S : Type u) [CommRing S]
  [Algebra R S]

/-- `G_{v+1}(S)[p] ≅ G_1(S)`. -/
theorem card_ker_pow (v : ℕ) :
    Nat.card (powMonoidHom p : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker =
      Nat.card ((G.G 1).points S) := by
  induction v with
  | zero =>
    have : (powMonoidHom p : (G.G 1).points S →* (G.G 1).points S).ker = ⊤ := by
      ext x
      simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_top, iff_true]
      simpa using G.pow_eq_one 1 S x
    rw [this, Subgroup.card_top]
  | succ v ih =>
    rw [← ih]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(G.incl (v + 1)).mapPoints S x.1, ?_⟩)
      ⟨?_, ?_⟩)
    · have hx : x.1 ^ p = 1 := x.2
      change ((G.incl (v + 1)).mapPoints S x.1) ^ p = 1
      rw [← map_pow, hx, map_one]
    · intro x y h
      exact Subtype.ext (G.mapPoints_injective (v + 1) S (congrArg Subtype.val h))
    · intro y
      have hy : y.1 ^ p = 1 := y.2
      have hy' : y.1 ^ (p ^ (v + 1)) = 1 := by
        rw [pow_succ', pow_mul, hy, one_pow]
      obtain ⟨x, hx⟩ := (G.range_eq (v + 1) S y.1).mpr hy'
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      change x ^ p = 1
      apply G.mapPoints_injective (v + 1) S
      rw [map_pow, hx, hy, map_one]

theorem ker_quot (v : ℕ) :
    ((G.quot v).mapPoints S).ker =
      (powMonoidHom p : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker := by
  ext x
  simp only [MonoidHom.mem_ker, powMonoidHom_apply]
  rw [← G.incl_quot]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    apply G.mapPoints_injective v S
    rw [h, map_one]

theorem card_ker_mul_card_range_quot (v : ℕ) :
    Nat.card ((G.G 1).points S) * Nat.card ((G.quot v).mapPoints S).range =
      Nat.card ((G.G (v + 1)).points S) := by
  rw [← G.card_ker_pow S v, ← G.ker_quot S v, ← Subgroup.index_ker, Subgroup.card_mul_index]

/-- If `#G_w(S) = p^{hw}` for all `w`, the quotient maps are surjective on `S`-points. -/
theorem quot_surjective_of_card (hp : 0 < p)
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w)) (v : ℕ) :
    Function.Surjective ((G.quot v).mapPoints S) := by
  have hfin : Finite ((G.G v).points S) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  have h := G.card_ker_mul_card_range_quot S v
  rw [hcard, hcard, mul_add, mul_one, pow_add] at h
  have hr : Nat.card ((G.quot v).mapPoints S).range = Nat.card ((G.G v).points S) := by
    rw [hcard]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp G.height) (h.trans (mul_comm _ _))
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ hr

/-- **`quot_v : G_{v+1}(ℚ̄_p) → G_v(ℚ̄_p)` is surjective** for `G` over a field `K` of
characteristic `0` inside `ℚ̄_p` (e.g. `ℚ_p`). -/
theorem quot_surjective_padicAlgCl {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [CharZero K]
    [Algebra K (PadicAlgCl p)] (G : PDivGroup K p) (v : ℕ) :
    Function.Surjective ((G.quot v).mapPoints (PadicAlgCl p)) :=
  G.quot_surjective_of_card (PadicAlgCl p) hp.out.pos (G.card_points_padicAlgCl) v

end PDivGroup

end PadicHodge
