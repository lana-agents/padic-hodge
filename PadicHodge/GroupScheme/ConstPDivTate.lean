/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.ConstPDiv
import PadicHodge.GroupScheme.TateMuZp
import PadicHodge.HodgeTate.Character

/-!
# The Tate module of `ℚ_p/ℤ_p`

For a domain `S`, `M_R(S) ≃* M` (`constPointsEquiv`), and under these identifications the
transition maps of `constPDiv R p` are `x ↦ p x`. A point of the Tate module is thus a sequence
`a_v ∈ ℤ/p^v` with `p a_v = p a_{v+1}` in `ℤ/p^{v+1}`, i.e. `a_{v+1} ≡ a_v mod p^v`
(`tateCoord_succ`): a compatible system, i.e. an element of `ℤ_p`.

* `constTateEquiv R S : (constPDiv R p).TateModule S ≃* Multiplicative ℤ_[p]`;
* `PDivGroup.galTate`: the action of `Gal(ℚ̄_p/ℚ_p)` on the Tate module of any `p`-divisible
  group over `ℚ_p` (through `galPoints`, as in `GroupScheme/TateMuZp.lean`);
* `galTate_constPDiv`: it is trivial on `T_p(ℚ_p/ℤ_p)`, so `V_p(ℚ_p/ℤ_p) = ℚ_p(0)`
  (`constTate_charRep`: `σ` acts through `charRep L 0`), which is Hodge–Tate with the single
  weight `0` (`isHodgeTate_constTate`, `htWeights_constTate`).
-/

noncomputable section

namespace PadicHodge

universe u

open FFGroupScheme WithConv

variable {p : ℕ} [hp : Fact p.Prime]

theorem nat_mul_mod_iff {v a b : ℕ} (ha : a < p ^ v) :
    p * a % p ^ (v + 1) = p * b % p ^ (v + 1) ↔ b % p ^ v = a := by
  rw [pow_succ', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt ha]
  constructor
  · intro h; exact (Nat.eq_of_mul_eq_mul_left hp.out.pos h).symm
  · intro h; rw [h]

/-- `p x = p y` in `ℤ/p^{v+1}` (`x ∈ ℤ/p^v`) iff `y ≡ x mod p^v`. -/
theorem mulP_eq_mul_iff {v : ℕ} (x : ZMod (p ^ v)) (y : ZMod (p ^ (v + 1))) :
    mulP p v x = (p : ZMod (p ^ (v + 1))) * y ↔ y.val % p ^ v = x.val := by
  rw [mulP_apply]
  conv_lhs => rw [← ZMod.natCast_zmod_val y, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
  exact nat_mul_mod_iff (ZMod.val_lt x)

variable (R : Type u) [CommRing R] [Nontrivial R] (S : Type u) [CommRing S] [IsDomain S]
  [Algebra R S]

omit [Nontrivial R] [IsDomain S] in
theorem mapPoints_constPt {M M' : Type} [CommGroup M] [Fintype M] [DecidableEq M]
    [CommGroup M'] [Fintype M'] [DecidableEq M'] (h : M →* M') (m : M) :
    (constMap R h).mapPoints S (constPt (R := R) S m) = constPt S (h m) :=
  WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

theorem constPointsEquiv_apply {M : Type} [CommGroup M] [Fintype M] [DecidableEq M] (m : M) :
    constPointsEquiv (R := R) S m = constPt S m := rfl

/-- The `ℤ/p^v`-coordinate of a point of the Tate module of `ℚ_p/ℤ_p`. -/
def tateCoord (x : (constPDiv R p).TateModule S) (v : ℕ) : ZMod (p ^ v) :=
  Multiplicative.toAdd ((constPointsEquiv (R := R) (M := CycP p v) S).symm (x.1 v))

theorem tateCoord_spec (x : (constPDiv R p).TateModule S) (v : ℕ) :
    constPointsEquiv (R := R) (M := CycP p v) S (Multiplicative.ofAdd (tateCoord R S x v)) =
      x.1 v :=
  (constPointsEquiv (R := R) (M := CycP p v) S).apply_symm_apply _

theorem tateCoord_succ (x : (constPDiv R p).TateModule S) (v : ℕ) :
    (tateCoord R S x (v + 1)).val % p ^ v = (tateCoord R S x v).val := by
  rw [← mulP_eq_mul_iff]
  have hx : ∀ w, ((constPDiv R p).incl w).mapPoints S (x.1 w) = (x.1 (w + 1)) ^ p := x.2
  have h2 : incP v (Multiplicative.ofAdd (tateCoord R S x v)) =
      (Multiplicative.ofAdd (tateCoord R S x (v + 1))) ^ p := by
    apply (constPointsEquiv (R := R) (M := CycP p (v + 1)) S).injective
    rw [map_pow]
    change constPt S (incP v _) = _
    rw [← mapPoints_constPt, ← constPointsEquiv_apply, tateCoord_spec, tateCoord_spec]
    exact hx v
  have h' := congrArg Multiplicative.toAdd h2
  rw [toAdd_pow, nsmul_eq_mul] at h'
  exact h'

/-- `ℤ_p → T_p(ℚ_p/ℤ_p)(S)`, `a ↦ (a mod p^v)_v`. -/
def zpTate : Multiplicative ℤ_[p] →* (constPDiv R p).TateModule S where
  toFun a := ⟨fun v => constPointsEquiv (R := R) (M := CycP p v) S
      (Multiplicative.ofAdd (PadicInt.toZModPow v (Multiplicative.toAdd a))), by
    intro v
    change (constMap R (incP v)).mapPoints S (constPt S _) = (constPointsEquiv S _) ^ p
    rw [← map_pow, mapPoints_constPt, ← constPointsEquiv_apply]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul]
    change mulP p v _ = _
    rw [mulP_eq_mul_iff]
    exact expo_succ _ v⟩
  map_one' := Subtype.ext <| funext fun v => by
    change constPointsEquiv S (Multiplicative.ofAdd
      (PadicInt.toZModPow v (Multiplicative.toAdd (1 : Multiplicative ℤ_[p])))) = 1
    rw [toAdd_one, map_zero, ofAdd_zero, map_one]
  map_mul' a b := Subtype.ext <| funext fun v => by
    change constPointsEquiv S (Multiplicative.ofAdd
      (PadicInt.toZModPow v (Multiplicative.toAdd (a * b)))) =
      constPointsEquiv S (Multiplicative.ofAdd (PadicInt.toZModPow v (Multiplicative.toAdd a))) *
      constPointsEquiv S (Multiplicative.ofAdd (PadicInt.toZModPow v (Multiplicative.toAdd b)))
    rw [toAdd_mul, map_add, ofAdd_add, map_mul]

theorem zpTate_injective : Function.Injective (zpTate (p := p) R S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h : ∀ v, PadicInt.toZModPow v (Multiplicative.toAdd a) = 0 := by
    intro v
    have := congrArg (fun x : (constPDiv R p).TateModule S => x.1 v) ha
    change constPointsEquiv S (Multiplicative.ofAdd
      (PadicInt.toZModPow v (Multiplicative.toAdd a))) = 1 at this
    rw [MulEquiv.map_eq_one_iff] at this
    exact this
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact PadicInt.ext_of_toZModPow.mp fun v => by rw [h v, map_zero]

theorem zpTate_surjective : Function.Surjective (zpTate (p := p) R S) := by
  intro x
  set k : ℕ → ℤ := fun v => ((tateCoord R S x v).val : ℤ)
  have hcompat : ∀ v, (p : ℤ) ^ v ∣ k (v + 1) - k v := by
    intro v
    have h : (tateCoord R S x v).val ≡ (tateCoord R S x (v + 1)).val [MOD p ^ v] := by
      change _ % _ = _ % _
      rw [tateCoord_succ, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    have := Nat.modEq_iff_dvd.mp h
    simp only [k]
    push_cast at this ⊢
    exact this
  set a := PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub k p hcompat)
  refine ⟨Multiplicative.ofAdd a, Subtype.ext <| funext fun v => ?_⟩
  change constPointsEquiv S (Multiplicative.ofAdd (PadicInt.toZModPow v a)) = x.1 v
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    tateCoord_spec]
  exact hcompat

/-- **`T_p(ℚ_p/ℤ_p)(S) ≅ ℤ_p`** for a domain `S`. -/
def constTateEquiv : (constPDiv R p).TateModule S ≃* Multiplicative ℤ_[p] :=
  (MulEquiv.ofBijective (zpTate R S) ⟨zpTate_injective R S, zpTate_surjective R S⟩).symm

/-! ### The Galois action -/

/-- The Galois action on the Tate module of a `p`-divisible group over a field `K ⊆ ℚ̄_p`
(e.g. `ℚ_p`). -/
def PDivGroup.galTate {K : Type} [Field K] [Algebra K (PadicAlgCl p)] (G : PDivGroup K p)
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    G.TateModule (PadicAlgCl p) →* G.TateModule (PadicAlgCl p) where
  toFun x := ⟨fun v => galPoints (G.G v) σ (x.1 v), by
    intro v
    have hx : ∀ w, (G.incl w).mapPoints _ (x.1 w) = (x.1 (w + 1)) ^ p := x.2
    rw [← map_pow, ← hx v]
    rfl⟩
  map_one' := by ext1; funext v; exact map_one _
  map_mul' x y := by ext1; funext v; exact map_mul _ _ _

/-- The Galois action on `T_p(ℚ_p/ℤ_p)(ℚ̄_p)` is trivial. -/
theorem galTate_constPDiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : (constPDiv ℚ_[p] p).TateModule (PadicAlgCl p)) :
    (constPDiv ℚ_[p] p).galTate σ x = x := by
  refine Subtype.ext <| funext fun v => ?_
  change galPoints (const ℚ_[p] (CycP p v)) σ (x.1 v) = x.1 v
  rw [← tateCoord_spec ℚ_[p] (PadicAlgCl p) x v, constPointsEquiv_apply]
  exact WithConv.ofConv_injective (AlgHom.ext fun _ => σ.commutes _)

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `T_p(ℚ_p/ℤ_p)(ℚ̄_p) ≅ ℤ_p` with trivial Galois action: `V_p(ℚ_p/ℤ_p) ≅ ℚ_p(0)`, i.e.
`σ ∈ G_L` acts through `charRep L 0`. -/
theorem constTate_charRep (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (x : (constPDiv ℚ_[p] p).TateModule (PadicAlgCl p)) :
    ((Multiplicative.toAdd (constTateEquiv ℚ_[p] (PadicAlgCl p)
        ((constPDiv ℚ_[p] p).galTate (σ.restrictScalars ℚ_[p]) x)) : ℤ_[p]) : ℚ_[p]) =
      charRep L 0 σ ((Multiplicative.toAdd (constTateEquiv ℚ_[p] (PadicAlgCl p) x) : ℤ_[p]) :
        ℚ_[p]) := by
  rw [galTate_constPDiv, charRep_apply, chiL, chiPow_apply, zpow_zero, Units.val_one,
    PadicInt.coe_one, one_mul]

variable {L} [FiniteDimensional ℚ_[p] L]

/-- `V_p(ℚ_p/ℤ_p) ≅ ℚ_p(0)` is Hodge–Tate. -/
theorem isHodgeTate_constTate : IsHodgeTate (charRep L 0) :=
  isHodgeTate_charRep 0

/-- The Hodge–Tate weight of `V_p(ℚ_p/ℤ_p)` is `0`. -/
theorem htWeights_constTate : htWeights (charRep L 0) = {0} := by
  rw [htWeights_charRep, neg_zero]

end PadicHodge
