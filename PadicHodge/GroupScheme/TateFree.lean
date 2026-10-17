/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierDualPDiv
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# `T_p G(ℚ̄_p) ≅ ℤ_p^h`

([Stix, §11.2], [Hong, Lemma 3.4.1]: the Tate module of a `p`-divisible group of height `h` over
a field of characteristic `0` is free of rank `h` over `ℤ_p`.) Standard arguments, written up here,
for a `p`-divisible group `G` over `R` and an `R`-algebra `S` such that the quotient maps are
surjective on `S`-points and `#G_v(S) = p^{hv}` (e.g. `R = ℚ_p`, `S = ℚ̄_p`):

* `quotLE h : G_b(S) → G_a(S)` for `a ≤ b` (iterated quotient maps, `Nat.leRecOn`), with
  `quotLE_eq_one_iff`: `ker(quotLE) = G_b(S)[p^{b-a}]`; `TateModule.quotLE_apply`;
* `TateModule.proj_surjective`: `T_p G(S) → G_v(S)` is surjective (lifting along chosen
  sections of the quotient maps, `liftLE`);
* `phiLevel t v : (ℤ/p^v)^h → G_v(S)`, `c ↦ ∏ (t_i)_v^{c_i}` for `t_1, …, t_h ∈ T_p G(S)`; if the
  `(t_i)_1` are `𝔽_p`-independent in `G_1(S)`, then `phiLevel t v` is injective (induction on `v`,
  using `quotLE_eq_one_iff`) and, by counting, bijective;
* `phi t : ℤ_p^h → T_p G(S)` is then bijective (`tateEquivOfBasis`);
* `exists_basis`: `G_1(S)` is an `𝔽_p`-vector space of dimension `h`; lifting a basis to
  `T_p G(S)` gives such `t`;
* **`PDivGroup.tateEquivZp : T_p G(ℚ̄_p) ≃* ℤ_p^h`** for `G` over `ℚ_p`.
-/

noncomputable section

open WithConv

namespace PadicHodge

universe u

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p) (S : Type u) [CommRing S]
  [Algebra R S]

/-! ### Iterated quotient maps -/

/-- The iterated quotient map `G_b(S) → G_a(S)` for `a ≤ b`. -/
def quotLE {a b : ℕ} (h : a ≤ b) : (G.G b).points S →* (G.G a).points S :=
  Nat.leRecOn (C := fun k => (G.G k).points S →* (G.G a).points S) h
    (fun {k} f => f.comp ((G.quot k).mapPoints S)) (MonoidHom.id _)

theorem quotLE_self (a : ℕ) (y : (G.G a).points S) : G.quotLE S (le_refl a) y = y := by
  rw [quotLE, Nat.leRecOn_self]
  rfl

theorem quotLE_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) (y : (G.G (b + 1)).points S) :
    G.quotLE S h' y = G.quotLE S h ((G.quot b).mapPoints S y) := by
  rw [quotLE, Nat.leRecOn_succ h]
  rfl

theorem quotLE_succ_left {a b : ℕ} (h : a + 1 ≤ b) (h' : a ≤ b) (y : (G.G b).points S) :
    (G.quot a).mapPoints S (G.quotLE S h y) = G.quotLE S h' y := by
  induction b, h using Nat.le_induction with
  | base =>
    rw [quotLE_self, G.quotLE_succ S (le_refl a), quotLE_self]
  | succ b hb ih =>
    rw [G.quotLE_succ S hb, G.quotLE_succ S (by omega), ih]

theorem TateModule.quotLE_apply (x : G.TateModule S) {a b : ℕ} (h : a ≤ b) :
    G.quotLE S h (x.1 b) = x.1 a := by
  induction b, h using Nat.le_induction with
  | base => exact G.quotLE_self S a _
  | succ b hb ih =>
    rw [G.quotLE_succ S hb, ← TateModule.val_eq_quot, ih]

/-- **`ker(G_b(S) → G_a(S)) = G_b(S)[p^{b-a}]`.** -/
theorem quotLE_eq_one_iff {a b : ℕ} (h : a ≤ b) (y : (G.G b).points S) :
    G.quotLE S h y = 1 ↔ y ^ (p ^ (b - a)) = 1 := by
  induction b, h using Nat.le_induction with
  | base => rw [quotLE_self, Nat.sub_self, pow_zero, pow_one]
  | succ b hb ih =>
    rw [G.quotLE_succ S hb, ih, ← map_pow, ← MonoidHom.mem_ker, G.ker_quot,
      MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul, ← pow_succ,
      show b + 1 - a = b - a + 1 by omega]

/-! ### Surjectivity of `T_p G(S) → G_v(S)` -/

/-- The projection `T_p G(S) → G_v(S)`. -/
def TateModule.proj (v : ℕ) : G.TateModule S →* (G.G v).points S :=
  (Pi.evalMonoidHom (fun w => (G.G w).points S) v).comp (G.TateModule S).subtype

@[simp] theorem TateModule.proj_apply (v : ℕ) (x : G.TateModule S) :
    TateModule.proj G S v x = x.1 v := rfl

section Lift

variable (hsurj : ∀ v, Function.Surjective ((G.quot v).mapPoints S))

include hsurj

/-- Iterated chosen lifts `G_a(S) → G_b(S)` for `a ≤ b`. -/
def liftLE {a b : ℕ} (h : a ≤ b) (y : (G.G a).points S) : (G.G b).points S :=
  Nat.leRecOn (C := fun k => (G.G k).points S) h
    (fun {k} z => Function.surjInv (hsurj k) z) y

theorem liftLE_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) (y : (G.G a).points S) :
    G.liftLE S hsurj h' y = Function.surjInv (hsurj b) (G.liftLE S hsurj h y) := by
  rw [liftLE, Nat.leRecOn_succ h]
  rfl

theorem quotLE_liftLE {a b : ℕ} (h : a ≤ b) (y : (G.G a).points S) :
    G.quotLE S h (G.liftLE S hsurj h y) = y := by
  induction b, h using Nat.le_induction with
  | base => rw [quotLE_self, liftLE, Nat.leRecOn_self]
  | succ b hb ih =>
    rw [G.liftLE_succ S hsurj hb, G.quotLE_succ S hb, Function.surjInv_eq (hsurj b), ih]

/-- **`T_p G(S) → G_v(S)` is surjective** when the quotient maps are surjective on `S`-points. -/
theorem TateModule.proj_surjective (v : ℕ) : Function.Surjective (TateModule.proj G S v) := by
  intro y
  let z : ∀ w, (G.G w).points S := fun w =>
    G.quotLE S (Nat.le_add_left w v) (G.liftLE S hsurj (Nat.le_add_right v w) y)
  have hz : ∀ w, (G.quot w).mapPoints S (z (w + 1)) = z w := by
    intro w
    simp only [z]
    rw [G.quotLE_succ_left S (by omega) (by omega), G.liftLE_succ S hsurj (Nat.le_add_right v w),
      G.quotLE_succ S (Nat.le_add_left w v), Function.surjInv_eq (hsurj (v + w))]
  refine ⟨⟨z, fun w => ?_⟩, ?_⟩
  · rw [← G.incl_quot w (z (w + 1)), hz]
  · exact G.quotLE_liftLE S hsurj _ y

end Lift

/-! ### Coordinates -/

theorem pow_mod_eq {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (m : ℕ) :
    x ^ (m % n) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

variable [NeZero p] {h : ℕ} (t : Fin h → G.TateModule S)

/-- `c ↦ ∏_i (t_i)_v^{c_i}`, `(ℤ/p^v)^h → G_v(S)`. -/
def phiLevel (v : ℕ) :
    Multiplicative (Fin h → ZMod (p ^ v)) →* (G.G v).points S where
  toFun c := ∏ i, ((t i).1 v) ^ (Multiplicative.toAdd c i).val
  map_one' := by simp
  map_mul' c c' := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, toAdd_mul, Pi.add_apply, ZMod.val_add, pow_mod_eq (G.pow_eq_one v S _)]

theorem phiLevel_apply (v : ℕ) (c : Multiplicative (Fin h → ZMod (p ^ v))) :
    G.phiLevel S t v c = ∏ i, ((t i).1 v) ^ (Multiplicative.toAdd c i).val := rfl

/-- Reduction `(ℤ/p^{v+1})^h → (ℤ/p^v)^h`. -/
def reduce (v : ℕ) (c : Multiplicative (Fin h → ZMod (p ^ (v + 1)))) :
    Multiplicative (Fin h → ZMod (p ^ v)) :=
  Multiplicative.ofAdd fun i => ((Multiplicative.toAdd c i).val : ZMod (p ^ v))

theorem quot_phiLevel (v : ℕ)
    (c : Multiplicative (Fin h → ZMod (p ^ (v + 1)))) :
    (G.quot v).mapPoints S (G.phiLevel S t (v + 1) c) = G.phiLevel S t v (reduce v c) := by
  apply G.mapPoints_injective v S
  rw [G.incl_quot, phiLevel_apply, phiLevel_apply, map_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hx : ((t i).1 (v + 1) ^ p) ^ (p ^ v) = 1 := by
    rw [← pow_mul, ← pow_succ']
    exact G.pow_eq_one (v + 1) S _
  rw [map_pow, (t i).2 v, reduce, toAdd_ofAdd, ZMod.val_natCast, pow_mod_eq hx, ← pow_mul,
    ← pow_mul, mul_comm]

/-- **Injectivity of the coordinates** if the `(t_i)_1` are independent over `𝔽_p`. -/
theorem phiLevel_injective [hp : Fact p.Prime]
    (hbasis : ∀ d : Fin h → ℕ, (∀ i, d i < p) → ∏ i, ((t i).1 1) ^ d i = 1 → ∀ i, d i = 0)
    (v : ℕ) : Function.Injective (G.phiLevel S t v) := by
  induction v with
  | zero =>
    intro c c' _
    apply Multiplicative.toAdd.injective
    funext i
    apply ZMod.val_injective
    have h1 := ZMod.val_lt (Multiplicative.toAdd c i)
    have h2 := ZMod.val_lt (Multiplicative.toAdd c' i)
    have h1' := h1.trans_le (pow_zero p).le
    have h2' := h2.trans_le (pow_zero p).le
    omega
  | succ v ih =>
    rw [injective_iff_map_eq_one]
    intro c hc
    -- reduction mod `p^v` vanishes
    have hred : reduce v c = 1 := by
      apply ih
      rw [← quot_phiLevel, hc, map_one, map_one]
    have hdvd : ∀ i, p ^ v ∣ (Multiplicative.toAdd c i).val := by
      intro i
      have := congrFun (congrArg Multiplicative.toAdd hred) i
      simp only [reduce, toAdd_ofAdd, toAdd_one, Pi.zero_apply] at this
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    choose d hd using hdvd
    have hdlt : ∀ i, d i < p := by
      intro i
      have h1 := ZMod.val_lt (Multiplicative.toAdd c i)
      rw [hd i, pow_succ] at h1
      exact Nat.lt_of_mul_lt_mul_left h1
    have hprod : (∏ i, ((t i).1 (v + 1)) ^ d i) ^ (p ^ v) = 1 := by
      rw [← Finset.prod_pow, ← hc, phiLevel_apply]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hd i, ← pow_mul, mul_comm]
    have h1 : G.quotLE S (show 1 ≤ v + 1 by omega) (∏ i, ((t i).1 (v + 1)) ^ d i) = 1 := by
      rw [quotLE_eq_one_iff, Nat.add_sub_cancel]
      exact hprod
    rw [map_prod] at h1
    simp only [map_pow, TateModule.quotLE_apply] at h1
    have h0 := hbasis d hdlt h1
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_one, Pi.zero_apply, ← ZMod.val_eq_zero, hd i, h0 i, mul_zero]

omit [NeZero p] in
theorem card_coords [NeZero p] (v : ℕ) :
    Nat.card (Multiplicative (Fin h → ZMod (p ^ v))) = p ^ (h * v) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, ← pow_mul, mul_comm]

theorem phiLevel_bijective [hp : Fact p.Prime]
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w)) (hh : h = G.height)
    (hbasis : ∀ d : Fin h → ℕ, (∀ i, d i < p) → ∏ i, ((t i).1 1) ^ d i = 1 → ∀ i, d i = 0)
    (v : ℕ) : Function.Bijective (G.phiLevel S t v) := by
  have : Finite ((G.G v).points S) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  refine (G.phiLevel_injective S t hbasis v).bijective_of_nat_card_le ?_
  rw [hcard, card_coords, hh]

/-- `ℤ_p^h → T_p G(S)`, `a ↦ ∏ t_i^{a_i}`. -/
def phi [hp : Fact p.Prime] : Multiplicative (Fin h → ℤ_[p]) →* G.TateModule S where
  toFun a := ⟨fun v => G.phiLevel S t v
      (Multiplicative.ofAdd fun i => PadicInt.toZModPow v (Multiplicative.toAdd a i)), by
    intro v
    have key : (Multiplicative.ofAdd fun i => PadicInt.toZModPow v (Multiplicative.toAdd a i)) =
        reduce v (Multiplicative.ofAdd fun i =>
          PadicInt.toZModPow (v + 1) (Multiplicative.toAdd a i)) := by
      apply Multiplicative.toAdd.injective
      funext i
      apply ZMod.val_injective
      simp only [reduce, toAdd_ofAdd, ZMod.val_natCast]
      exact (expo_succ _ v).symm
    change (G.incl v).mapPoints S (G.phiLevel S t v _) = (G.phiLevel S t (v + 1) _) ^ p
    rw [← G.incl_quot, quot_phiLevel, key]⟩
  map_one' := Subtype.ext <| funext fun v => by
    change G.phiLevel S t v _ = 1
    convert map_one (G.phiLevel S t v)
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' a b := Subtype.ext <| funext fun v => by
    change G.phiLevel S t v _ = G.phiLevel S t v _ * G.phiLevel S t v _
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext i
    simp

theorem phi_apply [hp : Fact p.Prime] (a : Multiplicative (Fin h → ℤ_[p])) (v : ℕ) :
    (G.phi S t a).1 v = G.phiLevel S t v
      (Multiplicative.ofAdd fun i => PadicInt.toZModPow v (Multiplicative.toAdd a i)) := rfl

theorem phi_bijective [hp : Fact p.Prime]
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w)) (hh : h = G.height)
    (hbasis : ∀ d : Fin h → ℕ, (∀ i, d i < p) → ∏ i, ((t i).1 1) ^ d i = 1 → ∀ i, d i = 0) :
    Function.Bijective (G.phi S t) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro a ha
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_one, Pi.zero_apply]
    refine PadicInt.ext_of_toZModPow.mp fun v => ?_
    have h1 := congrArg (fun x : G.TateModule S => x.1 v) ha
    simp only [phi_apply] at h1
    have h2 := G.phiLevel_injective S t hbasis v (h1.trans (map_one _).symm)
    have := congrFun (congrArg Multiplicative.toAdd h2) i
    simpa using this
  · intro x
    let e : ∀ v, Multiplicative (Fin h → ZMod (p ^ v)) ≃* (G.G v).points S := fun v =>
      MulEquiv.ofBijective _ (G.phiLevel_bijective S t hcard hh hbasis v)
    let c : ∀ v, Fin h → ZMod (p ^ v) := fun v => Multiplicative.toAdd ((e v).symm (x.1 v))
    have hc : ∀ v, G.phiLevel S t v (Multiplicative.ofAdd (c v)) = x.1 v := fun v =>
      (e v).apply_symm_apply _
    have hred : ∀ v i, (c (v + 1) i).val % p ^ v = (c v i).val := by
      intro v i
      have h1 : reduce v (Multiplicative.ofAdd (c (v + 1))) = Multiplicative.ofAdd (c v) := by
        apply G.phiLevel_injective S t hbasis v
        rw [← quot_phiLevel, hc, hc, ← TateModule.val_eq_quot]
      have := congrArg (fun z : Multiplicative (Fin h → ZMod (p ^ v)) =>
        ZMod.val (Multiplicative.toAdd z i)) h1
      simp only [reduce, toAdd_ofAdd, ZMod.val_natCast] at this
      exact this
    have hcompat : ∀ i v, (p : ℤ) ^ v ∣ ((c (v + 1) i).val : ℤ) - (c v i).val := by
      intro i v
      have h : (c v i).val ≡ (c (v + 1) i).val [MOD p ^ v] := by
        change _ % _ = _ % _
        rw [hred, Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have := Nat.modEq_iff_dvd.mp h
      push_cast at this ⊢
      exact this
    let a : Fin h → ℤ_[p] := fun i =>
      PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (fun v => ((c v i).val : ℤ)) p (hcompat i))
    refine ⟨Multiplicative.ofAdd a, Subtype.ext <| funext fun v => ?_⟩
    rw [phi_apply, ← hc v]
    congr 2
    funext i
    rw [toAdd_ofAdd, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, Int.cast_natCast,
      ZMod.natCast_zmod_val]
    exact hcompat i

/-! ### A basis of `G_1(S)` -/

omit [NeZero p] in
/-- A finite `𝔽_p`-vector space of cardinality `p^n` has `n` independent vectors. -/
theorem exists_independent_of_card [hp : Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {n : ℕ} (hcard : Nat.card V = p ^ n) :
    ∃ e : Fin n → V, ∀ d : Fin n → ℕ, (∀ i, d i < p) → ∑ i, d i • e i = 0 → ∀ i, d i = 0 := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) V = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hcard] at h1
    exact (Nat.pow_right_injective hp.out.two_le h1).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) V hrank
  refine ⟨fun i => b i, fun d hd hsum i => ?_⟩
  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hsum' : ∑ i, ((d i : ℕ) : ZMod p) • b i = 0 := by
    simp_rw [Nat.cast_smul_eq_nsmul]
    exact hsum
  have := hli _ hsum' i
  rw [ZMod.natCast_eq_zero_iff] at this
  exact Nat.eq_zero_of_dvd_of_lt this (hd i)

omit [NeZero p] in
/-- `G_1(S)` has `h` elements `e_i` independent over `𝔽_p`, if `#G_1(S) = p^h`. -/
theorem exists_basis_level_one [hp : Fact p.Prime]
    (hcard : Nat.card ((G.G 1).points S) = p ^ G.height) :
    ∃ e : Fin G.height → (G.G 1).points S,
      ∀ d : Fin G.height → ℕ, (∀ i, d i < p) → ∏ i, (e i) ^ d i = 1 → ∀ i, d i = 0 := by
  have hkill : ∀ x : Additive ((G.G 1).points S), p • x = 0 := fun x => by
    change Additive.ofMul (Additive.toMul x ^ p) = 0
    have := G.pow_eq_one 1 S (Additive.toMul x)
    rw [pow_one] at this
    rw [this]
    rfl
  letI : Module (ZMod p) (Additive ((G.G 1).points S)) := AddCommGroup.zmodModule hkill
  have hfin : Finite (Additive ((G.G 1).points S)) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card ((G.G 1).points S) ≠ 0
      rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨e, he⟩ := exists_independent_of_card (V := Additive ((G.G 1).points S)) hcard
  refine ⟨fun i => Additive.toMul (e i), fun d hd hprod => he d hd ?_⟩
  change Additive.ofMul (∏ i, (Additive.toMul (e i)) ^ d i) = Additive.ofMul 1
  rw [hprod]

omit [NeZero p] in
/-- **`T_p G(S) ≅ ℤ_p^h`** if the quotient maps are surjective on `S`-points and
`#G_v(S) = p^{hv}`. -/
theorem exists_tateEquiv [hp : Fact p.Prime]
    (hsurj : ∀ v, Function.Surjective ((G.quot v).mapPoints S))
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w)) :
    Nonempty (Multiplicative (Fin G.height → ℤ_[p]) ≃* G.TateModule S) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨e, he⟩ := G.exists_basis_level_one S (by rw [hcard, mul_one])
  choose t ht using fun i => TateModule.proj_surjective G S hsurj 1 (e i)
  refine ⟨MulEquiv.ofBijective (G.phi S t) (G.phi_bijective S t hcard rfl ?_)⟩
  intro d hd hprod
  apply he d hd
  simpa [← ht] using hprod

end PDivGroup

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup ℚ_[p] p)

/-- **`T_p G(ℚ̄_p) ≅ ℤ_p^h`** for a `p`-divisible group of height `h` over `ℚ_p`. -/
def tateEquivZp : Multiplicative (Fin G.height → ℤ_[p]) ≃* G.TateModule (PadicAlgCl p) :=
  (G.exists_tateEquiv (PadicAlgCl p) G.quot_surjective_padicAlgCl
    G.card_points_padicAlgCl).some

/-- `T_p G(ℚ̄_p) → G_v(ℚ̄_p)` is surjective. -/
theorem proj_surjective_padicAlgCl (v : ℕ) :
    Function.Surjective (TateModule.proj G (PadicAlgCl p) v) :=
  TateModule.proj_surjective G _ G.quot_surjective_padicAlgCl v

end PDivGroup

end PadicHodge
