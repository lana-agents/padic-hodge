/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.PDivisible
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Data.ZMod.Units

/-!
# The `p`-divisible group `μ_{p^∞}`

`muPDiv R p`: the `p`-divisible group `{μ_{p^v}}` of height `1` ([BC, after Prop. 7.2.2]), with
`μ_{p^v} = D(ℤ/p^v) = Spec R[ℤ/p^v]` and transition maps induced by reduction
`ℤ/p^{v+1} → ℤ/p^v` (on characters: composition).
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

open FFGroupScheme

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]

instance (v : ℕ) : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- The cyclic group `ℤ/p^v`, written multiplicatively. -/
abbrev CycP (v : ℕ) : Type := Multiplicative (ZMod (p ^ v))

instance (v : ℕ) : Fintype (CycP p v) := inferInstanceAs (Fintype (ZMod (p ^ v)))

/-- Reduction `ℤ/p^{v+1} → ℤ/p^v`. -/
def redP (v : ℕ) : CycP p (v + 1) →* CycP p v :=
  AddMonoidHom.toMultiplicative
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom

theorem redP_surjective (v : ℕ) : Function.Surjective (redP p v) := by
  intro b
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd b).val : ZMod (p ^ (v + 1))), ?_⟩
  change (ZMod.cast ((((Multiplicative.toAdd b).val : ZMod (p ^ (v + 1))))) : ZMod (p ^ v)) =
    Multiplicative.toAdd b
  rw [ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ v)), ZMod.natCast_zmod_val]

/-- `μ_{p^v} = D(ℤ/p^v)`. -/
def muP (v : ℕ) : FFGroupScheme R := diag R (CycP p v)

/-- The inclusion `μ_{p^v} → μ_{p^{v+1}}`. -/
def muIncl (v : ℕ) : FFGroupScheme.Hom (muP R p v) (muP R p (v + 1)) :=
  MonoidAlgebra.mapDomainBialgHom R (redP p v)

theorem muIncl_surjective (v : ℕ) : Function.Surjective (muIncl R p v) := by
  intro a
  change ∃ b : MonoidAlgebra R (CycP p (v + 1)), MonoidAlgebra.mapDomainBialgHom R (redP p v) b = a
  induction a using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | single m r =>
    obtain ⟨m', rfl⟩ := redP_surjective p v m
    refine ⟨MonoidAlgebra.single m' r, ?_⟩
    change MonoidAlgebra.mapDomain (redP p v) (MonoidAlgebra.single m' r) = _
    rw [MonoidAlgebra.mapDomain_single]

theorem diagPointsEquiv_muIncl (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (x : (muP R p v).points S) :
    diagPointsEquiv (CycP p (v + 1)) S ((muIncl R p v).mapPoints S x) =
      (diagPointsEquiv (CycP p v) S x).comp (redP p v) := by
  refine MonoidHom.ext fun m => ?_
  change (ofConv x) ((MonoidAlgebra.mapDomainBialgHom R (redP p v)) (MonoidAlgebra.single m 1)) =
    (ofConv x) (MonoidAlgebra.single (redP p v m) 1)
  change (ofConv x) (MonoidAlgebra.mapDomain (redP p v) (MonoidAlgebra.single m 1)) = _
  rw [MonoidAlgebra.mapDomain_single]

/-- Characters of `ℤ/p^{v+1}` killed by `p^v` are exactly those factoring through `ℤ/p^v`. -/
theorem exists_comp_redP_iff (v : ℕ) {S : Type u} [CommRing S] (ψ : CycP p (v + 1) →* S) :
    (∃ φ : CycP p v →* S, φ.comp (redP p v) = ψ) ↔ ψ ^ (p ^ v) = 1 := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine MonoidHom.ext fun m => ?_
    have : (redP p v m) ^ (p ^ v) = 1 := by
      change Multiplicative.ofAdd ((p ^ v) • Multiplicative.toAdd (redP p v m)) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply, ← map_pow, this,
      map_one]
  · intro hψ
    -- lift through the surjection `redP` using a section
    let sec : CycP p v → CycP p (v + 1) := fun b =>
      Multiplicative.ofAdd ((Multiplicative.toAdd b).val : ZMod (p ^ (v + 1)))
    have hsec : Function.RightInverse sec (redP p v) := fun b => by
      change (ZMod.cast ((((Multiplicative.toAdd b).val : ZMod (p ^ (v + 1))))) : ZMod (p ^ v)) =
        Multiplicative.toAdd b
      rw [ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ v)), ZMod.natCast_zmod_val]
    have hker : (redP p v).ker ≤ ψ.ker := by
      intro a ha
      rw [MonoidHom.mem_ker] at ha ⊢
      -- `a = c^{p^v}` for some `c`
      have h1 : ((Multiplicative.toAdd a).val : ZMod (p ^ v)) = 0 := by
        have : (ZMod.cast (Multiplicative.toAdd a) : ZMod (p ^ v)) = 0 := by
          change Multiplicative.toAdd (redP p v a) = 0
          rw [ha]; rfl
        rwa [← ZMod.natCast_zmod_val (Multiplicative.toAdd a),
          ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ v))] at this
      rw [ZMod.natCast_eq_zero_iff] at h1
      obtain ⟨c, hc⟩ := h1
      have ha' : a = (Multiplicative.ofAdd (c : ZMod (p ^ (v + 1)))) ^ (p ^ v) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← ZMod.natCast_zmod_val (Multiplicative.toAdd a),
          hc]
        push_cast; ring
      rw [ha', map_pow, ← MonoidHom.pow_apply, hψ, MonoidHom.one_apply]
    have hψk : ∀ a b, redP p v a = redP p v b → ψ a = ψ b := by
      intro a b hab
      have hk : a⁻¹ * b ∈ (redP p v).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
      have h1 : ψ (a⁻¹ * b) = 1 := hker hk
      have e : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
      rw [e, map_mul, h1, mul_one]
    let φ : CycP p v →* S :=
      { toFun := fun b => ψ (sec b)
        map_one' := by
          rw [← map_one ψ]
          exact hψk _ _ (by rw [hsec, map_one])
        map_mul' := fun b1 b2 => by
          rw [← map_mul]
          exact hψk _ _ (by rw [hsec, map_mul, hsec, hsec]) }
    refine ⟨φ, MonoidHom.ext fun a => ?_⟩
    exact hψk _ _ (hsec _)

/-- **`μ_{p^∞}`** as a `p`-divisible group of height `1`. -/
def muPDiv [Nontrivial R] : PDivGroup R p where
  height := 1
  G := muP R p
  order_eq v := by
    rw [muP, order_diag, one_mul]
    change Fintype.card (ZMod (p ^ v)) = _
    exact ZMod.card _
  incl := muIncl R p
  incl_surjective := muIncl_surjective R p
  range_eq v S _ _ y := by
    set E := diagPointsEquiv (R := R) (CycP p (v + 1)) S
    constructor
    · rintro ⟨x, rfl⟩
      have := (exists_comp_redP_iff p v (E ((muIncl R p v).mapPoints S x))).mp
        ⟨diagPointsEquiv (CycP p v) S x, (diagPointsEquiv_muIncl R p v S x).symm⟩
      rwa [← map_pow, MulEquiv.map_eq_one_iff] at this
    · intro hy
      obtain ⟨φ, hφ⟩ := (exists_comp_redP_iff p v (E y)).mpr
        (by rw [← map_pow]; exact (MulEquiv.map_eq_one_iff E).mpr hy)
      refine ⟨(diagPointsEquiv (CycP p v) S).symm φ, E.injective ?_⟩
      rw [diagPointsEquiv_muIncl, MulEquiv.apply_symm_apply, hφ]

end PadicHodge
