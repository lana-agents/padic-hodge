/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.QuotientEpi
import PadicHodge.GroupScheme.DualPDivFree
import PadicHodge.GroupScheme.PDivisiblePoints

/-!
# The Cartier dual of an arbitrary `p`-divisible group over a local PID

[Hong, Prop. 2.1.7, Def. 2.1.8]: for a `p`-divisible group `G = (G_v)` of height `h` over a local
principal ideal domain `R` (e.g. `O_{K'}`, `ℤ_p`), the Cartier duals `G_v^∨` with the transposes
`quot_v^∨` of the quotient maps form a `p`-divisible group `G^∨` of height `h`
(**`PDivGroup.dualPDivGen`**). No connectedness is assumed. For `F[p^∞]` this is the
Cartier dual `PDivFGL.dualPDiv` of `FormalGroup/DualPDivFGL.lean` (both are `dualPDivOf` of
some `DualPDivData`, whose data do not enter the construction; `dualPDivOf_eq`).

We verify the freeness conditions `PDivGroup.DualPDivData` of `DualPDivFree.lean`
(`PDivGroup.dualPDivDataGen`):

* `incl1 v : G_1 → G_{v+1}` (iterated `i`) is a closed immersion, and `quot1 v : G_{v+1} → G_1`
  (iterated `quot`) satisfies `incl1 ∘ quot1 = [p^v]` (`incl1_quot1`);
* **`ker(quot_v) = G_1`** on points with values in every `R`-algebra (`exists_incl1_eq`, from the
  kernel condition of `G`), and `quot_v` is trivial on `G_1`;
* hence (`FFGroupScheme.Hom.range_eq_invariants`, [Hong, proof of Lemma 2.1.5 (iii)]) the image
  of `quot_v^* : A_v → A_{v+1}` is the algebra `B` of `G_1`-invariants, `A_{v+1}` is free of
  rank `p^h` over `B` with a `B`-linear retraction `r`, `r(1) = 1`
  (`Module.Basis.exists_retraction_one`), `|B| = |A_v|` (`Hom.order_eq_mul`), so
  `quot_v^* : A_v ≅ B` (Orzech) and `r` gives the `A_v`-linear retraction `retr v`;
* `ker(A_{v+1} → A_1) = A_{v+1} · quot_v^*(A_v⁺)` (`Hom.mem_span_of_apply_eq_zero`);
* `[p^v] = incl1 ∘ quot1` with `quot1^*` split injective (composite of the `quot^*`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 2.1.5, Prop. 2.1.7, Def. 2.1.8.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p)

/-! ### Iterated inclusions and quotient maps -/

/-- The iterated inclusion `G_1 → G_{v+1}`. -/
def incl1 : ∀ v : ℕ, FFGroupScheme.Hom (G.G 1) (G.G (v + 1))
  | 0 => BialgHom.id R (G.G 1).A
  | v + 1 => (incl1 v).comp (G.incl (v + 1))

/-- The iterated quotient map `G_{v+1} → G_1`. -/
def quot1 : ∀ v : ℕ, FFGroupScheme.Hom (G.G (v + 1)) (G.G 1)
  | 0 => BialgHom.id R (G.G 1).A
  | v + 1 => (G.quot (v + 1)).comp (quot1 v)

theorem incl1_succ_mapPoints (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (x : (G.G 1).points S) :
    (G.incl1 (v + 1)).mapPoints S x = (G.incl (v + 1)).mapPoints S ((G.incl1 v).mapPoints S x) :=
  rfl

theorem quot1_succ_mapPoints (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (G.G (v + 2)).points S) :
    (G.quot1 (v + 1)).mapPoints S y = (G.quot1 v).mapPoints S ((G.quot (v + 1)).mapPoints S y) :=
  rfl

theorem incl1_surjective (v : ℕ) : Function.Surjective (G.incl1 v) := by
  induction v with
  | zero => exact Function.surjective_id
  | succ v ih => exact ih.comp (G.incl_surjective (v + 1))

/-- `incl1 ∘ quot1 = [p^v]` on points. -/
theorem incl1_quot1 (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) :
    (G.incl1 v).mapPoints S ((G.quot1 v).mapPoints S y) = y ^ (p ^ v) := by
  induction v with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ v ih =>
    rw [quot1_succ_mapPoints, incl1_succ_mapPoints, ih, map_pow, G.incl_quot, ← pow_mul,
      ← pow_succ']

/-- A point of `G_{v+1}` killed by `p` comes from `G_1`. -/
theorem exists_incl1_eq (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) (hy : y ^ p = 1) : ∃ x, (G.incl1 v).mapPoints S x = y := by
  induction v with
  | zero => exact ⟨y, rfl⟩
  | succ v ih =>
    have hy' : y ^ (p ^ (v + 1)) = 1 := by rw [pow_succ', pow_mul, hy, one_pow]
    obtain ⟨y', rfl⟩ := (G.range_eq (v + 1) S y).mpr hy'
    have : y' ^ p = 1 := by
      apply G.mapPoints_injective (v + 1) S
      rw [map_pow, hy, map_one]
    obtain ⟨x, rfl⟩ := ih y' this
    exact ⟨x, rfl⟩

/-- **`ker(quot_v) = G_1`** on points. -/
theorem exists_incl1_eq_of_quot (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) (hy : (G.quot v).mapPoints S y = 1) :
    ∃ x, (G.incl1 v).mapPoints S x = y := by
  refine G.exists_incl1_eq v S y ?_
  have : y ∈ ((G.quot v).mapPoints S).ker := hy
  rw [G.ker_quot] at this
  exact this

/-- `quot_v` is trivial on `G_1`. -/
theorem quot_incl1 (v : ℕ) (S : Type u) [CommRing S] [Algebra R S] (x : (G.G 1).points S) :
    (G.quot v).mapPoints S ((G.incl1 v).mapPoints S x) = 1 := by
  have : (G.incl1 v).mapPoints S x ∈ (powMonoidHom p).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    have := G.pow_eq_one 1 S x
    rw [pow_one] at this
    rw [this, map_one]
  rw [← G.ker_quot] at this
  exact this

theorem quot_incl1_apply (v : ℕ) (a : (G.G v).A) :
    G.incl1 v (G.quot v a) = algebraMap R (G.G 1).A (counit (R := R) a) :=
  Hom.trivial_of_mapPoints (G.incl1 v) (G.quot v) (fun S _ _ z => G.quot_incl1 v S z) a

/-! ### The image of `quot_v^*` is the algebra of `G_1`-invariants -/

variable [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [hp : Fact p.Prime]

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
theorem order_G_one_pos : 0 < (G.G 1).order := by
  rw [G.order_eq]
  exact pow_pos hp.out.pos _

theorem range_quot_eq_invariants (v : ℕ) :
    (G.quot v).imageAlg = (G.incl1 v).invariants :=
  Hom.range_eq_invariants (G.incl1 v) (G.quot v) (G.incl1_surjective v) G.order_G_one_pos
    (G.quot_incl1_apply v) (G.exists_incl1_eq_of_quot v)

theorem quot_mem_invariants (v : ℕ) (a : (G.G v).A) : G.quot v a ∈ (G.incl1 v).invariants := by
  rw [← G.range_quot_eq_invariants v]
  exact ⟨a, rfl⟩

/-- `quot_v^* : A_v → B = A_{v+1}^{G_1}`. -/
def quotInv (v : ℕ) : (G.G v).A →ₐ[R] (G.incl1 v).invariants :=
  (G.quot v : (G.G v).A →ₐ[R] (G.G (v + 1)).A).codRestrict _ (G.quot_mem_invariants v)

theorem coe_quotInv (v : ℕ) (a : (G.G v).A) :
    (Subtype.val (show (G.incl1 v).invariants from G.quotInv v a)) = G.quot v a := rfl

theorem quotInv_surjective (v : ℕ) : Function.Surjective (G.quotInv v) := by
  rintro ⟨b, hb⟩
  rw [← G.range_quot_eq_invariants v] at hb
  obtain ⟨a, rfl⟩ := hb
  exact ⟨a, rfl⟩

theorem order_quotient_incl1 (v : ℕ) : (G.incl1 v).quotient.order = (G.G v).order := by
  have h := Hom.order_eq_mul (G.incl1_surjective v)
  rw [G.order_eq, G.order_eq, show G.height * (v + 1) = G.height * 1 + G.height * v
    by ring, pow_add] at h
  rw [G.order_eq]
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h).symm

theorem quotInv_bijective (v : ℕ) : Function.Bijective (G.quotInv v) :=
  haveI : Module.Finite R (G.incl1 v).invariants := (G.incl1 v).quotient.finite
  haveI : Module.Free R (G.incl1 v).invariants := (G.incl1 v).quotient.free
  OrzechProperty.bijective_of_surjective_of_finrank_le (G.quotInv v).toLinearMap
    (G.quotInv_surjective v) (by
      change (G.G v).order ≤ (G.incl1 v).quotient.order
      rw [G.order_quotient_incl1])

/-- **`quot_v^*` is injective.** -/
theorem quot_injective' (v : ℕ) :
    Function.Injective (G.quot v : (G.G v).A → (G.G (v + 1)).A) := fun _ _ h =>
  (G.quotInv_bijective v).1 (Subtype.val_injective h)

/-- `A_v ≅ B`. -/
def quotInvEquiv (v : ℕ) : (G.G v).A ≃ₐ[R] (G.incl1 v).invariants :=
  AlgEquiv.ofBijective (G.quotInv v) (G.quotInv_bijective v)

/-! ### The freeness data -/

theorem exists_retraction_invariants (v : ℕ) :
    ∃ r : (G.G (v + 1)).A →ₗ[(G.incl1 v).invariants] (G.incl1 v).invariants, r 1 = 1 := by
  obtain ⟨bas⟩ := Hom.nonempty_basis_invariants (G.incl1_surjective v)
  haveI : Nonempty (Fin (G.G 1).order) := ⟨⟨0, G.order_G_one_pos⟩⟩
  exact bas.exists_retraction_one

/-- The `B`-linear retraction `A_{v+1} → B`. -/
def retrInv (v : ℕ) :
    (G.G (v + 1)).A →ₗ[(G.incl1 v).invariants] (G.incl1 v).invariants :=
  (G.exists_retraction_invariants v).choose

theorem retrInv_one (v : ℕ) : G.retrInv v 1 = 1 := (G.exists_retraction_invariants v).choose_spec

/-- The `A_v`-linear retraction `A_{v+1} → A_v` of `quot_v^*`. -/
def retrGen (v : ℕ) : (G.G (v + 1)).A →ₗ[R] (G.G v).A :=
  (G.quotInvEquiv v).symm.toLinearMap ∘ₗ ((G.retrInv v).restrictScalars R)

theorem retrGen_mul (v : ℕ) (b : (G.G v).A) (x : (G.G (v + 1)).A) :
    G.retrGen v (G.quot v b * x) = b * G.retrGen v x := by
  have h1 : G.quot v b * x = (G.quotInv v b : (G.incl1 v).invariants) • x := by
    rw [Algebra.smul_def]
    rfl
  simp only [retrGen, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1,
    (G.retrInv v).map_smul, smul_eq_mul, map_mul]
  congr 1
  exact (G.quotInvEquiv v).symm_apply_apply b

theorem retrGen_one (v : ℕ) : G.retrGen v 1 = 1 := by
  simp only [retrGen, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply, retrInv_one, map_one]

theorem retrGen_quot (v : ℕ) (b : (G.G v).A) : G.retrGen v (G.quot v b) = b := by
  simpa [G.retrGen_one] using G.retrGen_mul v b 1

/-- The `R`-linear retraction of `quot1^*`. -/
def quot1Retr : ∀ v : ℕ, (G.G (v + 1)).A →ₗ[R] (G.G 1).A
  | 0 => LinearMap.id
  | v + 1 => quot1Retr v ∘ₗ G.retrGen (v + 1)

theorem quot1Retr_quot1 (v : ℕ) (c : (G.G 1).A) : G.quot1Retr v (G.quot1 v c) = c := by
  induction v with
  | zero => rfl
  | succ v ih =>
    change G.quot1Retr v (G.retrGen (v + 1) (G.quot (v + 1) (G.quot1 v c))) = c
    rw [retrGen_quot, ih]

theorem ker_incl1_le (v : ℕ) :
    RingHom.ker (G.incl1 v : (G.G (v + 1)).A →ₐ[R] (G.G 1).A) ≤
      Ideal.span ((G.quot v : (G.G v).A → (G.G (v + 1)).A) '' {b | counit (R := R) b = 0}) := by
  intro a ha
  have h := Hom.mem_span_of_apply_eq_zero (G.incl1_surjective v) (RingHom.mem_ker.mp ha)
  refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ _) h
  rintro _ ⟨b, hb, rfl⟩
  rw [← G.range_quot_eq_invariants v] at hb
  obtain ⟨c, rfl⟩ := hb
  refine Ideal.subset_span ⟨c - algebraMap R (G.G v).A (counit (R := R) c), ?_, ?_⟩
  · change counit (R := R) (c - algebraMap R (G.G v).A (counit (R := R) c)) = 0
    rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
  · rw [map_sub, AlgHomClass.commutes]
    exact congrArg (fun r => G.quot v c - algebraMap R (G.G (v + 1)).A r)
      (CoalgHomClass.counit_comp_apply (G.quot v) c).symm

/-- **The freeness data of the Cartier dual** for an arbitrary `p`-divisible group over a local
PID. -/
def dualPDivDataGen : G.DualPDivData where
  retr := G.retrGen
  retr_mul := G.retrGen_mul
  retr_one := G.retrGen_one
  res v := (G.incl1 v : (G.G (v + 1)).A →ₐ[R] (G.G 1).A)
  res_surjective := G.incl1_surjective
  ker_res := G.ker_incl1_le
  mulP v := (G.quot1 v : (G.G 1).A →ₗ[R] (G.G (v + 1)).A)
  mulP_res v a := by
    have h := congrArg (fun z : (G.G (v + 1)).points (G.G (v + 1)).A => ofConv z a)
      (G.incl1_quot1 v (G.G (v + 1)).univPt)
    exact h
  mulPRetr := G.quot1Retr
  mulPRetr_mulP := G.quot1Retr_quot1

/-- **The Cartier dual `G^∨ = (G_v^∨, quot_v^∨)`** of a `p`-divisible group over a local PID
([Hong, Prop. 2.1.7 (2), Def. 2.1.8]). -/
abbrev dualPDivGen : PDivGroup R p := dualPDivOf G.dualPDivDataGen

theorem dualPDivGen_G (v : ℕ) : G.dualPDivGen.G v = (G.G v).dual := rfl

theorem dualPDivGen_incl (v : ℕ) : G.dualPDivGen.incl v = (G.quot v).dual := rfl

theorem dualPDivGen_height : G.dualPDivGen.height = G.height := rfl

/-- `T_p(G^∨) = DualTate G`. -/
theorem tateModule_dualPDivGen (S : Type u) [CommRing S] [Algebra R S] :
    G.dualPDivGen.TateModule S = G.DualTate S :=
  tateModule_dualPDivOf _ S

omit [IsDomain R] [IsPrincipalIdealRing R] hp in
/-- The construction `dualPDivOf` does not depend on the freeness data. -/
theorem dualPDivOf_eq (D D' : G.DualPDivData) : dualPDivOf D = dualPDivOf D' := rfl

end PDivGroup

end PadicHodge
