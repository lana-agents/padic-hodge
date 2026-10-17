/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Constant

/-!
# Functoriality and points of constant group schemes

For a homomorphism `h : M →* M'` of finite commutative groups, `f ↦ f ∘ h` is a bialgebra map
`R^{M'} → R^M`, i.e. a homomorphism `constMap h : M_R → M'_R` of finite flat group schemes; it is
a closed immersion (`constMap_surjective`) if `h` is injective.

Points of `M_R` over an arbitrary commutative `R`-algebra `S` (not necessarily a domain): an
`R`-algebra map `y : R^M → S` is determined by the values `ptVal y m = y(e_m)`, which form a
family of orthogonal idempotents summing to `1` (`ptVal_mul_ptVal`, `sum_ptVal`); conversely every
such family comes from a point (`ofIdem`). In these terms

* `ptVal_mul`: `(y z)(e_k) = ∑_a y(e_a) z(e_{a⁻¹ k})`;
* `ptVal_pow`: `y^k(e_m) = ∑_{m' : m'^k = m} y(e_{m'})`;
* `pow_eq_one_iff`: `y^n = 1 ↔ y(e_m) = 0` whenever `m^n ≠ 1`;
* `ptVal_mapPoints`: `(h_* x)(e_{m'}) = ∑_{h m = m'} x(e_m)`;
* `exists_mapPoints_eq_iff`: for injective `h`, `y` lies in the image of `h_*` iff
  `y(e_{m'}) = 0` for all `m' ∉ range h`.

We work with the explicit comultiplication `ConstGS.comul` on `M → R` and only pass to
`(const R M).A` for the bialgebra structure (Mathlib also has the product coalgebra structure on
`M → R`, which is a different one).
-/

noncomputable section

open TensorProduct WithConv

namespace PadicHodge

open ConstGS

universe u

variable {R : Type u} [CommRing R]

namespace ConstGS

variable {M : Type} [CommGroup M] [Fintype M] [DecidableEq M]

variable (R) in
/-- Evaluation of a tensor `∑ f ⊗ g ∈ R^M ⊗ R^M` at `(m, n)`. -/
def evT (m n : M) : (M → R) ⊗[R] (M → R) →ₗ[R] R :=
  LinearMap.mul' R R ∘ₗ TensorProduct.map (LinearMap.proj m) (LinearMap.proj n)

omit [CommGroup M] [Fintype M] [DecidableEq M] in
theorem evT_tmul (m n : M) (f g : M → R) : evT R m n (f ⊗ₜ g) = f m * g n := rfl

omit [CommGroup M] in
theorem eq_sum_evT (x : (M → R) ⊗[R] (M → R)) :
    x = ∑ m, ∑ n, evT R m n x • (e R M m ⊗ₜ[R] e R M n) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  | tmul f g =>
    conv_lhs => rw [eq_sum f, eq_sum g]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TensorProduct.tmul_smul, smul_smul, evT_tmul]

omit [CommGroup M] [Fintype M] [DecidableEq M] in
theorem tensor_ext [Finite M] {x y : (M → R) ⊗[R] (M → R)}
    (h : ∀ m n, evT R m n x = evT R m n y) : x = y := by
  classical
  have := Fintype.ofFinite M
  rw [eq_sum_evT x, eq_sum_evT y]
  simp only [h]

theorem evT_comul (g : M → R) (m n : M) : evT R m n (comul R M g) = g (m * n) := by
  simp [comul_apply, evT_tmul, e_apply]

end ConstGS

namespace FFGroupScheme

variable {M M' : Type} [CommGroup M] [Fintype M] [DecidableEq M] [CommGroup M'] [Fintype M']
  [DecidableEq M']

omit [Fintype M] [DecidableEq M] [Fintype M'] [DecidableEq M'] in
theorem evT_map_funLeft (h : M →* M') (x : (M' → R) ⊗[R] (M' → R)) (m n : M) :
    evT R m n (TensorProduct.map (LinearMap.funLeft R R h) (LinearMap.funLeft R R h) x) =
      evT R (h m) (h n) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f g => rfl

theorem map_funLeft_comul (h : M →* M') (g : M' → R) :
    TensorProduct.map (LinearMap.funLeft R R h) (LinearMap.funLeft R R h) (comul R M' g) =
      comul R M (g ∘ h) := by
  refine tensor_ext fun m n => ?_
  rw [evT_map_funLeft, evT_comul, evT_comul, Function.comp_apply, map_mul]

variable (R) in
/-- The algebra map `R^{M'} → R^M`, `f ↦ f ∘ h`. -/
def constMapAlg (h : M →* M') : (const R M').A →ₐ[R] (const R M).A where
  toFun := fun (f : M' → R) => f ∘ h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem constMapAlg_apply (h : M →* M') (f : M' → R) (m : M) :
    (constMapAlg R h f : M → R) m = f (h m) := rfl

variable (R) in
/-- The homomorphism `M_R → M'_R` induced by `h : M →* M'`. -/
def constMap (h : M →* M') : Hom (const R M) (const R M') :=
  BialgHom.ofAlgHom (constMapAlg R h)
    (AlgHom.ext fun f => by
      change (f : M' → R) (h 1) = f 1
      rw [map_one])
    (AlgHom.ext fun f => by
      change TensorProduct.map (LinearMap.funLeft R R h) (LinearMap.funLeft R R h)
        (comul R M' f) = comul R M (f ∘ h)
      exact map_funLeft_comul h f)

theorem constMap_apply (h : M →* M') (f : (const R M').A) :
    constMap R h f = constMapAlg R h f := rfl

/-- `constMap h` is a closed immersion if `h` is injective. -/
theorem constMap_surjective {h : M →* M'} (hinj : Function.Injective h) :
    Function.Surjective (constMap R h) := by
  intro g
  refine ⟨(Function.extend h (g : M → R) 0 : M' → R), ?_⟩
  funext m
  exact hinj.extend_apply _ _ m

/-! ### Points over an arbitrary algebra -/

section Points

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The value `y(e_m)` of a point `y ∈ M_R(S)`. -/
def ptVal (y : (const R M).points S) (m : M) : S := (ofConv y) (eA (R := R) m)

variable {S}

theorem ptVal_mul_ptVal (y : (const R M).points S) (m n : M) :
    ptVal S y m * ptVal S y n = if m = n then ptVal S y m else 0 := by
  rw [ptVal, ptVal, ← map_mul]
  have : eA (R := R) m * eA n = if m = n then eA m else 0 := e_mul_e m n
  rw [this]
  split_ifs <;> simp

theorem sum_ptVal (y : (const R M).points S) : ∑ m, ptVal S y m = 1 := by
  simp only [ptVal]
  rw [← map_sum]
  have : ∑ m, eA (R := R) (M := M) m = 1 := sum_e
  rw [this, map_one]

theorem eq_sum_ptVal (y : (const R M).points S) (f : (const R M).A) :
    (ofConv y) f = ∑ m, algebraMap R S ((f : M → R) m) * ptVal S y m := by
  conv_lhs => rw [show f = ∑ m, (f : M → R) m • eA (R := R) m from eq_sum f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def, ptVal]

theorem points_ext' {y z : (const R M).points S} (h : ∀ m, ptVal S y m = ptVal S z m) :
    y = z := by
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun f => ?_
  rw [eq_sum_ptVal, eq_sum_ptVal]
  simp only [h]

theorem ptVal_one (m : M) :
    ptVal S (1 : (const R M).points S) m = if m = 1 then 1 else 0 := by
  rw [ptVal, AlgHom.convOne_apply]
  change algebraMap R S (ConstGS.counit R M (e R M m)) = _
  rw [counit_e]
  split_ifs <;> simp

theorem ptVal_mul (y z : (const R M).points S) (k : M) :
    ptVal S (y * z) k = ∑ a, ptVal S y a * ptVal S z (a⁻¹ * k) := by
  change (ofConv (y * z)) (eA (R := R) k) = ∑ a, (ofConv y) (eA (R := R) a) *
    (ofConv z) (eA (R := R) (a⁻¹ * k))
  rw [AlgHom.convMul_apply]
  simp only [comul_eA, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

theorem ptVal_pow (y : (const R M).points S) (k : ℕ) (m : M) :
    ptVal S (y ^ k) m = ∑ m', if m' ^ k = m then ptVal S y m' else 0 := by
  induction k generalizing m with
  | zero =>
    rw [pow_zero, ptVal_one]
    simp only [pow_zero]
    by_cases hm : m = 1
    · subst hm; simp [sum_ptVal]
    · rw [if_neg hm]; simp [Ne.symm hm]
  | succ k ih =>
    rw [pow_succ, ptVal_mul]
    simp only [ih, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [Finset.sum_eq_single (m' ^ k)]
    · rw [if_pos rfl, ptVal_mul_ptVal]
      by_cases h : m' ^ (k + 1) = m
      · rw [if_pos h, if_pos (by rw [← h, pow_succ, inv_mul_cancel_left])]
      · rw [if_neg h, if_neg (fun h' => h (by
          rw [pow_succ]; nth_rewrite 2 [h']; exact mul_inv_cancel_left _ _))]
    · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
    · simp

theorem pow_eq_one_iff (y : (const R M).points S) (n : ℕ) :
    y ^ n = 1 ↔ ∀ m, m ^ n ≠ 1 → ptVal S y m = 0 := by
  constructor
  · intro h m hm
    have h1 := ptVal_pow y n (m ^ n)
    rw [h, ptVal_one, if_neg hm] at h1
    have h2 := congrArg (ptVal S y m * ·) h1
    simp only [mul_zero, Finset.mul_sum, mul_ite, ptVal_mul_ptVal] at h2
    rw [Finset.sum_eq_single m] at h2
    · simpa using h2.symm
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro h
    refine points_ext' fun m => ?_
    rw [ptVal_pow, ptVal_one]
    by_cases hm : m = 1
    · subst hm
      rw [if_pos rfl, ← sum_ptVal y]
      refine Finset.sum_congr rfl fun m' _ => ?_
      split_ifs with h'
      · rfl
      · exact (h m' h').symm
    · rw [if_neg hm]
      refine Finset.sum_eq_zero fun m' _ => ?_
      split_ifs with h'
      · exact h m' (h' ▸ hm)
      · rfl

theorem ptVal_mapPoints (h : M →* M') (x : (const R M).points S) (m' : M') :
    ptVal S ((constMap R h).mapPoints S x) m' = ∑ m, if h m = m' then ptVal S x m else 0 := by
  change (ofConv x) (constMapAlg R h (eA (R := R) m')) = _
  rw [eq_sum_ptVal]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [constMapAlg_apply]
  change algebraMap R S (e R M' m' (h m)) * _ = _
  rw [e_apply]
  split_ifs <;> simp

/-- A point from a family of orthogonal idempotents summing to `1`. -/
def ofIdem (t : M → S) (horth : ∀ m n, t m * t n = if m = n then t m else 0)
    (hsum : ∑ m, t m = 1) : (const R M).A →ₐ[R] S where
  toFun f := ∑ m, algebraMap R S ((f : M → R) m) * t m
  map_one' := by
    change ∑ m, algebraMap R S 1 * t m = 1
    simp [hsum]
  map_mul' f g := by
    change ∑ m, algebraMap R S ((f : M → R) m * (g : M → R) m) * t m = _
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single m]
    · rw [mul_mul_mul_comm, horth, if_pos rfl, map_mul]
    · intro b _ hb
      rw [mul_mul_mul_comm, horth, if_neg (Ne.symm hb), mul_zero]
    · simp
  map_zero' := by
    change ∑ m, algebraMap R S 0 * t m = 0
    simp
  map_add' f g := by
    change ∑ m, algebraMap R S ((f : M → R) m + (g : M → R) m) * t m = _
    simp [add_mul, Finset.sum_add_distrib]
  commutes' r := by
    change ∑ m, algebraMap R S r * t m = _
    rw [← Finset.mul_sum, hsum, mul_one]

theorem ofIdem_eA (t : M → S) (horth : ∀ m n, t m * t n = if m = n then t m else 0)
    (hsum : ∑ m, t m = 1) (k : M) : ofIdem t horth hsum (eA (R := R) k) = t k := by
  change ∑ m, algebraMap R S (e R M k m) * t m = t k
  simp only [e_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- For injective `h`, a point `y` of `M'_R` comes from `M_R` iff it vanishes on `e_{m'}` for
all `m' ∉ range h`. -/
theorem exists_mapPoints_eq_iff {h : M →* M'} (hinj : Function.Injective h)
    (y : (const R M').points S) :
    (∃ x, (constMap R h).mapPoints S x = y) ↔ ∀ m', m' ∉ Set.range h → ptVal S y m' = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ m' hm'
    rw [ptVal_mapPoints]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg (fun h' => hm' ⟨m, h'⟩)]
  · intro hy
    set t : M → S := fun m => ptVal S y (h m)
    have horth : ∀ m n, t m * t n = if m = n then t m else 0 := by
      intro m n
      simp only [t, ptVal_mul_ptVal, hinj.eq_iff]
    have hsum : ∑ m, t m = 1 := by
      rw [← sum_ptVal y]
      rw [← Finset.sum_image (f := ptVal S y) (fun a _ b _ hab => hinj hab)]
      refine Finset.sum_subset (Finset.subset_univ _) fun m' _ hm' => hy m' ?_
      rintro ⟨m, rfl⟩
      exact hm' (Finset.mem_image_of_mem _ (Finset.mem_univ m))
    refine ⟨toConv (ofIdem t horth hsum), points_ext' fun m' => ?_⟩
    rw [ptVal_mapPoints]
    simp only [ptVal, ofIdem_eA]
    by_cases hm' : m' ∈ Set.range h
    · obtain ⟨m, rfl⟩ := hm'
      rw [Finset.sum_eq_single m]
      · rw [if_pos rfl]; rfl
      · intro b _ hb; rw [if_neg (fun h' => hb (hinj h'))]
      · simp
    · rw [Finset.sum_eq_zero fun m _ => if_neg (fun h' => hm' ⟨m, h'⟩)]
      exact (hy m' hm').symm

end Points

end FFGroupScheme

end PadicHodge
