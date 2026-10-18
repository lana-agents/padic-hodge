/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.PDeriv
import PadicHodge.FormalGroup.Filtration

/-!
# Invariant derivations; `[p]_F(T) ∈ (T_1^p, …, T_d^p)` in characteristic `p`

For a formal group law `F` of dimension `d` over a commutative ring `k`, the **invariant
derivations** are `D_j g = ∂_{U_j} g(Φ(T, U))|_{U = 0}`. By the chain rule
(`MvPowerSeries.pderiv_subst`) and `Φ(T, 0) = T`,

* `invDeriv_eq`: `D_j g = ∑_l ∂_l g · M_{lj}` with `M_{lj}(T) = ∂_{U_j} Φ_l(T, 0)`, and `M(0) = 1`
  (the linear part of `Φ` is `T + U`), so `M` is invertible (`isUnit_det_invMat`).

For `[n]_F` (`mulPS`): `[n](Φ(T, U)) = Φ([n]T, [n]U)` (`mulPS_subst_addPS`), so
`D_j [n]_l = ∑_m ∂_{U_m} Φ_l([n]T, 0) · ∂_j [n]_m(0)` and `∂_j [n]_m(0) = n δ_{jm}`
([Hong, Lemma 2.2.14], `coeff_single_mulPS`). In characteristic `p` this gives `D_j [p] = 0`,
hence **`∂_j [p]_l = 0`** for all `j`, `l` (`pderiv_mulPS_p`), and therefore every monomial of
`[p]_l` is a `p`-th power, i.e. **`[p]_F(T) ∈ (T_1^p, …, T_d^p)`** (`mulPS_p_mem`). This is the
argument of [Hong, Prop. 1.5.10, proof] (the derivations `D_j` there satisfy `λ ∂/∂t_j = D_j λ`)
transported to formal group laws; it gives `ker(φ : F[p] → F[p]^{(p)}) = Spec k[T]/(T^p)`, of
order `p^d` ([Hong, Cor. 1.5.11, Cor. 2.2.18]; [Tate, §(2.2), p. 165] uses `[p]^* ω = p ω` for
invariant differentials).
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {k : Type*} [CommRing k] {d : ℕ} (F : FGL k d)

/-! ### `[n]_F` is an endomorphism -/

theorem addPS_addPS_comm {τ : Type*} {a b c e : Fin d → MvPowerSeries τ k} (ha : NoConst a)
    (hb : NoConst b) (hc : NoConst c) (he : NoConst e) :
    F.addPS (F.addPS a b) (F.addPS c e) = F.addPS (F.addPS a c) (F.addPS b e) := by
  rw [F.addPS_assoc ha hb (F.noConst_addPS hc he), ← F.addPS_assoc hb hc he,
    F.addPS_comm hb hc, F.addPS_assoc hc hb he, ← F.addPS_assoc ha hc (F.noConst_addPS hb he)]

theorem noConst_subst {σ τ : Type*} [Finite σ] {f : Fin d → MvPowerSeries σ k} (hf : NoConst f)
    {g : σ → MvPowerSeries τ k} (hg : ∀ s, constantCoeff (g s) = 0) :
    NoConst (fun j => (f j).subst g) := fun j =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hg) hg (hf j)

/-- **`[n](Φ(f, g)) = Φ([n] f, [n] g)`.** -/
theorem mulPS_subst_addPS (n : ℕ) {τ : Type*} {f g : Fin d → MvPowerSeries τ k} (hf : NoConst f)
    (hg : NoConst g) (i : Fin d) :
    (F.mulPS n i).subst (F.addPS f g) =
      F.addPS (fun j => (F.mulPS n j).subst f) (fun j => (F.mulPS n j).subst g) i := by
  have hfg := hasSubst_of_noConst (F.noConst_addPS hf hg)
  have hf' := hasSubst_of_noConst hf
  have hg' := hasSubst_of_noConst hg
  induction n generalizing i with
  | zero =>
    simp only [mulPS_zero, Pi.zero_apply]
    rw [subst_zero' hfg]
    have h0 : (fun _ : Fin d => (0 : MvPowerSeries (Fin d) k).subst f) =
        (0 : Fin d → MvPowerSeries τ k) := funext fun _ => subst_zero' hf'
    have h0' : (fun _ : Fin d => (0 : MvPowerSeries (Fin d) k).subst g) =
        (0 : Fin d → MvPowerSeries τ k) := funext fun _ => subst_zero' hg'
    rw [h0, h0', F.addPS_zero noConst_zero]
    rfl
  | succ n ih =>
    have e1 : ∀ (h : Fin d → MvPowerSeries τ k), HasSubst h →
        (fun j => (F.mulPS (n + 1) j).subst h) =
          F.addPS (fun j => (F.mulPS n j).subst h) h := by
      intro h hh
      funext j
      rw [mulPS_succ, F.subst_addPS (F.noConst_mulPS n) noConst_X hh]
      congr 1
      funext l
      exact subst_X hh l
    rw [show (F.mulPS (n + 1) i).subst (F.addPS f g) =
      (fun j => (F.mulPS (n + 1) j).subst (F.addPS f g)) i from rfl, e1 _ hfg, e1 _ hf', e1 _ hg']
    have ih' : (fun j => (F.mulPS n j).subst (F.addPS f g)) =
        F.addPS (fun j => (F.mulPS n j).subst f) (fun j => (F.mulPS n j).subst g) := funext ih
    rw [ih', F.addPS_addPS_comm (noConst_subst (F.noConst_mulPS n) hf)
      (noConst_subst (F.noConst_mulPS n) hg) hf hg]

/-! ### Invariant derivations -/

/-- The substitution `(T, U) ↦ (T, 0)`. -/
abbrev atZero : Fin 2 × Fin d → MvPowerSeries (Fin d) k := pairFam (fun j => X j) 0

theorem noConst_atZero : ∀ v, constantCoeff (atZero (k := k) (d := d) v) = 0 :=
  noConst_pairFam (fun j => constantCoeff_X j) fun _ => map_zero _

/-- The matrix `M_{lj}(T) = ∂Φ_l/∂U_j (T, 0)`. -/
def invMat : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) k) :=
  fun l j => (pderiv k (1, j) (F.Φ l)).subst atZero

theorem constantCoeff_invMat (l j : Fin d) :
    constantCoeff (F.invMat l j) = if l = j then 1 else 0 := by
  rw [invMat, constantCoeff_subst_of_constantCoeff_zero noConst_atZero, constantCoeff_pderiv,
    coeff_single_Φ]

/-- **`M` is invertible**: `M(0) = 1`. -/
theorem isUnit_det_invMat : IsUnit F.invMat.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff : MvPowerSeries (Fin d) k →+* k).mapMatrix F.invMat = 1 := by
    ext l j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_invMat, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

theorem subst_atZero_Φ (g : MvPowerSeries (Fin d) k) :
    (g.subst F.Φ).subst (atZero (k := k) (d := d)) = g := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero F.constantCoeff_Φ)
    (hasSubst_of_constantCoeff_zero noConst_atZero)]
  have : (fun l => (F.Φ l).subst (atZero (k := k) (d := d))) = fun l => X l :=
    funext F.unit_right
  rw [this, subst_self]
  rfl

/-- **Invariant derivations**: `∂_{U_j} g(Φ(T, U))|_{U=0} = ∑_l ∂_l g · M_{lj}`. -/
theorem invDeriv_eq (g : MvPowerSeries (Fin d) k) (j : Fin d) :
    (pderiv k (1, j) (g.subst F.Φ)).subst (atZero (k := k) (d := d)) =
      ∑ l, pderiv k l g * F.invMat l j := by
  have h0 := hasSubst_of_constantCoeff_zero (noConst_atZero (k := k) (d := d))
  rw [pderiv_subst F.constantCoeff_Φ, ← coe_substAlgHom h0, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, coe_substAlgHom, F.subst_atZero_Φ]
  rfl

/-- `∂_{U_j}` of a family in the `T`-variables vanishes. -/
theorem pderiv_one_subst_Xv0 (f : MvPowerSeries (Fin d) k) (j : Fin d) :
    pderiv k ((1 : Fin 2), j) (f.subst (Xv (R := k) (n := 2) 0)) = 0 := by
  rw [pderiv_subst (noConst_Xv 0)]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Xv, pderiv_X_of_ne (by simp), mul_zero]

theorem pderiv_one_subst_Xv1 (f : MvPowerSeries (Fin d) k) (j : Fin d) :
    pderiv k ((1 : Fin 2), j) (f.subst (Xv (R := k) (n := 2) 1)) =
      (pderiv k j f).subst (Xv (R := k) (n := 2) 1) := by
  classical
  rw [pderiv_subst (noConst_Xv 1)]
  simp only [Xv, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Φ_eq_addPS : (F.Φ : Fin d → MvPowerSeries (Fin 2 × Fin d) k) =
    F.addPS (Xv (R := k) (n := 2) 0) (Xv 1) := by
  funext i
  rw [addPS]
  have : pairFam (Xv (R := k) (d := d) (n := 2) 0) (Xv 1) = X := by
    funext v
    obtain ⟨a, l⟩ := v
    fin_cases a <;> rfl
  rw [this, subst_self]
  rfl

/-- `D_j [n]_l = ∑_m ∂_{U_m} Φ_l([n]T, 0) · n δ_{jm}`; we only record that it is a multiple of
`n`: it vanishes whenever `n = 0` in `k`. -/
theorem invDeriv_mulPS_eq_zero (n : ℕ) (hn : (n : k) = 0) (l j : Fin d) :
    (pderiv k (1, j) ((F.mulPS n l).subst F.Φ)).subst (atZero (k := k) (d := d)) = 0 := by
  have h0 := hasSubst_of_constantCoeff_zero (noConst_atZero (k := k) (d := d))
  rw [F.Φ_eq_addPS, F.mulPS_subst_addPS n (noConst_Xv 0) (noConst_Xv 1), addPS,
    pderiv_subst (noConst_pairFam (noConst_subst (F.noConst_mulPS n) (noConst_Xv 0))
      (noConst_subst (F.noConst_mulPS n) (noConst_Xv 1))), ← coe_substAlgHom h0, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  obtain ⟨a, m⟩ := s
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, pairFam_zero]
    rw [pderiv_one_subst_Xv0, mul_zero, map_zero]
  · simp only [Fin.mk_one, Fin.isValue, pairFam_one]
    rw [pderiv_one_subst_Xv1, map_mul, coe_substAlgHom h0,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (noConst_Xv 1)) h0]
    have hz : (fun s => (Xv (R := k) (d := d) (n := 2) 1 s).subst (atZero (k := k) (d := d))) =
        0 := by
      funext s
      rw [Xv, subst_X h0]
      rfl
    rw [hz]
    have hc : (pderiv k j (F.mulPS n m)).subst (0 : Fin d → MvPowerSeries (Fin d) k) = 0 := by
      rw [subst_zero_eq_C, constantCoeff_pderiv, coeff_single_mulPS]
      split_ifs <;> simp [hn]
    rw [hc, mul_zero]

/-- **`∂_m [n]_l = 0` if `n = 0` in `k`** (the invariant derivations kill `[n]`, and `M` is
invertible). -/
theorem pderiv_mulPS_eq_zero (n : ℕ) (hn : (n : k) = 0) (l m : Fin d) :
    pderiv k m (F.mulPS n l) = 0 := by
  have hM : IsUnit F.invMat := (Matrix.isUnit_iff_isUnit_det _).mpr F.isUnit_det_invMat
  have h : Matrix.vecMul (fun m => pderiv k m (F.mulPS n l)) F.invMat =
      Matrix.vecMul 0 F.invMat := by
    funext j
    rw [Matrix.zero_vecMul, Pi.zero_apply]
    change ∑ m, pderiv k m (F.mulPS n l) * F.invMat m j = 0
    rw [← F.invDeriv_eq, F.invDeriv_mulPS_eq_zero n hn]
  exact congrFun (Matrix.vecMul_injective_of_isUnit hM h) m

end FGL

end PadicHodge

/-! ### Power series all of whose monomials are divisible by some `X_j^N` -/

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [Finite σ] [LinearOrder σ]

/-- If every monomial of `f` is divisible by some `X_j^N`, then `f ∈ (X_j^N)_j`. -/
theorem mem_span_X_pow (N : ℕ) (f : MvPowerSeries σ R)
    (h : ∀ a, coeff a f ≠ 0 → ∃ j, N ≤ a j) :
    f ∈ Ideal.span (Set.range fun j => (X j : MvPowerSeries σ R) ^ N) := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  let S : (σ →₀ ℕ) → Finset σ := fun a => Finset.univ.filter fun j => N ≤ a j
  let ch : (σ →₀ ℕ) → Option σ := fun a =>
    if hS : (S a).Nonempty then some ((S a).min' hS) else none
  let g : σ → MvPowerSeries σ R := fun j b =>
    if ch (b + Finsupp.single j N) = some j then coeff (b + Finsupp.single j N) f else 0
  have hg : ∀ j b, coeff b (g j) =
      if ch (b + Finsupp.single j N) = some j then coeff (b + Finsupp.single j N) f else 0 :=
    fun _ _ => rfl
  have key : f = ∑ j, X j ^ N * g j := by
    ext a
    rw [map_sum]
    have hterm : ∀ j, coeff a (X j ^ N * g j) =
        if ch a = some j then coeff a f else 0 := by
      intro j
      rw [X_pow_eq, coeff_monomial_mul, one_mul]
      split_ifs with h1 h2 h2
      · rw [hg, tsub_add_cancel_of_le h1, if_pos h2]
      · rw [hg, tsub_add_cancel_of_le h1, if_neg h2]
      · exfalso
        apply h1
        have hS : (S a).Nonempty := by
          by_contra hne
          simp only [ch, dif_neg hne] at h2
          simp at h2
        simp only [ch, dif_pos hS, Option.some.injEq] at h2
        have := (S a).min'_mem hS
        rw [h2] at this
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact Finsupp.single_le_iff.mpr this
      · rfl
    simp only [hterm]
    by_cases hS : (S a).Nonempty
    · have hch : ch a = some ((S a).min' hS) := by simp only [ch, dif_pos hS]
      rw [Finset.sum_eq_single ((S a).min' hS)]
      · rw [if_pos hch]
      · intro j _ hj
        rw [if_neg]
        rw [hch]
        exact fun h' => hj (Option.some.inj h').symm
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · have hch : ch a = none := by simp only [ch, dif_neg hS]
      simp only [hch, reduceCtorEq, if_false, Finset.sum_const_zero]
      by_contra hne
      obtain ⟨j, hj⟩ := h a hne
      exact hS ⟨j, by simp [S, hj]⟩
  rw [key]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

end MvPowerSeries

namespace PadicHodge

namespace FGL

variable {k : Type*} [CommRing k] {d : ℕ} (F : FGL k d)

/-- In characteristic `p`, a power series without constant term all of whose partial derivatives
vanish lies in `(X_j^p)_j`. -/
theorem mem_span_X_pow_of_pderiv (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (f : MvPowerSeries (Fin d) k) (h0 : constantCoeff f = 0) (h : ∀ m, pderiv k m f = 0) :
    f ∈ Ideal.span (Set.range fun j => (X j : MvPowerSeries (Fin d) k) ^ p) := by
  -- every exponent of a monomial of `f` is divisible by `p`
  have hdiv : ∀ a, coeff a f ≠ 0 → ∀ j, p ∣ a j := by
    intro a ha j
    by_contra hpj
    have hpos : 0 < a j := Nat.pos_of_ne_zero fun h' => hpj (h' ▸ dvd_zero p)
    have hle : Finsupp.single j 1 ≤ a := Finsupp.single_le_iff.mpr hpos
    have hc := congrArg (coeff (a - Finsupp.single j 1)) (h j)
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, map_zero] at hc
    have e : (((a - Finsupp.single j 1 : Fin d →₀ ℕ) j : ℕ) : k) + 1 = ((a j : ℕ) : k) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_succ, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    rw [e] at hc
    have hu : IsUnit ((a j : ℕ) : k) := by
      have hcop : Nat.Coprime (a j) p :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpj)
      have hb := Nat.gcd_eq_gcd_ab (a j) p
      rw [hcop.gcd_eq_one, Nat.cast_one] at hb
      have h1 := congrArg (Int.cast : ℤ → k) hb
      rw [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
        Int.cast_natCast, CharP.cast_eq_zero k p, zero_mul, add_zero] at h1
      exact IsUnit.of_mul_eq_one _ h1.symm
    exact ha ((hu.mul_left_eq_zero).mp hc)
  refine MvPowerSeries.mem_span_X_pow p f fun a ha => ?_
  have hne : a ≠ 0 := by
    rintro rfl
    exact ha (by rw [coeff_zero_eq_constantCoeff_apply, h0])
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Finsupp.ext hall)
  exact ⟨j, Nat.le_of_dvd (Nat.pos_of_ne_zero hj) (hdiv a ha j)⟩

/-- **`[p]_F(T) ∈ (T_1^p, …, T_d^p)` in characteristic `p`** ([Hong, Prop. 1.5.10, proof],
for formal group laws). -/
theorem mulPS_p_mem (p : ℕ) [Fact p.Prime] [CharP k p] (l : Fin d) :
    F.mulPS p l ∈ Ideal.span (Set.range fun j => (X j : MvPowerSeries (Fin d) k) ^ p) :=
  mem_span_X_pow_of_pderiv p _ (F.constantCoeff_mulPS p l)
    (F.pderiv_mulPS_eq_zero p (CharP.cast_eq_zero k p) l)

end FGL

end PadicHodge
