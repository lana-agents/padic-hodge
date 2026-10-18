/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Formal group laws of dimension `d`

Following [Hong, Def. 2.2.3]: a (commutative) formal group law of dimension `d` over `R` is a
family `Φ(T, U) = (Φ_i(T, U))_{i < d}` of power series in `2d` variables `T = (t_j)`,
`U = (u_j)` such that

* (i) `Φ(T, Φ(U, V)) = Φ(Φ(T, U), V)` (associativity),
* (ii) `Φ(T, 0) = T = Φ(0, T)` (unit section),
* (iii) `Φ(T, U) = Φ(U, T)` (commutativity).

Variables are indexed by `Fin n × Fin d` (copy, coordinate); substitutions use Mathlib's
`MvPowerSeries.subst`. We also record `Φ_i(0, 0) = 0` (in [Hong] it is part of the continuity of
`μ : R[[T]] → R[[T, U]]`; it also follows from (ii)).

* `FGL R d`; the multiplicative law `Ĝ_m` ([Hong, Ex. 2.2.4]) is `FGL.multiplicative`
  (`FormalGroup/Mult.lean`).
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The substitution family `(t_j ↦ f_j, u_j ↦ g_j)` for `Φ(T, U)`. -/
def pairFam {τ : Type*} (f g : Fin d → MvPowerSeries τ R) :
    Fin 2 × Fin d → MvPowerSeries τ R :=
  fun v => if v.1 = 0 then f v.2 else g v.2

omit [CommRing R] in
@[simp] theorem pairFam_zero {τ : Type*} (f g : Fin d → MvPowerSeries τ R) (j : Fin d) :
    pairFam f g (0, j) = f j := rfl

omit [CommRing R] in
@[simp] theorem pairFam_one {τ : Type*} (f g : Fin d → MvPowerSeries τ R) (j : Fin d) :
    pairFam f g (1, j) = g j := rfl

/-- The `j`-th variable of copy `a`. -/
def Xv {n : ℕ} (a : Fin n) (j : Fin d) : MvPowerSeries (Fin n × Fin d) R := X (a, j)

variable (R d) in
/-- **A commutative formal group law of dimension `d` over `R`** ([Hong, Def. 2.2.3]). -/
structure FGL where
  /-- the power series `Φ_i(T, U)` -/
  Φ : Fin d → MvPowerSeries (Fin 2 × Fin d) R
  constantCoeff_Φ : ∀ i, constantCoeff (Φ i) = 0
  /-- (i) `Φ(Φ(T, U), V) = Φ(T, Φ(U, V))` -/
  assoc : ∀ i,
    (Φ i).subst (pairFam (fun j => (Φ j).subst (pairFam (Xv (R := R) (n := 3) 0) (Xv 1)))
      (Xv 2)) =
    (Φ i).subst (pairFam (Xv (R := R) (n := 3) 0)
      (fun j => (Φ j).subst (pairFam (Xv (R := R) (n := 3) 1) (Xv 2))))
  /-- (ii) `Φ(T, 0) = T` -/
  unit_right : ∀ i,
    (Φ i).subst (pairFam (fun j => (X j : MvPowerSeries (Fin d) R)) 0) = X i
  /-- (ii) `Φ(0, T) = T` -/
  unit_left : ∀ i,
    (Φ i).subst (pairFam 0 (fun j => (X j : MvPowerSeries (Fin d) R))) = X i
  /-- (iii) `Φ(U, T) = Φ(T, U)` -/
  comm : ∀ i, (Φ i).subst (pairFam (Xv (R := R) (n := 2) 1) (Xv 0)) = Φ i

end PadicHodge
