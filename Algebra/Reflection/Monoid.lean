/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Instances
import Algebra.Theories.Monoid
import Algebra.Reflection.Semigroup

open List
open Logic

namespace Algebra.Monoid

inductive Expr {α} (xs : List α)
| ofSemigroup : Semigroup.Expr xs → Expr xs
| id : Expr xs

namespace Expr
variable {α} {xs : List α}

instance instDecidableEq : DecidableEq (Expr xs)
| ofSemigroup a, ofSemigroup b =>
  match inferDecidable (a = b) with
  | isTrue rfl => isTrue rfl
  | isFalse h => isFalse fun | rfl => h rfl
| ofSemigroup _, id => Decidable.isFalse Expr.noConfusion
| id, ofSemigroup _ => Decidable.isFalse Expr.noConfusion
| id, id => Decidable.isTrue rfl

def lift (x : α) {xs : List α} : Expr xs → Expr (x :: xs)
| ofSemigroup e => ofSemigroup (e.lift x)
| id => id

def op : Expr xs → Expr xs → Expr xs
| ofSemigroup a, ofSemigroup b => ofSemigroup (Semigroup.Expr.op a b)
| id, b => b
| a, id => a

section Eval
variable (s : MonoidSig α)

def eval {xs : List α} : Expr xs → α
| ofSemigroup e => e.eval s.toSemigroupSig
| id => s.id

@[simp] theorem eval_lift (x) {xs} : ∀ (a : Expr xs), (Expr.lift x a).eval s = a.eval s
| ofSemigroup _ => Semigroup.Expr.eval_lift _ _ _
| id => rfl

@[simp] theorem eval_ofSemigroup {xs} (a : Semigroup.Expr xs) : (ofSemigroup a).eval s = a.eval s.toSemigroupSig := rfl

@[simp] theorem eval_id {xs} : (Expr.id : Expr xs).eval s = s.id := rfl

@[simp] theorem eval_op [Monoid s] {xs} : ∀ (a b : Expr xs), (Expr.op a b).eval s = s.op (a.eval s) (b.eval s)
| ofSemigroup a, ofSemigroup b => by simp [eval, op]
| id, ofSemigroup b => by simp [eval, op, Algebra.op_left_id s.op]
| ofSemigroup a, id => by simp [eval, op, Algebra.op_right_id s.op]
| id, id => by simp [eval, op, Algebra.op_right_id s.op s.id]

end Eval

section Completeness
variable (xs : List α)

def sig : MonoidSig (Expr xs) where
  op := Expr.op
  id := Expr.id

protected theorem op_assoc : ∀ (x y z : Expr xs), op (op x y) z = op x (op y z)
| id, id, id => rfl
| id, id, ofSemigroup _ => rfl
| id, ofSemigroup _, id => rfl
| id, ofSemigroup _, ofSemigroup _ => rfl
| ofSemigroup _, id, id => rfl
| ofSemigroup _, id, ofSemigroup _ => rfl
| ofSemigroup _, ofSemigroup _, id => rfl
| ofSemigroup x, ofSemigroup y, ofSemigroup z => by simp only [op, Semigroup.Expr.op_assoc xs x y z]

instance : Monoid (Expr.sig xs) where
  op_assoc := Expr.op_assoc xs
  op_right_id (x) := match x with
  | Expr.ofSemigroup _ => rfl
  | Expr.id => rfl
  op_left_id (x) := match x with
  | Expr.ofSemigroup _ => rfl
  | Expr.id => rfl

end Completeness

end Expr

class Reflect (s : MonoidSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

protected def Reflect.eq {α} (s : MonoidSig α) (x xs) [inst : Reflect s x xs] : inst.expr.eval s = x := inst.eval_eq

namespace Reflect
variable {α} (s : MonoidSig α) [Monoid s]

class Var (x : α) (xs : List α) extends Reflect s x xs

instance (priority:=low) instVarLift (x y : α) (xs : List α) [Var s y xs] : Var s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

instance instVarSelf (x : α) (xs : List α) : Var s x (x :: xs) where
  expr := Expr.ofSemigroup (Semigroup.Expr.var Index.head)
  eval_eq := by simp

instance instId {xs : List α} : Reflect s (no_index s.id) xs where
  expr := Expr.id
  eval_eq := by simp

instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index (s.op x y)) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

end Reflect

theorem reflect {α} (s : MonoidSig α) [Monoid s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b → a = b := by
  intro h
  rw [←Reflect.eq s a xs, ←Reflect.eq s b xs, h]

end Algebra.Monoid

section Example
open Algebra Notation
variable {α : Type _} (s : MonoidSig α) [Monoid s] (a b c d : α)

local infix:70 " ⋆ " => s.op
local notation "e" => s.id

example : (a ⋆ b) ⋆ (c ⋆ (e ⋆ d)) = (a ⋆ e) ⋆ ((b ⋆ c) ⋆ d) :=
  Monoid.reflect s [a,b,c,d] rfl

example (x y z : Nat) : x + (y + z) + 1 = (x + (0 + y)) + z + 1 :=
  Monoid.reflect Nat.sig.toAddMonoidSig [1,x,y,z] rfl

end Example
