/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Semigroup
import Algebra.Theories.Category

namespace Algebra
variable {α} (s : MonoidSig α)

local infixr:70 " ⋆ " => s.op
local notation "e" => s.id

class Monoid extends Semigroup (no_index s.toSemigroupSig) : Prop where
  protected op_left_id (x) : e ⋆ x = x
  protected op_right_id (x) : x ⋆ e = x

protected def Monoid.infer [OpAssoc s.op] [OpLeftId s.op s.id] [OpRightId s.op s.id] : Monoid s where
  op_assoc := op_assoc _
  op_left_id := op_left_id _
  op_right_id := op_right_id _

namespace Monoid
variable {s} [self : Monoid s]

instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨Monoid.op_left_id⟩
instance : OpRightId (no_index s.op) (no_index s.id) := ⟨Monoid.op_right_id⟩

instance : Category (no_index s.toCategorySig) where
  toSemicategory := Semicategory.infer _
  dop_left_id _ _ := op_left_id s.op
  dop_right_id _ _ := op_right_id s.op

end Monoid

class CommMonoid extends CommSemigroup (no_index s.toSemigroupSig) : Prop where
  protected op_right_id (x) : x ⋆ e = x

protected def CommMonoid.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] : CommMonoid s where
  op_assoc := op_assoc _
  op_comm := op_comm _
  op_right_id := op_right_id _

namespace CommMonoid
variable {s} [self : CommMonoid s]

local instance : OpRightId (no_index s.op) (no_index s.id) := ⟨CommMonoid.op_right_id⟩

protected theorem op_left_id (x) : e ⋆ x = x := calc
  _ = x ⋆ e := by rw [op_comm (.⋆.)]
  _ = x := by rw [op_right_id (.⋆.)]
local instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨CommMonoid.op_left_id⟩

instance : Monoid s := Monoid.infer s

end CommMonoid

class CancelMonoid extends Monoid s, CancelSemigroup (no_index s.toSemigroupSig) : Prop

protected def CancelMonoid.infer [OpAssoc s.op] [OpLeftId s.op s.id] [OpRightId s.op s.id] [OpLeftCancel s.op] [OpRightCancel s.op] : CancelMonoid s where
  op_assoc := op_assoc _
  op_left_id := op_left_id _
  op_right_id := op_right_id _
  op_left_cancel := op_left_cancel _
  op_right_cancel := op_right_cancel _

namespace CancelMonoid
variable {s} [self : CancelMonoid s]

instance : CancelCategory (no_index s.toCategorySig) where
  toCategory := Category.infer _
  dop_left_cancel _ _ _ := op_left_cancel s.op
  dop_right_cancel _ _ _ := op_right_cancel s.op

end CancelMonoid

class CancelCommMonoid extends CommMonoid s, CancelCommSemigroup (no_index s.toSemigroupSig) : Prop

protected def CancelCommMonoid.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] [OpRightCancel s.op] : CancelCommMonoid s where
  op_assoc := op_assoc _
  op_comm := op_comm _
  op_right_id := op_right_id _
  op_right_cancel := op_right_cancel _

end Algebra
