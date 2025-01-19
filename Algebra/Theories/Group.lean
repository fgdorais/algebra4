/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Monoid
import Algebra.Theories.Groupoid

namespace Algebra
variable {α} (s : GroupSig α)

local infixr:70 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

class Group extends Semigroup (no_index s.toSemigroupSig) : Prop where
  protected op_right_id (x) : x ⋆ e = x
  protected op_right_inv (x) : x ⋆ x⁻¹ = e

protected def Group.infer [OpAssoc s.op] [OpRightInv s.op s.inv s.id] [OpRightId s.op s.id] : Group s where
  op_assoc := op_assoc _
  op_right_id := op_right_id _
  op_right_inv := op_right_inv _

namespace Group
variable {s} [self : Group s]

local instance : OpRightId (no_index s.op) (no_index s.id) := ⟨Group.op_right_id⟩
instance : OpRightInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Group.op_right_inv⟩

instance : Groupoid (no_index s.toGroupoidSig) where
  dop_assoc _ _ _ _ := op_assoc s.op
  dop_right_id _ _ := op_right_id s.op
  dop_right_inv _ _ := op_right_inv s.op

local instance : OpRightCancel (no_index s.op) := ⟨dop_right_cancel s.toGroupoidSig.op (a:=()) (b:=()) (c:=())⟩

local instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨dop_left_id s.toGroupoidSig.op (a:=()) (b:=())⟩

instance : OpLeftInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨dop_left_inv s.toGroupoidSig.op (a:=()) (b:=())⟩

local instance : OpLeftCancel (no_index s.op) := ⟨dop_left_cancel s.toCategorySig.op (a:=()) (b:=()) (c:=())⟩

instance : InvOp (no_index s.inv) (no_index s.op) := ⟨dinv_op s.toGroupoidSig.inv (a:=()) (b:=()) (c:=())⟩

instance : InvInvol (no_index s.inv) := ⟨dinv_invol s.toGroupoidSig.inv (a:=()) (b:=())⟩

instance : InvId (no_index s.inv) (no_index s.id) := ⟨dinv_id s.toGroupoidSig.inv (a:=())⟩

instance toCancelMonoid : CancelMonoid (no_index s.toMonoidSig) := CancelMonoid.infer _

end Group

class CommGroup extends Group s, CommMonoid (no_index s.toMonoidSig) : Prop where

protected def CommGroup.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] [OpRightInv s.op s.inv s.id] : CommGroup s where
  op_assoc := op_assoc _
  op_comm := op_comm _
  op_right_id := op_right_id _
  op_right_inv := op_right_inv _

namespace CommGroup
variable {s} [self : CommGroup s]

protected theorem inv_hom (x y) : (x ⋆ y)⁻¹ = x⁻¹ ⋆ y⁻¹ := calc
  _ = y⁻¹ ⋆ x⁻¹ := by rw [inv_op s.inv x y]
  _ = x⁻¹ ⋆ y⁻¹ := by rw [op_comm (.⋆.) x⁻¹ y⁻¹]
instance : InvHom (no_index s.inv) (no_index s.op) := ⟨CommGroup.inv_hom⟩

instance toCancelCommMonoid : CancelCommMonoid (no_index s.toMonoidSig) := CancelCommMonoid.infer _

end CommGroup

end Algebra
