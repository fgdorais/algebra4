/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Category

namespace Algebra
variable {α} {β : α → α → Sort _}

class Groupoid (s : GroupoidSig β) : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : s.op (s.op x y) z = s.op x (s.op y z)
  protected dop_right_id {{a b}} (x : β a b) : s.op x s.id = x
  protected dop_right_inv {{a b}} (x : β a b) : s.op x (s.inv x) = s.id

protected def Groupoid.infer (s : GroupoidSig β) [DOpAssoc s.op] [DOpRightId s.op s.id] [DOpRightInv s.op s.inv s.id] : Groupoid s where
  dop_assoc := dop_assoc _
  dop_right_id := dop_right_id _
  dop_right_inv := dop_right_inv _

namespace Groupoid
variable {s : GroupoidSig β} [Groupoid s]

local infixr:60 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

local instance : DOpAssoc (no_index s.op) := ⟨Groupoid.dop_assoc⟩
local instance : DOpRightId (no_index s.op) (no_index s.id) := ⟨Groupoid.dop_right_id⟩
instance : DOpRightInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Groupoid.dop_right_inv⟩

protected theorem dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} (h : s.op y x = s.op z x) : y = z := calc
  _ = y ⋆ e := by rw [dop_right_id s.op]
  _ = y ⋆ (x ⋆ x⁻¹) := by rw [dop_right_inv s.op]
  _ = (y ⋆ x) ⋆ x⁻¹ := by rw [dop_assoc s.op]
  _ = (z ⋆ x) ⋆ x⁻¹ := by rw [h]
  _ = z ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = z ⋆ e := by rw [dop_right_inv s.op]
  _ = z := by rw [dop_right_id s.op]
local instance : DOpRightCancel (no_index s.op) := ⟨Groupoid.dop_right_cancel⟩

protected theorem dop_left_id {{a b}} (x : β a b) : e ⋆ x = x :=
  dop_right_cancel s.op x⁻¹ $ calc
  _ = e ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = e ⋆ e := by rw [dop_right_inv s.op]
  _ = e := by rw [dop_right_id s.op]
  _ = x ⋆ x⁻¹ := by rw [dop_right_inv s.op]
local instance : DOpLeftId (no_index s.op) (no_index s.id) := ⟨Groupoid.dop_left_id⟩

protected theorem dop_left_inv {{a b}} (x : β a b) : x⁻¹ ⋆ x = e :=
  dop_right_cancel s.op x⁻¹ $ calc
  _ = x⁻¹ ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = x⁻¹ ⋆ e := by rw [dop_right_inv s.op]
  _ = x⁻¹ := by rw [dop_right_id s.op]
  _ = e ⋆ x⁻¹ := by rw [dop_left_id s.op]
instance : DOpLeftInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Groupoid.dop_left_inv⟩

protected theorem dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} (h : x ⋆ y = x ⋆ z) : y = z := calc
  _ = e ⋆ y := by rw [dop_left_id s.op]
  _ = (x⁻¹ ⋆ x) ⋆ y := by rw [dop_left_inv s.op]
  _ = x⁻¹ ⋆ (x ⋆ y) := by rw [dop_assoc s.op]
  _ = x⁻¹ ⋆ (x ⋆ z) := by rw [h]
  _ = (x⁻¹ ⋆ x) ⋆ z := by rw [dop_assoc s.op]
  _ = e ⋆ z := by rw [dop_left_inv s.op]
  _ = z := by rw [dop_left_id s.op]
local instance : DOpLeftCancel (no_index s.op) := ⟨Groupoid.dop_left_cancel⟩

protected theorem dinv_op {{a b c}} (x : β a b) (y : β c a) : (x ⋆ y)⁻¹ = y⁻¹ ⋆ x⁻¹ :=
  dop_right_cancel s.op (x ⋆ y) $ calc
  _ = e := by rw [←dop_left_inv s.op (x ⋆ y)]
  _ = y⁻¹ ⋆ y := by rw [dop_left_inv s.op y]
  _ = y⁻¹ ⋆ (e ⋆ y) := by rw [dop_left_id s.op y]
  _ = y⁻¹ ⋆ (x⁻¹ ⋆ x) ⋆ y := by rw [dop_left_inv s.op x]
  _ = y⁻¹ ⋆ x⁻¹ ⋆ (x ⋆ y) := by rw [dop_assoc s.op x⁻¹ x y]
  _ = (y⁻¹ ⋆ x⁻¹) ⋆ (x ⋆ y) := by rw [dop_assoc s.op y⁻¹ x⁻¹ (x ⋆ y)]
instance : DInvOp (no_index s.inv) (no_index s.op) := ⟨Groupoid.dinv_op⟩

protected theorem dinv_invol {{a b}} (x : β a b) : x⁻¹⁻¹ = x :=
  dop_right_cancel s.op x⁻¹ $ calc
  _ = e := by rw [←dop_left_inv s.op x⁻¹]
  _ = x ⋆ x⁻¹ := by rw [dop_right_inv s.op x]
instance : DInvInvol (no_index s.inv) := ⟨Groupoid.dinv_invol⟩

protected theorem dinv_id {{a}} : (e : β a a)⁻¹ = e :=
  dop_right_cancel s.op e $ show e⁻¹ ⋆ e = e ⋆ e from calc
  _ = e := by rw [dop_left_inv s.op e]
  _ = e ⋆ e := by rw [dop_right_id s.op e]
instance : DInvId (no_index s.inv) (no_index s.id) := ⟨Groupoid.dinv_id⟩

instance : CancelCategory (no_index s.toCategorySig) := CancelCategory.infer _

end Groupoid

end Algebra
