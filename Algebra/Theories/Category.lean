/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic
import Algebra.Theories.Semicategory

namespace Algebra
variable {α} {β : α → α → Sort _}

class Category (s : CategorySig β) : Prop extends Semicategory (no_index s.toSemicategorySig) where
  protected dop_left_id {{a b}} (x : β a b) : s.op s.id x = x
  protected dop_right_id {{a b}} (x : β a b) : s.op x s.id = x

protected def Category.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] : Category s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _

namespace Category
variable {s : CategorySig β} [Category s]

instance : DOpLeftId (no_index s.op) (no_index s.id) := ⟨Category.dop_left_id⟩
instance : DOpRightId (no_index s.op) (no_index s.id) := ⟨Category.dop_right_id⟩

instance : Semicategory (no_index s.toSemicategorySig) := Semicategory.infer _

end Category

class CancelCategory (s : CategorySig β) : Prop extends Category (no_index s), CancelSemicategory (no_index s.toSemicategorySig)

protected def CancelCategory.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] [DOpLeftCancel s.op] [DOpRightCancel s.op] : CancelCategory s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _
  dop_left_cancel := dop_left_cancel _
  dop_right_cancel := dop_right_cancel _

namespace CancelCategory
variable {s : CategorySig β} [CancelCategory s]

instance : DOpLeftCancel (no_index s.op) := ⟨CancelCategory.dop_left_cancel⟩
instance : DOpRightCancel (no_index s.op) := ⟨CancelCategory.dop_right_cancel⟩

instance : CancelSemicategory (no_index s.toSemicategorySig) := CancelSemicategory.infer _

end CancelCategory

end Algebra
