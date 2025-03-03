/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Algebra.Theories.Basic

namespace Algebra
variable {α} {β : α → α → Sort _}

class Semicategory (s : SemicategorySig β) : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : s.op (s.op x y) z = s.op x (s.op y z)

protected def Semicategory.infer (s : SemicategorySig β) [DOpAssoc s.op] : Semicategory s where
  dop_assoc := dop_assoc _

namespace Semicategory
variable {s : SemicategorySig β} [Semicategory s]

instance : DOpAssoc (no_index s.op) := ⟨Semicategory.dop_assoc⟩

end Semicategory

class CancelSemicategory (s : SemicategorySig β) : Prop extends Semicategory (no_index s) where
  protected dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} : s.op x y = s.op x z → y = z
  protected dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} : s.op y x = s.op z x → y = z

protected def CancelSemicategory.infer (s : SemicategorySig β) [DOpAssoc s.op] [DOpLeftCancel s.op] [DOpRightCancel s.op] : CancelSemicategory s where
  dop_assoc := dop_assoc _
  dop_left_cancel := dop_left_cancel _
  dop_right_cancel := dop_right_cancel _

namespace CancelSemicategory
variable {s : SemicategorySig β} [CancelSemicategory s]

instance : DOpLeftCancel (no_index s.op) := ⟨CancelSemicategory.dop_left_cancel⟩
instance : DOpRightCancel (no_index s.op) := ⟨CancelSemicategory.dop_right_cancel⟩

end CancelSemicategory

end Algebra
