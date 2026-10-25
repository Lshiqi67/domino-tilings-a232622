module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
核验固定版本中后续路线需要的基础模块和公开接口。
这些 #check 不构成论文任何节点的形式化证明。
-/

#check Fintype.card
#check Fintype.card_congr
#check Equiv
#check MulAction.orbitRel
#check MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
#check Matrix.mul_apply
#check PowerSeries
#check PowerSeries.coeff
#check PowerSeries.constantCoeff
