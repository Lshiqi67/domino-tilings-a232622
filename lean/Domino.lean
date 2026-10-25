module

public import Domino.Environment
public import Domino.Board.Examples
public import Domino.Symmetry.Counting
public import Domino.Transfer.Examples
public import Domino.HalfBoard.Examples
public import Domino.ThreeRows.Boundary
public import Domino.ThreeRows.Recurrence

/-!
半棋盘路线的项目入口。M1–M6 已实现，包括真实轨道的主生成函数、七阶递推及初值。
全文扩展和基本块第二证明尚未实现；逐项范围见 docs/coverage.json。
-/
