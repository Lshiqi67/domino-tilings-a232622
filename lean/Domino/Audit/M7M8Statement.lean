module

import Domino

/-! 输出最终定义及定理类型，供语义审阅；不增加假设。 -/

#print Domino.symmetryKind
#print Domino.symmetryOrbitCount
#check Domino.three_row_stabilizer_counting
#check Domino.symmetryTilingCount_formulas
#check Domino.symmetryOrbitCount_formulas
#check Domino.symmetry_type_divisibility
#check Domino.symmetry_orbit_zero
#check Domino.symmetry_orbit_eight
#print Domino.General.Legal
#print Domino.General.evenRunScan
#check Domino.General.legal_iff_even_run_scan
#check Domino.General.row_cover_unique
#check Domino.General.partialTilingEquivPath
#check Domino.General.profile_count_matrix
#check Domino.General.reflectionFixedEquivPartial
#check Domino.General.halfTurnFixedEquivPartial
#check Domino.General.halfTurn_extension_iff
#check Domino.General.horizontalFixedEquivTop
#check Domino.General.horizontal_restrict_top_bonds
#check Domino.General.odd_height_four_counts
#print Domino.General.matrixPencil
#check Domino.General.matrix_geometric_left
#check Domino.General.matrix_geometric_right
#check Domino.General.matrix_geometric_constant
#check Domino.General.matrix_geometric_unique
#check Domino.General.matrix_denominator_constant
#check Domino.General.matrix_entry_denominator
#print Domino.General.orbitSeries
#print Domino.General.RationalSeries
#check Domino.General.orbit_matrix_series
#check Domino.General.odd_height_rational_witness
#check Domino.General.odd_height_eventual_recurrence
#check Domino.General.zero_height_transfer
#check Domino.General.orbit_one_row
#check Domino.General.odd_height_empty
#check Domino.General.odd_height_main
