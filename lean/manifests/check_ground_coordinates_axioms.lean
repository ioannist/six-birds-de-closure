import SbtCosmo.Derivation.GroundMatrixCoordinates
import SbtCosmo.Derivation.GroundCoordinates.Point000
import SbtCosmo.Derivation.GroundCoordinates.Point001
import SbtCosmo.Derivation.GroundCoordinates.Point002
import SbtCosmo.Derivation.GroundCoordinates.Point003
import SbtCosmo.Derivation.GroundCoordinates.Point004
import SbtCosmo.Derivation.GroundCoordinates.Point005
import SbtCosmo.Derivation.GroundCoordinates.Point006
import SbtCosmo.Derivation.GroundCoordinates.Point007
import SbtCosmo.Derivation.GroundCoordinates.Point008
import SbtCosmo.Derivation.GroundCoordinates.Point009
import SbtCosmo.Derivation.GroundCoordinates.Point010
import SbtCosmo.Derivation.GroundCoordinates.Point011
import SbtCosmo.Derivation.GroundOriginalCoordinates
import SbtCosmo.Derivation.GroundCoordinateControls

#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.realMatrix_mul
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.realMatrix_one
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.basis_apply
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.basis_symm_apply
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.conjugate_entries
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.transformExpr_return
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.transformed_sound
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.conjugate_rows
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.conjugate_norm
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.imaginaryExpr_return
#print axioms SbtCosmo.Derivation.GroundMatrixCoordinates.imaginaryIntervals_sound
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point000.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point001.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point002.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point003.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point004.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point005.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point006.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point007.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point008.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point009.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point010.imag_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.real_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.imag_inverse
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.realBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.imagBox_return
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.real_rows
#print axioms SbtCosmo.Derivation.GroundCoordinates.Point011.imag_rows
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_real_rows
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_real_norm
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_imag_rows
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_imag_norm
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_full_norm
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.stable_rates
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_stable_full_norm
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_native_attraction
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_twenty_norm
#print axioms SbtCosmo.Derivation.GroundOriginalCoordinates.actual_thirty_norm
#print axioms SbtCosmo.Derivation.GroundCoordinateControls.zero_inverse_rejected
#print axioms SbtCosmo.Derivation.GroundCoordinateControls.zero_row_budget_rejected
