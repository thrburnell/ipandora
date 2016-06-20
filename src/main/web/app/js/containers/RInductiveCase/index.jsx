import { connect } from 'react-redux'
import { getValues } from 'redux-form'
import InductiveCase from '../../components/InductiveCase'
import { toggleLine } from '../../actions'
import { ASSERT_JUSTIFICATION_TYPE } from '../../constants'

const mapStateToProps = (state) => {

  const form = getValues(state.form.addInductiveCaseProofLine)
  const lineSelectable = 
    state.inductiveCaseProofStepType == "ASSERT" &&
    form &&
    (form.justification == ASSERT_JUSTIFICATION_TYPE.IMPLICATION ||
     form.justification == ASSERT_JUSTIFICATION_TYPE.ASSUMPTION_CLOSURE)

  return {
    lines: state.inductiveCaseProof,
    complete: state.inductiveCaseProofComplete,
    stepType: state.inductiveCaseProofStepType,
    lineSelectable,
    ...state.inductiveCase
  }
}

const mapDispatchToProps = (dispatch) => (
  {
    onLineSelect: (index) => dispatch(toggleLine(index))
  }
)

const RInductiveCase = connect(
  mapStateToProps,
  mapDispatchToProps
)(InductiveCase)

export default RInductiveCase

