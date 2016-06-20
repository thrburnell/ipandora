import { connect } from 'react-redux'
import { getValues } from 'redux-form'
import BaseCase from '../../components/BaseCase'
import { toggleLine } from '../../actions'
import { ASSERT_JUSTIFICATION_TYPE } from '../../constants'

const mapStateToProps = (state) => {

  const form = getValues(state.form.addBaseCaseProofLine)
  const lineSelectable = 
    state.baseCaseProofStepType == "ASSERT" &&
    form &&
    (form.justification == ASSERT_JUSTIFICATION_TYPE.IMPLICATION ||
     form.justification == ASSERT_JUSTIFICATION_TYPE.ASSUMPTION_CLOSURE)

  return {
    lines: state.baseCaseProof,
    complete: state.baseCaseProofComplete,
    stepType: state.baseCaseProofStepType,
    lineSelectable,
    toShow: state.baseCase.toShow[0]
  }
}

const mapDispatchToProps = (dispatch) => (
  {
    onLineSelect: (index) => dispatch(toggleLine(index))
  }
)

const RBaseCase = connect(
  mapStateToProps,
  mapDispatchToProps
)(BaseCase)

export default RBaseCase

