import { connect } from 'react-redux'
import { getValues } from 'redux-form'
import InductiveCase from '../../components/InductiveCase'
import { toggleLine } from '../../actions'
import { ASSERT_JUSTIFICATION_TYPE } from '../../constants'

const mapStateToProps = (state) => {

  const form = getValues(state.form.addProofLine)
  const lineSelectable = 
    state.proofStepType == "ASSERT" &&
    form &&
    (form.justification == ASSERT_JUSTIFICATION_TYPE.IMPLICATION ||
     form.justification == ASSERT_JUSTIFICATION_TYPE.ASSUMPTION_CLOSURE)

  return {
    lines: state.proof.filter(node => node.type != "GIVEN"),
    complete: state.proofComplete,
    stepType: state.proofStepType,
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

