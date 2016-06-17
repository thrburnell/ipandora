import { connect } from 'react-redux'
import { getValues } from 'redux-form'
import Proof from '../../components/Proof'
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
    complete: false,
    stepType: state.proofStepType,
    lineSelectable
  }
}

const mapDispatchToProps = (dispatch) => (
  {
    onLineSelect: (index) => dispatch(toggleLine(index))
  }
)

const RProof = connect(
  mapStateToProps,
  mapDispatchToProps
)(Proof)

export default RProof

