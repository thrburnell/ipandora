import { connect } from 'react-redux'
import { checkProofStep } from '../actions'
import AddProofStep from '../components/AddProofStep'

const mapStateToProps = (state) => (
  {
    justification:
      state.proofStepJustification.map(id => ({
        id,
        uiId: state.knownFormulas[id].uiId
      }))
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onCheckButtonClick: (formula, justification) => dispatch(checkProofStep(formula, justification))
  }
)

const RAddProofStep = connect(
  mapStateToProps,
  mapDispatchToProps
)(AddProofStep)

export default RAddProofStep

