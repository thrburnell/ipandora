import { connect } from 'react-redux'
import ProofStepSelector from '../../components/InductiveCase/ProofStepSelector'
import { PROOF_STEP_TYPE } from '../../constants'
import { setInductiveCaseProofStepType, markInductiveCaseProofComplete } from '../../actions'

const mapStateToProps = (state) => (
  {
    canMarkComplete: state.inductiveCaseProof.length > 1
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onEqualityClick: () => dispatch(setInductiveCaseProofStepType(PROOF_STEP_TYPE.EQUALITY)),
    onMarkCompleteClick: () => dispatch(markInductiveCaseProofCompleted())
  }
)

const RProofStepSelector = connect(
  mapStateToProps,
  mapDispatchToProps
)(ProofStepSelector)

export default RProofStepSelector

