import { connect } from 'react-redux'
import ProofStepSelector from '../../components/InductiveCase/ProofStepSelector'
import { PROOF_STEP_TYPE } from '../../constants'
import { setInductiveCaseProofStepType, markInductiveCaseProofComplete } from '../../actions'

const mapStateToProps = (state) => (
  {
    canMarkComplete: state.inductiveCaseProof.length > 0
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onAssertClick: () => dispatch(setInductiveCaseProofStepType(PROOF_STEP_TYPE.ASSERT)),
    onAssumeClick: () => dispatch(setInductiveCaseProofStepType(PROOF_STEP_TYPE.ASSUME)),
    onTakeArbitraryClick: () => dispatch(setInductiveCaseProofStepType(PROOF_STEP_TYPE.TAKE_ARBITRARY)),
    onCaseAnalysisClick: () => dispatch(setInductiveCaseProofStepType(PROOF_STEP_TYPE.CASE_ANALYSIS)),
    onMarkCompleteClick: () => dispatch(markInductiveCaseProofCompleted())
  }
)

const RProofStepSelector = connect(
  mapStateToProps,
  mapDispatchToProps
)(ProofStepSelector)

export default RProofStepSelector

