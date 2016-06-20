import { connect } from 'react-redux'
import ProofStepSelector from '../../components/BaseCase/ProofStepSelector'
import { PROOF_STEP_TYPE } from '../../constants'
import { setBaseCaseProofStepType, markBaseCaseProofComplete } from '../../actions'

const mapStateToProps = (state) => (
  {
    canMarkComplete: state.baseCaseProof.length > 0
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onAssertClick: () => dispatch(setBaseCaseProofStepType(PROOF_STEP_TYPE.ASSERT)),
    onAssumeClick: () => dispatch(setBaseCaseProofStepType(PROOF_STEP_TYPE.ASSUME)),
    onTakeArbitraryClick: () => dispatch(setBaseCaseProofStepType(PROOF_STEP_TYPE.TAKE_ARBITRARY)),
    onCaseAnalysisClick: () => dispatch(setBaseCaseProofStepType(PROOF_STEP_TYPE.CASE_ANALYSIS)),
    onMarkCompleteClick: () => dispatch(markBaseCaseProofCompleted())
  }
)

const RProofStepSelector = connect(
  mapStateToProps,
  mapDispatchToProps
)(ProofStepSelector)

export default RProofStepSelector

