import { connect } from 'react-redux'
import ProofStepSelector from '../../components/Proof/ProofStepSelector'
import { PROOF_STEP_TYPE } from '../../constants'
import { setProofStepType } from '../../actions'

const mapStateToProps = (state) => (
  {

  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onAssertClick: () => dispatch(setProofStepType(PROOF_STEP_TYPE.ASSERT)),
    onAssumeClick: () => dispatch(setProofStepType(PROOF_STEP_TYPE.ASSUME)),
    onTakeArbitraryClick: () => dispatch(setProofStepType(PROOF_STEP_TYPE.TAKE_ARBITRARY)),
    onCaseAnalysisClick: () => dispatch(setProofStepType(PROOF_STEP_TYPE.CASE_ANALYSIS)),
  }
)

const RProofStepSelector = connect(
  mapStateToProps,
  mapDispatchToProps
)(ProofStepSelector)

export default RProofStepSelector

