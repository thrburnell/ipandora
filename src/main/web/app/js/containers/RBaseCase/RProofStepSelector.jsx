import { connect } from 'react-redux'
import ProofStepSelector from '../../components/BaseCase/ProofStepSelector'
import { PROOF_STEP_TYPE } from '../../constants'
import { setBaseCaseProofStepType, markBaseCaseProofComplete } from '../../actions'

const mapStateToProps = (state) => (
  {
    canMarkComplete: state.baseCaseProof.length > 1,
    markCompleteError: state.baseCaseProofCompleteError
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onEqualityClick: () => dispatch(setBaseCaseProofStepType(PROOF_STEP_TYPE.EQUALITY)),
    onMarkCompleteClick: () => dispatch(markBaseCaseProofComplete())
  }
)

const RProofStepSelector = connect(
  mapStateToProps,
  mapDispatchToProps
)(ProofStepSelector)

export default RProofStepSelector

