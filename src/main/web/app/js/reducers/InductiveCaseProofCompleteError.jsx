import { SET_INDUCTIVE_CASE_PROOF_COMPLETE_ERROR, CLOSE_INDUCTIVE_CASE_PROOF_STEP } from '../actions'

const InductiveCaseProofCompleteError = (state=false, action) => {
  switch (action.type) {
    case SET_INDUCTIVE_CASE_PROOF_COMPLETE_ERROR:
      return true
    case CLOSE_INDUCTIVE_CASE_PROOF_STEP:
      return false
    default:
      return state
  }
}

export default InductiveCaseProofCompleteError

