import { SET_BASE_CASE_PROOF_COMPLETE_ERROR, CLOSE_BASE_CASE_PROOF_STEP } from '../actions'

const BaseCaseProofCompleteError = (state=false, action) => {
  switch (action.type) {
    case SET_BASE_CASE_PROOF_COMPLETE_ERROR:
      return true
    case CLOSE_BASE_CASE_PROOF_STEP:
      return false
    default:
      return state
  }
}

export default BaseCaseProofCompleteError

