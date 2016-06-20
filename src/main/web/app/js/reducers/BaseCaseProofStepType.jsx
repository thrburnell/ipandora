import { SET_BASE_CASE_PROOF_STEP_TYPE, CLOSE_BASE_CASE_PROOF_STEP } from '../actions'

const BaseCaseProofStepType = (state=null, action) => {

  switch (action.type) {
    case SET_BASE_CASE_PROOF_STEP_TYPE:
      return action.proofStepType

    case CLOSE_BASE_CASE_PROOF_STEP:
      return null

    default:
      return state
  }
}

export default BaseCaseProofStepType

