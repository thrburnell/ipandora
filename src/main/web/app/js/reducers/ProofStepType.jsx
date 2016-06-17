import { SET_PROOF_STEP_TYPE, CLOSE_PROOF_STEP } from '../actions'

const ProofStepType = (state=null, action) => {
  
  switch (action.type) {
    case SET_PROOF_STEP_TYPE:
      return action.proofStepType

    case CLOSE_PROOF_STEP:
      return null

    default:
      return state
  }
}

export default ProofStepType

