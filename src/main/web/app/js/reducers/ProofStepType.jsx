import { SET_PROOF_STEP_TYPE } from '../actions'

const ProofStepType = (state=null, action) => {
  
  switch (action.type) {
    case SET_PROOF_STEP_TYPE:
      return action.proofStepType

    default:
      return state
  }
}

export default ProofStepType

