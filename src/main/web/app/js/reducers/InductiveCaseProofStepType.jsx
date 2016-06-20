import { SET_INDUCTIVE_CASE_PROOF_STEP_TYPE, CLOSE_INDUCTIVE_CASE_PROOF_STEP } from '../actions'

const InductiveCaseProofStepType = (state=null, action) => {

  switch (action.type) {
    case SET_INDUCTIVE_CASE_PROOF_STEP_TYPE:
      return action.proofStepType

    case CLOSE_INDUCTIVE_CASE_PROOF_STEP:
      return null

    default:
      return state
  }
}

export default InductiveCaseProofStepType

