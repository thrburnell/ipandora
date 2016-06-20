import { SET_INDUCTIVE_CASE_PROOF_COMPLETE } from '../actions'

const InductiveCaseProofComplete = (state=false, action) => {

  switch (action.type) {
    case SET_INDUCTIVE_CASE_PROOF_COMPLETE:
      return true

    default:
      return false
  }

}

export default InductiveCaseProofComplete

