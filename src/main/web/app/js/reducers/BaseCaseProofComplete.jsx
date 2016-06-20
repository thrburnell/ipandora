import { SET_BASE_CASE_PROOF_COMPLETE } from '../actions'

const BaseCaseProofComplete = (state=false, action) => {

  switch (action.type) {
    case SET_BASE_CASE_PROOF_COMPLETE:
      return true

    default:
      return state
  }

}

export default BaseCaseProofComplete

