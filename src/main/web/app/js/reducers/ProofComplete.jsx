import { SET_PROOF_COMPLETE } from '../actions'

const ProofComplete = (state=false, action) => {
  
  switch (action.type) {
    case SET_PROOF_COMPLETE:
      return true

    default:
      return state
  }
}

export default ProofComplete

