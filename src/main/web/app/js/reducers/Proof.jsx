import { ADD_PROOF_NODE } from '../actions'

const Proof = (state=[], action) => {

  switch (action.type) {
    case ADD_PROOF_NODE:
      return [...state, action.node]

    default:
      return state
  }
}

export default Proof

