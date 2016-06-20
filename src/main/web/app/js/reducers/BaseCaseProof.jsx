import { RECEIVE_INDUCTION_SCHEMA, ADD_BASE_CASE_PROOF_NODE } from '../actions'

const BaseCaseProof = (state=[], action) => {

  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return [
        {
          id: 0,
          body: action.baseCase.toShow[0].split("=")[0],
          type: "INITIAL_TERM"
        }
      ]

    case ADD_BASE_CASE_PROOF_NODE:
      return [
        ...state,
        action.node
      ]

    default:
      return state
  }

}

export default BaseCaseProof

