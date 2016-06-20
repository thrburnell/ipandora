import { RECEIVE_INDUCTION_SCHEMA, ADD_INDUCTIVE_CASE_PROOF_NODE } from '../actions'

const BaseCaseProof = (state=[], action) => {

  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return [
        {
          id: 0,
          body: action.inductiveCase.toShow[0].split("=")[0],
          type: "INITIAL_TERM"
        }
      ]

    case ADD_INDUCTIVE_CASE_PROOF_NODE:
      return [
        ...state,
        action.node
      ]
  }

  return state
}

export default BaseCaseProof

